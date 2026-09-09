(*
 * CFG Normalization Pass -- Correctness Proof
 *
 * STATUS: cfg_norm_fn_correct is FALSE as stated.
 *
 * The theorem lacks a block-label freshness condition.
 * split_block_name can collide with an existing block label,
 * causing the transformed function to jump to the wrong block.
 *
 * Counterexample: A function with 4 blocks including one already
 * labeled "A_split_B" (= split_block_name "A" "B"). After cfg_norm_fn,
 * the transformed function has two blocks with label "A_split_B".
 * lookup_block finds the old one (INVALID), not the new split block.
 * Original execution: A→B→STOP→Halt.
 * Transformed execution: A→"A_split_B"(old)→INVALID→Abort.
 *
 * Fix: Add precondition
 *   (!pred_lbl tgt_lbl.
 *      ~MEM (split_block_name pred_lbl tgt_lbl) (fn_labels func))
 *)

Theory cfgNormBase
Ancestors
  cfgNormDefs cfgNormSim cfgTransform cfgTransformProofs stateEquiv
  stateEquivProps venomExecSemantics execEquivProofs venomWf venomExecProps
  venomInstProps venomInst venomState venomExecProofs prevBbIndep
  finite_map

(* ================================================================
   Section 1: Counterexample -- block label collision
   ================================================================ *)

(* Counterexample function: 4 blocks, one pre-existing "A_split_B" *)
Definition cx_func_def:
  cx_func = mk_raw_function ""
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := JNZ;
            inst_operands := [Var "c"; Label "B"; Label "C"];
            inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 1; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>;
     <| bb_label := "C"; bb_instructions :=
        [<| inst_id := 2; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "A_split_B"; bb_instructions :=
        [<| inst_id := 4; inst_opcode := INVALID;
            inst_operands := []; inst_outputs := [] |>] |>]
End

(* The counterexample function is well-formed *)
Theorem cx_wf_function[local]:
  wf_function cx_func
Proof
  simp[wf_function_def, cx_func_def, mk_raw_function_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (
    rpt strip_tac >> gvs[] >>
    rw[bb_well_formed_def, is_terminator_def, listTheory.LAST_DEF] >>
    TRY (Cases_on `i` >> gvs[is_terminator_def] >>
         TRY (Cases_on `n` >> gvs[is_terminator_def]) >> NO_TAC) >>
    TRY (Cases_on `j` >> gvs[is_terminator_def] >>
         TRY (Cases_on `n` >> gvs[is_terminator_def]) >> NO_TAC)
  ) >>
  conj_tac >- (
    rw[fn_succs_closed_def, fn_labels_def, cx_func_def] >>
    gvs[bb_succs_def, get_successors_def, is_terminator_def,
        get_label_def, listTheory.nub_def, listTheory.REV_DEF,
        listTheory.NULL_DEF, listTheory.LAST_DEF, listTheory.MEM,
        listTheory.FILTER, listTheory.MAP,
        optionTheory.IS_SOME_DEF, optionTheory.THE_DEF] >> gvs[]
  ) >>
  EVAL_TAC
QED

(* The freshness condition is satisfied *)
Theorem cx_freshness[local]:
  !pred_lbl tgt_lbl var.
    MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
        (fn_all_vars cx_func) ==> F
Proof
  rw[Once (EVAL ``fn_all_vars cx_func``), listTheory.MEM, split_block_name_def] >>
  spose_not_then strip_assume_tac >>
  qpat_x_assum `_ = "c"` (mp_tac o AP_TERM ``STRLEN``) >>
  simp[stringTheory.STRLEN_CAT]
QED

(* cfg_norm_fn produces a function with duplicate "A_split_B" labels *)
Theorem cx_cfg_norm_fn[local]:
  cfg_norm_fn cx_func = mk_raw_function ""
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := JNZ;
            inst_operands := [Var "c"; Label "A_split_B"; Label "C"];
            inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 1; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>;
     <| bb_label := "C"; bb_instructions :=
        [<| inst_id := 2; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "A_split_B"; bb_instructions :=
        [<| inst_id := 4; inst_opcode := INVALID;
            inst_operands := []; inst_outputs := [] |>] |>;
     <| bb_label := "A_split_B"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>]
Proof
  EVAL_TAC
QED

(* In the transformed function, lookup_block "A_split_B" finds the OLD
   block (INVALID), not the new split block (JMP "B"). *)
Theorem cx_lookup_collision[local]:
  lookup_block "A_split_B" (cfg_norm_fn cx_func).fn_blocks =
  SOME <| bb_label := "A_split_B"; bb_instructions :=
          [<| inst_id := 4; inst_opcode := INVALID;
              inst_operands := []; inst_outputs := [] |>] |>
Proof
  EVAL_TAC
QED

(* Original execution: A's JNZ with condition 1w jumps to "B" *)
Theorem cx_orig_jnz[local]:
  !s. FLOOKUP s.vs_vars "c" = SOME 1w ==>
    step_inst_base
      <| inst_id := 0; inst_opcode := JNZ;
         inst_operands := [Var "c"; Label "B"; Label "C"];
         inst_outputs := [] |> s =
    OK (jump_to "B" s)
Proof
  rw[] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def, jump_to_def]
QED

(* Transformed execution: A's JNZ with condition 1w jumps to "A_split_B" *)
Theorem cx_trans_jnz[local]:
  !s. FLOOKUP s.vs_vars "c" = SOME 1w ==>
    step_inst_base
      <| inst_id := 0; inst_opcode := JNZ;
         inst_operands := [Var "c"; Label "A_split_B"; Label "C"];
         inst_outputs := [] |> s =
    OK (jump_to "A_split_B" s)
Proof
  rw[] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def, jump_to_def]
QED

(* Original: "B" block is STOP → Halt *)
Theorem cx_orig_stop[local]:
  !s. step_inst_base
      <| inst_id := 1; inst_opcode := STOP;
         inst_operands := []; inst_outputs := [] |> s =
    Halt (halt_state s)
Proof
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> rw[]
QED

(* Transformed: old "A_split_B" block is INVALID → Abort *)
Theorem cx_trans_invalid[local]:
  !s. step_inst_base
      <| inst_id := 4; inst_opcode := INVALID;
         inst_operands := []; inst_outputs := [] |> s =
    Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> rw[]
QED

(* Key divergence: original reaches Halt, transformed reaches Abort.
   result_equiv of any fresh set maps Halt to Abort = F. *)
Theorem cx_result_divergence[local]:
  !fresh s1 a s2.
    ~result_equiv fresh (Halt s1) (Abort a s2)
Proof
  rw[result_equiv_def]
QED

(* ================================================================
   Section 2: Counterexample -- PHI predecessor label mismatch
   
   cfg_norm_fn replaces PHI entries (Label pred, Var x) with
   (Label split, Var fwd_x). Starting from state s with
   vs_prev_bb = SOME pred and vs_current_bb = target, the original
   PHI resolves correctly but the transformed PHI fails (no matching
   predecessor label). Original → Halt, Transformed → Error.
   result_equiv fresh (Halt _) (Error _) = F for all fresh.
   ================================================================ *)

(* Function: P (JNZ→B,C), C (JMP→B), B (PHI [P→x, C→z]; STOP) *)
Definition cx2_func_def:
  cx2_func = mk_raw_function ""
    [<| bb_label := "P"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := JNZ;
            inst_operands := [Var "c"; Label "B"; Label "C"];
            inst_outputs := [] |>] |>;
     <| bb_label := "C"; bb_instructions :=
        [<| inst_id := 3; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 1; inst_opcode := PHI;
            inst_operands := [Label "P"; Var "x"; Label "C"; Var "z"];
            inst_outputs := ["y"] |>;
         <| inst_id := 2; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>]
End

Theorem cx2_wf[local]:
  wf_function cx2_func
Proof
  simp[wf_function_def, cx2_func_def, mk_raw_function_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (
    rpt strip_tac >> gvs[] >>
    rw[bb_well_formed_def, is_terminator_def, listTheory.LAST_DEF] >>
    TRY (Cases_on `i` >> gvs[is_terminator_def] >>
         TRY (Cases_on `n` >> gvs[is_terminator_def]) >> NO_TAC) >>
    TRY (Cases_on `j` >> gvs[is_terminator_def] >>
         TRY (Cases_on `n` >> gvs[is_terminator_def]) >> NO_TAC)
  ) >>
  conj_tac >- (
    rw[fn_succs_closed_def, fn_labels_def, cx2_func_def] >>
    gvs[bb_succs_def, get_successors_def, is_terminator_def,
        get_label_def, listTheory.nub_def, listTheory.REV_DEF,
        listTheory.NULL_DEF, listTheory.LAST_DEF, listTheory.MEM,
        listTheory.FILTER, listTheory.MAP,
        optionTheory.IS_SOME_DEF, optionTheory.THE_DEF] >> gvs[]
  ) >>
  EVAL_TAC
QED

Theorem cx2_freshness[local]:
  !pred_lbl tgt_lbl var.
    MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
        (fn_all_vars cx2_func) ==> F
Proof
  rw[Once (EVAL ``fn_all_vars cx2_func``), listTheory.MEM,
     split_block_name_def] >>
  spose_not_then strip_assume_tac >>
  qpat_x_assum `_ = _` (mp_tac o AP_TERM ``STRLEN``) >>
  simp[stringTheory.STRLEN_CAT]
QED

Theorem cx2_labels_fresh[local]:
  split_labels_fresh split_block_name cx2_func
Proof
  rw[split_labels_fresh_def, fn_labels_def, cx2_func_def,
     mk_raw_function_def, split_block_name_def, listTheory.MEM, listTheory.MAP] >>
  spose_not_then strip_assume_tac >>
  qpat_x_assum `_ = _` (mp_tac o AP_TERM ``STRLEN``) >>
  simp[stringTheory.STRLEN_CAT]
QED

(* cfg_norm_fn splits the P→B edge *)
Theorem cx2_cfg_norm[local]:
  cfg_norm_fn cx2_func = mk_raw_function ""
    [<| bb_label := "P"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := JNZ;
            inst_operands := [Var "c"; Label "P_split_B"; Label "C"];
            inst_outputs := [] |>] |>;
     <| bb_label := "C"; bb_instructions :=
        [<| inst_id := 3; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 1; inst_opcode := PHI;
            inst_operands := [Label "P_split_B"; Var "P_split_B_fwd_x";
                              Label "C"; Var "z"];
            inst_outputs := ["y"] |>;
         <| inst_id := 2; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>;
     <| bb_label := "P_split_B"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := ASSIGN;
            inst_operands := [Var "x"];
            inst_outputs := ["P_split_B_fwd_x"] |>;
         <| inst_id := 1; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>]
Proof
  EVAL_TAC
QED

(* Original: start at B with prev_bb=P, has x=42w -> PHI resolves -> STOP -> Halt *)
Theorem cx2_orig_halt[local]:
  !s ctx. s.vs_current_bb = "B" /\ s.vs_prev_bb = SOME "P" /\
          s.vs_inst_idx = 0 /\ FLOOKUP s.vs_vars "x" = SOME 42w ==>
    run_blocks (SUC 0) ctx cx2_func s =
    Halt (halt_state (update_var "y" 42w (s with vs_inst_idx := 1)))
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_blocks_def] >>
  gvs[cx2_func_def, mk_raw_function_def, lookup_block_def, listTheory.FIND_thm] >>
  simp[eval_phis_def, eval_one_phi_def, resolve_phi_def, eval_operand_def,
       lookup_var_def, update_var_def, phi_prefix_length_def] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  rw[get_instruction_def, listTheory.oEL_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_def] >> rw[is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> rw[]
QED

(* Transformed: start at B with prev_bb=P → PHI fails (no "P" entry) *)
Theorem cx2_trans_error[local]:
  !s ctx fuel. s.vs_current_bb = "B" /\ s.vs_prev_bb = SOME "P" /\
               s.vs_inst_idx = 0 /\ fuel > 0 ==>
    run_blocks fuel ctx (cfg_norm_fn cx2_func) s =
    Error "phi evaluation failed"
Proof
  rpt strip_tac >> Cases_on `fuel` >> gvs[] >>
  ONCE_REWRITE_TAC[run_blocks_def] >>
  gvs[cx2_cfg_norm, mk_raw_function_def, cfg_norm_fn_def, insert_split_def,
      lookup_block_def, listTheory.FIND_thm] >>
  simp[eval_phis_def, eval_one_phi_def, resolve_phi_def]
QED

(* ================================================================
   Section 3: Helpers for correctness proof
   ================================================================ *)

(* wf_function without fn_inst_ids_distinct -- this is the variant that is
   preserved through cfg_norm iteration. fn_inst_ids_distinct (cross-block
   uniqueness of inst_ids) is NOT preserved by insert_split because the pass
   starts with id_base=0 which collides with existing ids. Only per-block
   inst_id distinctness is needed for correctness. *)
Definition wf_function_no_ids_def:
  wf_function_no_ids fn <=>
    ALL_DISTINCT (fn_labels fn) /\
    fn_has_entry fn /\
    (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\
    fn_succs_closed fn
End

Theorem wf_function_imp_no_ids:
  !fn. wf_function fn ==> wf_function_no_ids fn
Proof
  rw[wf_function_def, wf_function_no_ids_def]
QED

(* Per-block inst_id distinctness from wf_function *)
Theorem wf_function_block_inst_ids_distinct:
  !func bb. wf_function func /\ MEM bb func.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rw[wf_function_def, fn_inst_ids_distinct_def] >>
  qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
  qpat_x_assum `MEM bb _` mp_tac >>
  qspec_tac (`func.fn_blocks`, `bbs`) >>
  Induct >> simp[] >> rpt strip_tac >>
  fs[listTheory.ALL_DISTINCT_APPEND]
QED

(* Entry label is preserved by insert_split *)
Theorem insert_split_entry[local]:
  !func pred_bb target_bb id_base.
    func.fn_blocks <> [] ==>
    fn_entry_label (insert_split func pred_bb target_bb id_base) =
    fn_entry_label func
Proof
  rw[insert_split_def, fn_entry_label_def, entry_block_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `func.fn_blocks` >>
  gvs[listTheory.NULL_DEF, replace_block_def,
      subst_label_terminator_bb_label, update_phis_for_split_bb_label] >>
  rw[] >> gvs[subst_label_terminator_bb_label, update_phis_for_split_bb_label] >>
  Cases_on `h.bb_label = pred_bb.bb_label` >>
  gvs[subst_label_terminator_bb_label]
QED

(* PHI predecessor labels are all from fn_labels.
   Trivially satisfied by any compiler-generated function:
   PHI entries reference actual predecessors. *)
Definition fn_phi_preds_closed_def:
  fn_phi_preds_closed func <=>
    !bb inst l.
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI /\
      resolve_phi l inst.inst_operands <> NONE ==>
      MEM l (fn_labels func)
End

(* PHI non-interference: no PHI output variable is read by a different PHI
   from the same predecessor. Ensures sequential PHI execution agrees with
   parallel semantics for that predecessor.
   Trivially satisfied when PHI output names are disjoint from PHI value
   variable names (standard in compiler-generated SSA). *)
Definition fn_phis_non_interfering_def:
  fn_phis_non_interfering func <=>
    !bb inst1 inst2 out pred_lbl v.
      MEM bb func.fn_blocks /\
      MEM inst1 bb.bb_instructions /\ inst1.inst_opcode = PHI /\
      MEM inst2 bb.bb_instructions /\ inst2.inst_opcode = PHI /\
      inst1 <> inst2 /\
      MEM out inst1.inst_outputs /\
      resolve_phi pred_lbl inst2.inst_operands = SOME (Var v) ==>
      out <> v
End

(* PHI label distinctness: each predecessor label appears at most once in each
   PHI instruction's operands. Equivalent to ALL_DISTINCT (MAP FST (phi_pairs ops)).
   Trivially satisfied in compiler-generated Venom IR -- each CFG predecessor
   contributes exactly one entry. Without this, phi_pairs can return multiple
   values for the same label, but resolve_phi only returns the first. *)
Definition fn_phi_labels_distinct_def:
  fn_phi_labels_distinct func <=>
    !bb inst.
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI ==>
      ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))
End

(* If a label does not appear in PHI operands, resolve_phi returns NONE *)
Theorem resolve_phi_NONE_fresh[local]:
  !prev_bb ops.
    EVERY (\op. !l. op = Label l ==> l <> prev_bb) ops ==>
    resolve_phi prev_bb ops = NONE
Proof
  recInduct resolve_phi_ind >> rw[resolve_phi_def]
QED

(* Useful corollary: fresh label + phi_preds_closed => resolve_phi NONE *)
Theorem resolve_phi_fresh_label:
  !func bb inst split_lbl.
    fn_phi_preds_closed func /\
    ~MEM split_lbl (fn_labels func) /\
    MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI ==>
    resolve_phi split_lbl inst.inst_operands = NONE
Proof
  rw[fn_phi_preds_closed_def] >>
  Cases_on `resolve_phi split_lbl inst.inst_operands` >> simp[] >>
  first_x_assum (qspecl_then [`bb`, `inst`, `split_lbl`] mp_tac) >>
  simp[]
QED

(* ================================================================
   Section 3b: Frame lemma -- unused variables don't affect execution

   run_function_frame: If two states agree on all variables used by
   a function (fn_all_vars) and on all environment fields, running the
   function produces result_equiv UNIV results. This handles INVOKE
   correctly: callee starts from FEMPTY vars, so caller var differences
   are irrelevant.
   ================================================================ *)

(* Condition: all var operands and outputs of bb are in V *)
Definition block_vars_in_def:
  block_vars_in V bb <=>
    (!inst. MEM inst bb.bb_instructions ==>
      (!x. MEM (Var x) inst.inst_operands ==> x IN V) /\
      (!x. MEM x inst.inst_outputs ==> x IN V))
End

(* Condition: all blocks of func have vars in V *)
Definition fn_vars_in_def:
  fn_vars_in V func <=>
    (!bb. MEM bb func.fn_blocks ==> block_vars_in V bb)
End

(* fn_all_vars collects exactly these vars *)
Theorem fn_vars_in_fn_all_vars[local]:
  !func. fn_vars_in (set (fn_all_vars func)) func
Proof
  rw[fn_vars_in_def, block_vars_in_def, fn_all_vars_def] >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rpt strip_tac >| [
    qexists_tac `FLAT (MAP
      (\inst'. inst'.inst_outputs ++
        FLAT (MAP (\op. case op of Var v => [v] | _ => [])
              inst'.inst_operands)) bb.bb_instructions)` >>
    conj_tac >- (qexists_tac `bb` >> simp[]) >>
    simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
    qexists_tac `inst.inst_outputs ++
      FLAT (MAP (\op. case op of Var v => [v] | _ => [])
            inst.inst_operands)` >>
    conj_tac >- (qexists_tac `inst` >> simp[]) >>
    simp[listTheory.MEM_APPEND, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
    DISJ2_TAC >> qexists_tac `[x]` >>
    simp[] >> qexists_tac `Var x` >> simp[],
    (* outputs case *)
    qexists_tac `FLAT (MAP
      (\inst'. inst'.inst_outputs ++
        FLAT (MAP (\op. case op of Var v => [v] | _ => [])
              inst'.inst_operands)) bb.bb_instructions)` >>
    conj_tac >- (qexists_tac `bb` >> simp[]) >>
    simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
    qexists_tac `inst.inst_outputs ++
      FLAT (MAP (\op. case op of Var v => [v] | _ => [])
            inst.inst_operands)` >>
    conj_tac >- (qexists_tac `inst` >> simp[]) >>
    simp[listTheory.MEM_APPEND]
  ]
QED

(* setup_callee produces equal states from execution_equiv states *)
Theorem setup_callee_equiv[local]:
  !fn args s1 s2.
    execution_equiv UNIV s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[setup_callee_def, execution_equiv_def,
     venom_state_component_equality]
QED

(* merge_callee_state preserves state_equiv on caller vars *)
Theorem merge_callee_equiv[local]:
  !vars s1 s2 cs.
    state_equiv vars s1 s2 ==>
    state_equiv vars (merge_callee_state s1 cs) (merge_callee_state s2 cs)
Proof
  rw[merge_callee_state_def, state_equiv_def, execution_equiv_def,
     lookup_var_def]
QED

(* Updating the returned FMP in the same way preserves state equivalence. *)
Theorem adopt_return_fmp_equiv[local]:
  !vars ir s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (adopt_return_fmp ir s1) (adopt_return_fmp ir s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, state_equiv_def, execution_equiv_def,
      lookup_var_def]
QED

(* eval_operands gives same results under state_equiv *)
Theorem eval_operands_equiv[local]:
  !vars ops s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct_on `ops` >> simp[eval_operands_def] >>
  rpt strip_tac >>
  `eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_equiv >> simp[] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[]
QED

(* FOLDL of update_var preserves state_equiv *)
Theorem foldl_update_var_equiv[local]:
  !pairs vars s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct >> simp[] >> Cases >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  irule update_var_preserves >> simp[]
QED

(* bind_outputs preserves state_equiv when writing same vals *)
Theorem bind_outputs_equiv[local]:
  !outs vals vars s1 s2.
    state_equiv vars s1 s2 ==>
    case (bind_outputs outs vals s1, bind_outputs outs vals s2) of
      (SOME s1', SOME s2') => state_equiv vars s1' s2'
    | (NONE, NONE) => T
    | _ => F
Proof
  simp[bind_outputs_def] >> rpt strip_tac >>
  Cases_on `LENGTH outs = LENGTH vals` >> simp[] >>
  irule foldl_update_var_equiv >> simp[]
QED

(* INVOKE case of frame lemma, standalone. Since setup_callee creates
   identical callee states, run_blocks gets identical inputs and
   produces identical results. Only merge+bind_outputs needs state_equiv. *)
Theorem step_inst_invoke_frame[local]:
  !fuel ctx inst s1 s2 vars.
    inst.inst_opcode = INVOKE /\
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    (!x. MEM x inst.inst_outputs ==> x NOTIN vars) ==>
    result_equiv vars (step_inst fuel ctx inst s1)
                      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  (* Establish intermediate equalities *)
  `!ops. (!v. MEM (Var v) ops ==> MEM (Var v) inst.inst_operands) ==>
         eval_operands ops s1 = eval_operands ops s2` by
    (rpt strip_tac >> irule eval_operands_equiv >>
     simp[] >> metis_tac[]) >>
  `!fn args. setup_callee fn args s1 = setup_callee fn args s2` by
    (rpt gen_tac >> irule setup_callee_equiv >>
     gvs[state_equiv_def, execution_equiv_def] >>
     simp[pred_setTheory.IN_UNIV]) >>
  (* Unfold step_inst, reduce if-then-else and pair case *)
  simp[Once step_inst_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
  simp[] >>
  (* arg_ops operands are in inst.inst_operands *)
  Cases_on `decode_invoke inst` >> simp[result_equiv_def] >>
  PairCases_on `x` >> simp[] >>
  rename1 `decode_invoke inst = SOME (callee_name, arg_ops)` >>
  `eval_operands arg_ops s1 = eval_operands arg_ops s2` by
    (first_x_assum irule >> rpt strip_tac >>
     gvs[decode_invoke_def] >>
     BasicProvers.every_case_tac >> gvs[listTheory.MEM]) >>
  Cases_on `lookup_function callee_name ctx.ctx_functions` >>
  simp[result_equiv_def] >>
  Cases_on `eval_operands arg_ops s2` >> simp[result_equiv_def] >>
  gvs[] >>
  Cases_on `setup_callee x x' s2` >> simp[result_equiv_def] >>
  (* Both sides call run_blocks on identical arguments *)
  Cases_on `run_blocks fuel ctx x x''` >>
  simp[result_equiv_def] >>
  TRY (simp[execution_equiv_refl] >> NO_TAC) >>
  (* IntRet case: merge the callee, adopt the same returned FMP, then bind. *)
  `state_equiv vars (merge_callee_state s1 v)
                    (merge_callee_state s2 v)` by
    (irule merge_callee_equiv >> simp[]) >>
  simp[bind_outputs_def] >>
  IF_CASES_TAC >> gvs[result_equiv_def]
  >- (`state_equiv vars
        (adopt_return_fmp i (merge_callee_state s1 v))
        (adopt_return_fmp i (merge_callee_state s2 v))` by
        (irule adopt_return_fmp_equiv >> gvs[]) >>
      irule foldl_update_var_equiv >> gvs[])
  >> irule adopt_return_fmp_equiv >> gvs[]
QED

(* Frame lemma Step 1: step_inst (combines INVOKE + non-INVOKE) *)
Theorem step_inst_frame[local]:
  !fuel ctx inst s1 s2 vars.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    (!x. MEM x inst.inst_outputs ==> x NOTIN vars) ==>
    result_equiv vars (step_inst fuel ctx inst s1)
                      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (irule step_inst_invoke_frame >> simp[])
  >- (simp[step_inst_non_invoke] >>
      irule step_inst_result_equiv >> simp[])
QED

(* Frame lemma Step 2: exec_block (standalone induction) *)
Theorem run_block_frame[local]:
  !fuel ctx bb s1 s2 vars.
    state_equiv vars s1 s2 /\ block_vars_in (COMPL vars) bb ==>
    result_equiv vars (exec_block fuel ctx bb s1)
                      (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by fs[state_equiv_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >>
  gvs[result_equiv_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def] >>
     irule listTheory.EL_MEM >> simp[]) >>
  `(!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
   (!x. MEM x inst.inst_outputs ==> x NOTIN vars)` by
    (fs[block_vars_in_def, pred_setTheory.IN_COMPL] >>
     metis_tac[]) >>
  `result_equiv vars (step_inst fuel ctx inst s1)
                     (step_inst fuel ctx inst s2)` by
    (irule step_inst_frame >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[result_equiv_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[]
  >- ((* Terminator + OK: check halted *)
      `v.vs_halted <=> v'.vs_halted` by
        fs[state_equiv_def, execution_equiv_def] >>
      Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
      fs[state_equiv_def]) >>
  (* Non-terminator: use exec_block IH *)
  `step_inst fuel ctx inst s1 = OK v` by
    ASM_REWRITE_TAC[] >>
  first_x_assum irule >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* PHI operands outside vars when block vars are in COMPL vars *)
Theorem block_vars_phi_ops_outside[local]:
  !vars bb. block_vars_in (COMPL vars) bb ==>
    EVERY (\inst. inst.inst_opcode = PHI ==>
              !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)
         bb.bb_instructions
Proof
  rw[block_vars_in_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

(* Frame lemma Step 2b: run_block (eval_phis + exec_block) *)
Theorem run_block_entry_frame[local]:
  !fuel ctx bb s1 s2 vars.
    state_equiv vars s1 s2 /\ block_vars_in (COMPL vars) bb ==>
    result_equiv vars (run_block fuel ctx bb s1)
                      (run_block fuel ctx bb s2)
Proof
  ONCE_REWRITE_TAC[run_block_def] >> rpt strip_tac >>
  imp_res_tac block_vars_phi_ops_outside >>
  mp_tac (Q.SPECL [`s1`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s1 bb.bb_instructions` >> gvs[exec_result_distinct] >>
  mp_tac (Q.SPECL [`s2`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s2 bb.bb_instructions` >> gvs[exec_result_distinct]
  >- (
    irule run_block_frame >> simp[] >>
    irule state_equiv_inst_idx >>
    qspecl_then [`s1`,`s2`,`vars`,`bb.bb_instructions`,`v`] mp_tac
      eval_phis_state_equiv >> simp[] >> strip_tac >>
    fs[] >> metis_tac[state_equiv_sym]
  )
  >- (
    qspecl_then [`s1`,`s2`,`vars`,`bb.bb_instructions`,`v`] mp_tac
      eval_phis_state_equiv >> simp[] >> strip_tac >> gvs[]
  )
  >- (
    qspecl_then [`s2`,`s1`,`vars`,`bb.bb_instructions`,`v`] mp_tac
      eval_phis_state_equiv >> simp[state_equiv_sym] >> strip_tac >> gvs[]
  )
  >- simp[result_equiv_def]
QED
(* Frame lemma Step 3: run_blocks (standalone induction) *)
Theorem run_function_frame[local]:
  !fuel ctx func s1 s2 vars.
    state_equiv vars s1 s2 /\ fn_vars_in (COMPL vars) func ==>
    result_equiv vars (run_blocks fuel ctx func s1)
                      (run_blocks fuel ctx func s2)
Proof
  Induct_on `fuel`
  >- simp[venomExecSemanticsTheory.run_blocks_def, result_equiv_def] >>
  rpt strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  Cases_on `lookup_block s2.vs_current_bb func.fn_blocks`
  >- simp[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `block_vars_in (COMPL vars) bb` by (
    fs[fn_vars_in_def] >> first_assum irule >> metis_tac[lookup_block_MEM]) >>
  `result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)` by
    metis_tac[run_block_entry_frame] >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx bb s2` >>
  gvs[result_equiv_def] >>
  `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[result_equiv_def]
  >- fs[state_equiv_def, execution_equiv_def] >>
  first_x_assum irule >> simp[] >>
  fs[fn_vars_in_def] >> metis_tac[lookup_block_MEM]
QED

(* Specialized: run_blocks on same func with split_rel states *)
Theorem run_function_split_rel[local]:
  !fuel ctx func s1 s2.
    state_equiv (COMPL (set (fn_all_vars func))) s1 s2 ==>
    result_equiv UNIV
      (run_blocks fuel ctx func s1)
      (run_blocks fuel ctx func s2)
Proof
  rpt strip_tac >>
  irule result_equiv_subset >>
  qexists_tac `COMPL (set (fn_all_vars func))` >>
  conj_tac >- simp[pred_setTheory.SUBSET_UNIV] >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `func`, `s1`, `s2`,
    `COMPL (set (fn_all_vars func))`] run_function_frame) >>
  simp[pred_setTheory.COMPL_COMPL, fn_vars_in_fn_all_vars]
QED

(* ================================================================
   Section 4: insert_split correctness -- one split preserves semantics

   Key idea: fuel induction. For the pred_bb case, states diverge
   after the split block. run_function_split_rel bridges the gap:
   it shows the ORIGINAL function gives UNIV-equivalent results from
   states that differ only in unused vars.
   ================================================================ *)

(* Helper: lookup_block_insert_split_other without LET *)
Theorem lookup_insert_split_other[local]:
  !func pred_bb target_bb id_base lbl.
    lbl <> pred_bb.bb_label /\
    lbl <> target_bb.bb_label /\
    lbl <> split_block_name pred_bb.bb_label target_bb.bb_label ==>
    lookup_block lbl
      (insert_split func pred_bb target_bb id_base).fn_blocks =
    lookup_block lbl func.fn_blocks
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `lbl`]
            lookup_block_insert_split_other) >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  drule build_split_block_label >> strip_tac >> gvs[]
QED

(* Helper: lookup_block_insert_split_pred without LET *)
Theorem lookup_insert_split_pred[local]:
  !func pred_bb target_bb id_base.
    pred_bb.bb_label <> target_bb.bb_label /\
    (?bb. lookup_block pred_bb.bb_label func.fn_blocks = SOME bb) ==>
    ?split_bb.
    lookup_block pred_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
    SOME (subst_label_terminator target_bb.bb_label
            split_bb.bb_label pred_bb) /\
    split_bb.bb_label = split_block_name pred_bb.bb_label target_bb.bb_label
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
            lookup_block_insert_split_pred) >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  drule build_split_block_label >> strip_tac >>
  strip_tac >> qexists_tac `split_bb` >> gvs[]
QED

(* Helper: lookup_block_insert_split_target without LET *)
Theorem lookup_insert_split_target[local]:
  !func pred_bb target_bb id_base.
    pred_bb.bb_label <> target_bb.bb_label /\
    (?bb. lookup_block target_bb.bb_label func.fn_blocks = SOME bb) ==>
    ?split_bb var_repls.
    lookup_block target_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
    SOME (update_phis_for_split pred_bb.bb_label split_bb.bb_label
            var_repls target_bb) /\
    split_bb.bb_label = split_block_name pred_bb.bb_label target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
            lookup_block_insert_split_target) >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  drule build_split_block_label >> strip_tac >> gvs[]
QED

(* After exec_block OK (not halted), vs_prev_bb = SOME s.vs_current_bb.
   Uses same completeInduct_on measure pattern as run_block_current_bb_in_succs. *)
(* Promoted to venomExecPropsTheory *)
val run_block_ok_prev_bb = venomExecPropsTheory.exec_block_ok_prev_bb;

Theorem bb_well_formed_no_early_terminator[local]:
  !bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions - 1 ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  fs[bb_well_formed_def] >> res_tac >> fs[]
QED

Theorem wf_function_no_ids_imp_inst_wf[local]:
  !func bb. wf_function_no_ids func /\ fn_inst_wf func /\
            MEM bb func.fn_blocks ==>
            EVERY inst_wf bb.bb_instructions
Proof
  rpt strip_tac >> gvs[fn_inst_wf_def] >> res_tac >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem wf_function_no_ids_imp_bb_wf[local]:
  !func bb. wf_function_no_ids func /\ MEM bb func.fn_blocks ==>
            bb_well_formed bb
Proof
  rpt strip_tac >> gvs[wf_function_no_ids_def] >> metis_tac[]
QED

Theorem run_block_ok_succ_in_labels:
  !fuel ctx bb s s' func.
    wf_function_no_ids func /\ fn_inst_wf func /\
    MEM bb func.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block_entry fuel ctx bb s = OK s' /\ ~s'.vs_halted ==>
    MEM s'.vs_current_bb (fn_labels func)
Proof
  rpt strip_tac >>
  imp_res_tac wf_function_no_ids_imp_inst_wf >>
  imp_res_tac wf_function_no_ids_imp_bb_wf >>
  imp_res_tac bb_well_formed_no_early_terminator >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  qpat_x_assum `run_block_entry _ _ _ _ = OK _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_distinct] >>
  strip_tac >>
  imp_res_tac eval_phis_preserves_current_bb >>
  qspecl_then [`fuel`,`ctx`,`bb`,
    `v with vs_inst_idx := phi_prefix_length bb.bb_instructions`,`s'`]
    mp_tac exec_block_current_bb_in_succs >>
  impl_keep_tac >- (
    rpt conj_tac >> simp[phi_prefix_length_le]) >>
  strip_tac >>
  fs[wf_function_no_ids_def, fn_succs_closed_def] >> metis_tac[]
QED

(* After exec_block OK non-halted, vs_prev_bb = SOME (initial vs_current_bb). *)
Theorem run_block_ok_prev_bb_fn[local]:
  !fuel ctx bb s s' func.
    wf_function_no_ids func /\ fn_inst_wf func /\
    MEM bb func.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block_entry fuel ctx bb s = OK s' /\ ~s'.vs_halted ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  imp_res_tac wf_function_no_ids_imp_inst_wf >>
  imp_res_tac wf_function_no_ids_imp_bb_wf >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  imp_res_tac bb_well_formed_no_early_terminator >>
  imp_res_tac run_block_ok_prev_bb_exact >> fs[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]
QED

Theorem lookup_block_label[local]:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >>
  rw[lookup_block_def, listTheory.FIND_thm]
QED

(* step_inst_base preserves vs_labels when result is OK.
   Terminators returning OK (JMP/JNZ/DJMP) all use jump_to which
   only updates prev_bb/current_bb/inst_idx. Non-terminators: by
   step_preserves_labels (lift through step_inst_non_invoke). *)
Theorem step_inst_base_preserves_vs_labels[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==> s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (imp_res_tac step_inst_base_OK_not_INVOKE >> fs[]) >>
  `step_inst 0 ARB inst s = OK s'` by
    simp[step_inst_non_invoke] >>
  metis_tac[step_inst_preserves_labels_always]
QED

(* exec_block preserves vs_labels on OK result. *)
(* step_inst preserves vs_labels for any opcode (terminators go through
   step_inst_base which preserves it; non-terminators use step_preserves_labels). *)
Theorem foldl_update_var_preserves_vs_labels[local]:
  !pairs s. (FOLDL (\s' (out,val). update_var out val s') s pairs).vs_labels
             = s.vs_labels
Proof
  Induct >> simp[] >>
  Cases >> simp[update_var_def]
QED

Theorem step_inst_preserves_vs_labels[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    fs[step_inst_def, AllCaseEqs()] >>
    fs[bind_outputs_def, AllCaseEqs()] >> rw[] >>
    Cases_on `ret.iret_adopt_fmp` >>
    simp[foldl_update_var_preserves_vs_labels, merge_callee_state_def,
         adopt_return_fmp_def]
  )
  >> (
    `step_inst_base inst s = OK s'` by fs[step_inst_non_invoke] >>
    imp_res_tac step_inst_base_preserves_vs_labels
  )
QED

Theorem run_block_preserves_vs_labels[local]:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==>
    s'.vs_labels = s.vs_labels
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> fs[]
  >- imp_res_tac step_inst_preserves_vs_labels
  >> (`s''.vs_labels = s.vs_labels` by
        imp_res_tac step_inst_preserves_vs_labels >>
      `s.vs_inst_idx < LENGTH bb.bb_instructions` by
        fs[get_instruction_def, AllCaseEqs()] >>
      qpat_x_assum `!m. m < _ ==> _` (qspec_then
        `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`bb`,
        `s'' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s'`] mp_tac) >>
      simp[])
QED

(* After exec_block OK non-halted on any block in func, the IH conditions
   for insert_split_correct are maintained: current_bb <> split_lbl, and
   if at target_bb then prev_bb <> pred_bb and prev_bb <> split_lbl.
   Extracted to avoid 3x duplication in other/target/pred step helpers. *)
Theorem insert_split_ih_maintained[local]:
  !func pred_bb target_bb split_lbl fuel ctx cur_bb s v.
    wf_function_no_ids func /\ fn_inst_wf func /\
    ALL_DISTINCT (fn_labels func) /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME cur_bb /\
    s.vs_current_bb <> pred_bb.bb_label /\
    s.vs_inst_idx = 0 /\
    run_block_entry fuel ctx cur_bb s = OK v /\ ~v.vs_halted ==>
    MEM v.vs_current_bb (fn_labels func) /\
    v.vs_current_bb <> split_lbl /\
    (v.vs_current_bb = target_bb.bb_label ==>
      v.vs_prev_bb <> SOME pred_bb.bb_label /\
      v.vs_prev_bb <> SOME split_lbl)
Proof
  rpt strip_tac >>
  `MEM cur_bb func.fn_blocks` by metis_tac[lookup_block_MEM] >>
  imp_res_tac wf_function_no_ids_imp_inst_wf >>
  imp_res_tac wf_function_no_ids_imp_bb_wf >>
  `cur_bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  imp_res_tac bb_well_formed_no_early_terminator >>
  imp_res_tac run_block_ok_succ_in_labels >>
  imp_res_tac run_block_ok_prev_bb_exact >>
  gvs[] >>
  `cur_bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  fs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]
QED

(* Helper: one step of insert_split simulation for "other" blocks *)
Theorem insert_split_other_step[local]:
  !func pred_bb target_bb id_base func' split_lbl n ctx s cur_bb.
    wf_function_no_ids func /\
    fn_inst_wf func /\
    ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    s.vs_current_bb <> split_lbl /\
    s.vs_current_bb <> pred_bb.bb_label /\
    s.vs_current_bb <> target_bb.bb_label /\
    s.vs_inst_idx = 0 /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME cur_bb /\
    s.vs_labels = FEMPTY /\
    (!ctx' s'.
       ~s'.vs_halted /\
       s'.vs_current_bb <> split_lbl /\
       s'.vs_inst_idx = 0 /\
       s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <> SOME split_lbl) ==>
      ?fuel'. fuel' >= n /\
        result_equiv UNIV (run_blocks n ctx' func s')
                          (run_blocks fuel' ctx' func' s')) ==>
    ?fuel'. fuel' >= SUC n /\
      result_equiv UNIV (run_blocks (SUC n) ctx func s)
                        (run_blocks fuel' ctx func' s)
Proof
  rpt strip_tac >>
  qpat_x_assum `func' = _` SUBST_ALL_TAC >>
  qpat_x_assum `split_lbl = _` SUBST_ALL_TAC >>
  `lookup_block s.vs_current_bb
     (insert_split func pred_bb target_bb id_base).fn_blocks = SOME cur_bb` by
    simp[lookup_insert_split_other] >>
  `MEM cur_bb func.fn_blocks` by (irule lookup_block_MEM >> metis_tac[]) >>
  (* Unfold LHS run_blocks (SUC n) *)
  ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[Excl "run_block_def"] >>
  Cases_on `run_block_entry n ctx cur_bb s` >> fs[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >>
  TRY (qexists_tac `SUC n` >> ONCE_REWRITE_TAC[run_blocks_unfold] >>
       simp[result_equiv_UNIV_refl] >> NO_TAC) >>
  (* Only OK case remains *)
  rename1 `OK v` >>
  Cases_on `v.vs_halted` >> fs[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >>
  TRY (qexists_tac `SUC n` >> ONCE_REWRITE_TAC[run_blocks_unfold] >>
       simp[result_equiv_UNIV_refl] >> NO_TAC) >>
  (* Only non-halted OK case remains *)
  `~v.vs_halted` by fs[] >>
  `v.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
  `v.vs_current_bb <> split_block_name pred_bb.bb_label target_bb.bb_label /\
   (v.vs_current_bb = target_bb.bb_label ==>
    v.vs_prev_bb <> SOME pred_bb.bb_label /\
    v.vs_prev_bb <> SOME (split_block_name pred_bb.bb_label target_bb.bb_label))` by
    (mp_tac insert_split_ih_maintained >>
     disch_then (qspecl_then [`func`, `pred_bb`, `target_bb`,
       `split_block_name pred_bb.bb_label target_bb.bb_label`,
       `n`, `ctx`, `cur_bb`, `s`, `v`] mp_tac) >> simp[Excl "run_block_def"]) >>
  `v.vs_labels = FEMPTY` by (
    imp_res_tac venomExecPropsTheory.run_block_preserves_labels >> fs[Excl "run_block_def"]) >>
  first_x_assum (qspecl_then [`ctx`, `v`] mp_tac) >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >>
  strip_tac >>
  rename [`result_equiv _ _ (run_blocks fuel2 _ _ _)`] >>
  `run_block_entry fuel2 ctx cur_bb s = OK v` by (
    drule venomExecPropsTheory.run_block_fuel_mono_OK >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >>
  qexists_tac `SUC fuel2` >> conj_tac >- simp[] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[Excl "run_block_def"]
QED

(* step_inst on a PHI instruction with updated operands gives the same
   result when prev_bb doesn't match old or new label *)
Theorem step_inst_update_phi_other[local]:
  !fuel ctx inst s old_lbl new_lbl var_repls.
    inst.inst_opcode = PHI /\
    (s.vs_prev_bb = NONE \/
     ?prev. s.vs_prev_bb = SOME prev /\
            prev <> old_lbl /\ prev <> new_lbl) ==>
    step_inst fuel ctx
      (inst with inst_operands :=
        update_phi_ops old_lbl new_lbl var_repls inst.inst_operands) s =
    step_inst fuel ctx inst s
Proof
  rw[step_inst_def, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >>
  simp[resolve_phi_update_phi_ops_other]
QED

(* exec_block on update_phis_for_split gives same result when prev doesn't
   match old or new label. Covers NONE (entry) and SOME prev cases. *)
Theorem run_block_update_phis_other[local]:
  !fuel ctx bb s old_lbl new_lbl var_repls.
    (s.vs_prev_bb = NONE \/
     ?prev. s.vs_prev_bb = SOME prev /\
            prev <> old_lbl /\ prev <> new_lbl) ==>
    exec_block fuel ctx
      (update_phis_for_split old_lbl new_lbl var_repls bb) s =
    exec_block fuel ctx bb s
Proof
  ntac 4 gen_tac >>
  MAP_EVERY qid_spec_tac [`s`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt strip_tac >>
  `LENGTH (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions
   = LENGTH bb.bb_instructions` by
    simp[update_phis_for_split_length] >>
  simp[Once exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >>
  gvs[listTheory.oEL_def] >>
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = PHI` >> (
    (* Both cases: establish instruction equality *)
    TRY (`(update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions❲s.vs_inst_idx❳ =
       bb.bb_instructions❲s.vs_inst_idx❳ with inst_operands :=
         update_phi_ops old_lbl new_lbl var_repls
           bb.bb_instructions❲s.vs_inst_idx❳.inst_operands` by
        simp[update_phis_for_split_phi]) >>
    TRY (`(update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions❲s.vs_inst_idx❳ =
       bb.bb_instructions❲s.vs_inst_idx❳` by
        simp[update_phis_for_split_non_phi]) >>
    simp[] >>
    (* For PHI case, show step_inst is the same *)
    TRY (`step_inst fuel ctx
         (bb.bb_instructions❲s.vs_inst_idx❳ with inst_operands :=
           update_phi_ops old_lbl new_lbl var_repls
             bb.bb_instructions❲s.vs_inst_idx❳.inst_operands) s =
       step_inst fuel ctx bb.bb_instructions❲s.vs_inst_idx❳ s` by
        (irule step_inst_update_phi_other >> fs[] >> metis_tac[]) >>
      simp[]) >>
    Cases_on `step_inst fuel ctx bb.bb_instructions❲s.vs_inst_idx❳ s` >>
    simp[] >>
    Cases_on `is_terminator bb.bb_instructions❲s.vs_inst_idx❳.inst_opcode` >>
    gvs[is_terminator_def] >>
    first_x_assum irule >>
    simp[get_instruction_def, listTheory.oEL_def] >>
    TRY (conj_tac >- simp[is_terminator_def]) >>
    metis_tac[step_inst_preserves_prev_bb, is_terminator_def])
QED
(* When prev_bb doesn't match old/new label, eval_phis on update_phis_for_split
   instructions gives same result as eval_phis on original instructions.
   This is because update_phi_ops only changes entries matching old_label,
   so resolve_phi prev (update_phi_ops ...) = resolve_phi prev ... when prev
   doesn't match old_label or new_label. *)
Theorem eval_phis_update_phis_for_split_other[local]:
  !s old_lbl new_lbl var_repls insts.
    (s.vs_prev_bb = NONE \/
     ?prev. s.vs_prev_bb = SOME prev /\
            prev <> old_lbl /\ prev <> new_lbl) ==>
    eval_phis s
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
        else inst with inst_operands :=
          update_phi_ops old_lbl new_lbl var_repls inst.inst_operands)
        insts) =
    eval_phis s insts
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `insts` >> simp[eval_phis_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def] >>
  Cases_on `s.vs_prev_bb` >> gvs[eval_one_phi_def] >>
  rename1 `SOME prev` >>
  `resolve_phi prev (update_phi_ops old_lbl new_lbl var_repls
    h.inst_operands) = resolve_phi prev h.inst_operands`
    by metis_tac[resolve_phi_update_phi_ops_other] >>
  Cases_on `resolve_phi prev h.inst_operands` >> gvs[eval_one_phi_def] >>
  Cases_on `eval_operand x' s` >> gvs[eval_one_phi_def] >>
  Cases_on `h.inst_outputs` >> gvs[eval_one_phi_def] >>
  Cases_on `eval_phis s rest` >> gvs[]
QED

(* Disjunction helper: vs_prev_bb = NONE gives the left disjunct *)
Theorem prev_bb_NONE_implies_other[local]:
  !s pred_lbl split_lbl.
    s.vs_prev_bb = NONE ==>
    s.vs_prev_bb = NONE \/
    ?prev. s.vs_prev_bb = SOME prev /\ prev <> pred_lbl /\ prev <> split_lbl
Proof
  simp[]
QED

(* If eval_one_phi returns SOME, the instruction must have exactly one output *)
Theorem eval_one_phi_imp_outputs[local]:
  !s inst out val.
    eval_one_phi s inst = SOME (out,val) ==> inst.inst_outputs = [out]
Proof
  rpt strip_tac >>
  gvs[eval_one_phi_def, AllCaseEqs()]
QED

(* Per-PHI forwarding: resolve_phi on original finds Var orig via pred_lbl,
   updated instruction finds Var new_v via split_lbl, and eval_operand
   gives same value because of execution_equiv + forwarding condition.
   General form: works for any instruction, with direct ∀orig conditions. *)

Theorem update_var_execution_preserves[local]:
  !vars x v s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (update_var x v s1) (update_var x v s2)
Proof
  rw[execution_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem eval_one_phi_forwarded_resolve[local]:
  !s1 s2 pred_lbl split_lbl var_repls inst out val.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    inst.inst_outputs = [out] /\
    inst.inst_opcode = PHI /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    eval_one_phi s1 inst = SOME (out,val) /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig /\
         new_v NOTIN vars) /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==> orig NOTIN vars)
    ==> eval_one_phi s2
        (inst with inst_operands :=
          update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) =
       SOME (out,val)
Proof
  rpt strip_tac >>
  `(inst with inst_operands :=
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands).inst_outputs =
    inst.inst_outputs` by simp[] >>
  `(inst with inst_operands :=
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands).inst_operands =
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands` by simp[] >>
  `?val_op. resolve_phi pred_lbl inst.inst_operands = SOME val_op /\
    eval_operand val_op s1 = SOME val` by (
    simp[eval_one_phi_def] >>
    Cases_on `inst.inst_outputs` >> gvs[eval_one_phi_def] >>
    Cases_on `s1.vs_prev_bb` >> gvs[eval_one_phi_def] >>
    Cases_on `resolve_phi pred_lbl inst.inst_operands` >> gvs[] >>
    Cases_on `eval_operand x s1` >> gvs[]) >>
  mp_tac (Q.SPECL [`pred_lbl`, `split_lbl`, `var_repls`,
    `inst.inst_operands`, `val_op`] resolve_phi_update_phi_ops_match) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `val_op` >> gvs[eval_one_phi_def, eval_operand_def, lookup_var_def, AllCaseEqs()] >>
  TRY (Cases_on `ALOOKUP var_repls s` >> gvs[eval_operand_def, lookup_var_def, AllCaseEqs()]) >>
  rfs[execution_equiv_def, lookup_var_def]
QED

(* v2: Same as eval_one_phi_forwarded_resolve but WITHOUT new_v NOTIN vars.
   The condition is unnecessary — the FLOOKUP precondition alone drives the proof.
   new_v NOTIN vars is UNPROVABLE when vars = COMPL(set(fn_all_vars func)) because
   var_repls_new_not_in_fn_all_vars gives new_v NOTIN fn_all_vars, which contradicts
   new_v IN fn_all_vars (needed for new_v NOTIN COMPL(fn_all_vars)). *)
Theorem eval_one_phi_forwarded_resolve_v2[local]:
  !s1 s2 pred_lbl split_lbl var_repls inst out val.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    inst.inst_outputs = [out] /\
    inst.inst_opcode = PHI /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    eval_one_phi s1 inst = SOME (out,val) /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig) /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==> orig NOTIN vars)
    ==> eval_one_phi s2
        (inst with inst_operands :=
          update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) =
       SOME (out,val)
Proof
  rpt strip_tac >>
  `(inst with inst_operands :=
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands).inst_outputs =
    inst.inst_outputs` by simp[] >>
  `(inst with inst_operands :=
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands).inst_operands =
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands` by simp[] >>
  `?val_op. resolve_phi pred_lbl inst.inst_operands = SOME val_op /\
    eval_operand val_op s1 = SOME val` by (
    simp[eval_one_phi_def] >>
    Cases_on `inst.inst_outputs` >> gvs[eval_one_phi_def] >>
    Cases_on `s1.vs_prev_bb` >> gvs[eval_one_phi_def] >>
    Cases_on `resolve_phi pred_lbl inst.inst_operands` >> gvs[] >>
    Cases_on `eval_operand x s1` >> gvs[]) >>
  mp_tac (Q.SPECL [`pred_lbl`, `split_lbl`, `var_repls`,
    `inst.inst_operands`, `val_op`] resolve_phi_update_phi_ops_match) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `val_op` >> gvs[eval_one_phi_def, eval_operand_def, lookup_var_def, AllCaseEqs()] >>
  TRY (Cases_on `ALOOKUP var_repls s` >> gvs[eval_operand_def, lookup_var_def, AllCaseEqs()]) >>
  rfs[execution_equiv_def, lookup_var_def]
QED

(* Forwarding case: eval_phis on original instructions with s1.vs_prev_bb = SOME pred_lbl
   and eval_phis on updated instructions with s2.vs_prev_bb = SOME split_lbl.
   Both succeed with execution_equiv results, provided var_repls forwarding holds. *)

(* Per-PHI forwarding: resolve_phi on original finds Var orig via pred_lbl,
   updated instruction finds Var new_v via split_lbl, and eval_operand
   gives same value because of execution_equiv + forwarding condition. *)
Theorem eval_one_phi_forwarded[local]:
  !s1 s2 pred_lbl split_lbl var_repls inst orig new_v v out vars.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    inst.inst_outputs = [out] /\
    resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
    ALOOKUP var_repls orig = SOME new_v /\
    FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig /\
    IS_SOME (FLOOKUP s1.vs_vars orig) /\
    new_v NOTIN vars /\
    resolve_phi split_lbl inst.inst_operands = NONE
    ==> eval_one_phi s2
        (inst with inst_operands :=
          update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) =
       SOME (out, THE (FLOOKUP s1.vs_vars orig))
Proof
  rpt strip_tac >>
  `(inst with inst_operands :=
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands).inst_outputs =
    inst.inst_outputs` by simp[] >>
  `(inst with inst_operands :=
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands).inst_operands =
    update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands` by simp[] >>
  simp[eval_one_phi_def] >>
  Cases_on `inst.inst_outputs` >> gvs[eval_one_phi_def] >>
  mp_tac (Q.SPECL [`pred_lbl`, `split_lbl`, `var_repls`,
    `inst.inst_operands`, `Var orig`] resolve_phi_update_phi_ops_match) >>
  impl_tac >- simp[] >>
  strip_tac >>
  gvs[eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s1.vs_vars orig` >> gvs[]
QED

Theorem eval_phis_update_phis_for_split_forwarded[local]:
  !s1 s2 pred_lbl split_lbl var_repls insts vars func.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
       resolve_phi split_lbl inst.inst_operands = NONE) /\
    (!inst orig. MEM inst insts /\ inst.inst_opcode = PHI /\
       resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig /\
         new_v NOTIN vars) /\
    (!inst orig. MEM inst insts /\ inst.inst_opcode = PHI /\
       resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==>
       orig NOTIN vars) /\
    eval_phis s1 insts = OK s1'
    ==> ?s2'. eval_phis s2
         (MAP (\inst. if inst.inst_opcode <> PHI then inst
           else inst with inst_operands :=
             update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands)
           insts) = OK s2' /\
       execution_equiv vars s1' s2' /\
       s2'.vs_current_bb = s1'.vs_current_bb /\
       s2'.vs_inst_idx = s1'.vs_inst_idx /\
       s2'.vs_prev_bb = s2.vs_prev_bb /\
       s2'.vs_halted = s1'.vs_halted
Proof
  qid_spec_tac `s1'` >>
  Induct_on `insts` >> rpt gen_tac >> strip_tac
  >- (
    `s1' = s1` by fs[eval_phis_def] >>
    qexists_tac `s2` >>
    qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
    simp[eval_phis_def] >>
    fs[execution_equiv_def])
  >- (
    qpat_x_assum `eval_phis s1 (h::insts) = OK s1'` mp_tac >>
    PURE_ONCE_REWRITE_TAC[eval_phis_def] >>
    IF_CASES_TAC
    >- (
      simp[] >> strip_tac >>
      qexists_tac `s2` >>
      simp[Once eval_phis_def] >>
      fs[execution_equiv_def])
    >- (
      simp[] >>
      Cases_on `eval_one_phi s1 h` >> gvs[exec_result_distinct] >>
      PairCases_on `x` >> gvs[] >>
      Cases_on `eval_phis s1 insts` >> gvs[exec_result_distinct] >>
      strip_tac >>
      (* Apply IH: specialize all universally quantified variables *)
      first_x_assum (qspecl_then
        [`v`,`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`vars`] mp_tac) >>
      impl_tac >- (
        rpt conj_tac >-
          simp[] >-
          simp[] >-
          simp[] >-
          simp[] >-
          simp[] >-
          simp[] >-
          (rpt strip_tac >> res_tac >> simp[]) >-
          (rpt strip_tac >> res_tac >> simp[]) >-
          (rpt strip_tac >> res_tac >> simp[])) >>
      strip_tac >>
      qexists_tac `update_var x0 x1 s2''` >>
      (* First conjunct: eval_phis on updated instructions yields same result *)
      conj_tac >- (
        imp_res_tac eval_one_phi_imp_outputs >>
        mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,
          `h`,`x0`,`x1`] eval_one_phi_forwarded_resolve) >>
        impl_tac >- metis_tac[] >>
        strip_tac >>
        PURE_ONCE_REWRITE_TAC[eval_phis_def] >>
        simp[]) >>
      (* Second conjunct: execution_equiv via boundary lemma *)
      conj_tac >- (
        mp_tac (Q.SPECL [`vars`,`x0`,`x1`,`v`,`s2''`] update_var_execution_preserves) >>
        simp[]) >>
      (* Remaining field preservation conjuncts: update_var only touches vs_vars *)
      rpt conj_tac >> rw[update_var_def]))
QED

(* v2: Same as eval_phis_update_phis_for_split_forwarded but WITHOUT new_v NOTIN vars. *)
Theorem eval_phis_update_phis_for_split_forwarded_v2[local]:
  !s1 s2 pred_lbl split_lbl var_repls insts vars func.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
       resolve_phi split_lbl inst.inst_operands = NONE) /\
    (!inst orig. MEM inst insts /\ inst.inst_opcode = PHI /\
       resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig) /\
    (!inst orig. MEM inst insts /\ inst.inst_opcode = PHI /\
       resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==> orig NOTIN vars) /\
    eval_phis s1 insts = OK s1'
    ==> ?s2'. eval_phis s2
         (MAP (\inst. if inst.inst_opcode <> PHI then inst
           else inst with inst_operands :=
             update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands)
           insts) = OK s2' /\
       execution_equiv vars s1' s2' /\
       s2'.vs_current_bb = s1'.vs_current_bb /\
       s2'.vs_inst_idx = s1'.vs_inst_idx /\
       s2'.vs_prev_bb = s2.vs_prev_bb /\
       s2'.vs_halted = s1'.vs_halted
Proof
  qid_spec_tac `s1'` >>
  Induct_on `insts` >> rpt gen_tac >> strip_tac
  >- (
    `s1' = s1` by fs[eval_phis_def] >>
    qexists_tac `s2` >>
    qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
    simp[eval_phis_def] >>
    fs[execution_equiv_def])
  >- (
    qpat_x_assum `eval_phis s1 (h::insts) = OK s1'` mp_tac >>
    PURE_ONCE_REWRITE_TAC[eval_phis_def] >>
    IF_CASES_TAC
    >- (
      simp[] >> strip_tac >>
      qexists_tac `s2` >>
      simp[Once eval_phis_def] >>
      fs[execution_equiv_def])
    >- (
      simp[] >>
      Cases_on `eval_one_phi s1 h` >> gvs[exec_result_distinct] >>
      PairCases_on `x` >> gvs[] >>
      Cases_on `eval_phis s1 insts` >> gvs[exec_result_distinct] >>
      strip_tac >>
      first_x_assum (qspecl_then
        [`v`,`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`vars`] mp_tac) >>
      impl_tac >- (
        rpt conj_tac >- simp[] >- simp[] >- simp[] >- simp[] >- simp[] >- simp[]
        >- (rpt strip_tac >> res_tac >> simp[])
        >- (rpt strip_tac >> res_tac >> simp[])
        >- (rpt strip_tac >> res_tac >> simp[])) >>
      strip_tac >>
      qexists_tac `update_var x0 x1 s2''` >>
      conj_tac >- (
        imp_res_tac eval_one_phi_imp_outputs >>
        mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,
          `h`,`x0`,`x1`] eval_one_phi_forwarded_resolve_v2) >>
        impl_tac >- metis_tac[] >>
        strip_tac >>
        PURE_ONCE_REWRITE_TAC[eval_phis_def] >>
        simp[]) >>
      conj_tac >- (
        mp_tac (Q.SPECL [`vars`,`x0`,`x1`,`v`,`s2''`] update_var_execution_preserves) >>
        simp[]) >>
      rpt conj_tac >> rw[update_var_def]))
QED
(* eval_phis equality for update_phis_for_split, stated directly on the
   update_phis_for_split record projection to avoid simp blowing up lambdas *)
Theorem eval_phis_update_phis_for_split_target_eq[local]:
  !s pred_lbl split_lbl var_repls target_bb.
    (s.vs_prev_bb = NONE \/
     ?prev. s.vs_prev_bb = SOME prev /\
            prev <> pred_lbl /\ prev <> split_lbl) ==>
    eval_phis s (update_phis_for_split pred_lbl split_lbl var_repls target_bb).bb_instructions =
    eval_phis s target_bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  simp[update_phis_for_split_def] >>
  irule eval_phis_update_phis_for_split_other >> simp[]
QED

(* phi_prefix_length equality for update_phis_for_split *)
Theorem phi_prefix_length_update_phis_for_split_eq[local]:
  !pred_lbl split_lbl var_repls target_bb.
    phi_prefix_length (update_phis_for_split pred_lbl split_lbl var_repls target_bb).bb_instructions =
    phi_prefix_length target_bb.bb_instructions
Proof
  rpt gen_tac >>
  simp[update_phis_for_split_def] >>
  irule phi_prefix_length_map_congruent >>
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> simp[update_phis_for_split_def]
QED

Theorem phi_prefix_length_all_phi[local]:
  !insts i. i < phi_prefix_length insts ==> (EL i insts).inst_opcode = PHI
Proof
  Induct_on `insts` >> simp[phi_prefix_length_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `i` >> simp[]
QED

Theorem phi_prefix_length_at_nonphi[local]:
  !insts. phi_prefix_length insts < LENGTH insts ==>
    (EL (phi_prefix_length insts) insts).inst_opcode <> PHI
Proof
  Induct_on `insts` >> simp[phi_prefix_length_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def]
QED

(* bb_well_formed implies phi_prefix_length < LENGTH: the last instruction
   is always a terminator (not PHI), so PHI prefix must be shorter. *)
Theorem bb_well_formed_phi_prefix_length_lt[local]:
  !bb. bb_well_formed bb ==>
    phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  `LENGTH bb.bb_instructions <= phi_prefix_length bb.bb_instructions`
    by simp[arithmeticTheory.NOT_LT] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions`
    by simp[phi_prefix_length_le] >>
  `phi_prefix_length bb.bb_instructions = LENGTH bb.bb_instructions`
    by decide_tac >>
  fs[bb_well_formed_def] >>
  `~is_terminator PHI` by simp[is_terminator_def] >>
  `is_terminator
    (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode`
    by metis_tac[listTheory.LAST_EL] >>
  `LENGTH bb.bb_instructions <> 0` by
    (Cases_on `bb.bb_instructions` >> simp[]) >>
  `PRE (LENGTH bb.bb_instructions) < phi_prefix_length bb.bb_instructions`
    by simp[] >>
  `bb.bb_instructions❲PRE (LENGTH bb.bb_instructions)❳.inst_opcode = PHI`
    by metis_tac[phi_prefix_length_all_phi] >>
  metis_tac[]
QED

(* Boundary lemma: run_block on update_phis_for_split bb = run_block on original bb
   when vs_prev_bb doesn't match the relabeled labels. *)
Theorem run_block_update_phis_for_split_target[local]:
  !fuel ctx pred_lbl split_lbl var_repls target_bb s.
    (s.vs_prev_bb = NONE \/
     ?prev. s.vs_prev_bb = SOME prev /\
            prev <> pred_lbl /\ prev <> split_lbl) ==>
    run_block fuel ctx
      (update_phis_for_split pred_lbl split_lbl var_repls target_bb) s =
    run_block fuel ctx target_bb s
Proof
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[eval_phis_update_phis_for_split_target_eq,
       phi_prefix_length_update_phis_for_split_eq] >>
  Cases_on `eval_phis s target_bb.bb_instructions` >> gvs[] >>
  imp_res_tac eval_phis_only_updates_vs_vars >> gvs[] >>
  (* v.vs_prev_bb = s.vs_prev_bb, so the condition transfers to the exec_block state *)
  irule run_block_update_phis_other >>
  Cases_on `s.vs_prev_bb` >> gvs[] >- (
    disj1_tac >> fs[venom_state_component_equality]) >>
  disj2_tac >> qexists_tac `prev` >> fs[venom_state_component_equality]
QED
(* resolve_phi returns an operand that is MEM of the original list *)
Theorem resolve_phi_MEM_operands[local]:
  !prev_bb ops val_op. resolve_phi prev_bb ops = SOME val_op ==> MEM val_op ops
Proof
  recInduct resolve_phi_ind >> rw[resolve_phi_def]
QED

(* resolve_phi = OPTION_MAP Var o ALOOKUP (phi_pairs ops) when phi_well_formed *)
Theorem resolve_phi_phi_pairs[local]:
  !ops l. phi_well_formed ops ==>
    resolve_phi l ops = OPTION_MAP Var (ALOOKUP (phi_pairs ops) l)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def, phi_pairs_def, alistTheory.ALOOKUP_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  TRY (Cases_on `v3` >> simp[phi_pairs_def]) >>
  BasicProvers.every_case_tac >> simp[]
QED

(* MEM v (phi_vars_needing_forward) ==> exists PHI inst with resolve_phi *)
Theorem phi_vars_resolve_phi[local]:
  !lbl pred_bb insts v.
    MEM v (phi_vars_needing_forward lbl pred_bb insts) ==>
    ?inst'. MEM inst' insts /\ inst'.inst_opcode = PHI /\
      MEM (lbl, v) (phi_pairs inst'.inst_operands)
Proof
  Induct_on `insts` >>
  rw[phi_vars_needing_forward_def, LET_THM] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_vars_needing_forward_def, LET_THM] >>
  gvs[listTheory.MEM_APPEND, listTheory.MEM_MAP, listTheory.MEM_FILTER,
      pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

(* Combined: phi_vars_needing_forward variable has resolve_phi = SOME (Var v)
   when the PHI instruction is well-formed and labels are distinct *)
Theorem phi_vars_resolve_phi_full[local]:
  !lbl pred_bb insts v func bb.
    fn_inst_wf func /\ fn_phi_labels_distinct func /\
    MEM bb func.fn_blocks /\
    bb.bb_instructions = insts /\
    MEM v (phi_vars_needing_forward lbl pred_bb insts) ==>
    ?inst'. MEM inst' insts /\ inst'.inst_opcode = PHI /\
      resolve_phi lbl inst'.inst_operands = SOME (Var v)
Proof
  rpt strip_tac >>
  drule phi_vars_resolve_phi >> strip_tac >>
  qexists_tac `inst'` >> simp[] >>
  `inst_wf inst'` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed inst'.inst_operands` by
    (Cases_on `inst'.inst_opcode` >> gvs[inst_wf_def]) >>
  drule resolve_phi_phi_pairs >>
  disch_then (qspec_then `lbl` mp_tac) >> simp[] >>
  strip_tac >>
  `ALL_DISTINCT (MAP FST (phi_pairs inst'.inst_operands))` by
    (fs[fn_phi_labels_distinct_def] >> metis_tac[]) >>
  `ALOOKUP (phi_pairs inst'.inst_operands) lbl = SOME v` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >> simp[])
QED

(* resolve_phi on well-formed PHI operands always returns a Var *)
Theorem resolve_phi_returns_var[local]:
  !lbl ops val_op.
    phi_well_formed ops /\ resolve_phi lbl ops = SOME val_op ==>
    ?vn. val_op = Var vn
Proof
  Induct_on `ops` using phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def] >>
  rw[] >> metis_tac[]
QED

(* If old_label has no resolve_phi match, update_phi_ops is identity *)
Theorem update_phi_ops_no_match[local]:
  !old_label new_label var_repls ops.
    resolve_phi old_label ops = NONE ==>
    update_phi_ops old_label new_label var_repls ops = ops
Proof
  ho_match_mp_tac update_phi_ops_ind >>
  simp[update_phi_ops_def, resolve_phi_def]
QED

(* PHI step error preservation: if step_inst_base errors on sa,
   step_inst_base on the updated inst also errors on sb *)
Theorem step_inst_phi_error_preserved:
  !inst sa sb pred_lbl split_lbl var_repls e.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    sa.vs_prev_bb = SOME pred_lbl /\
    sb.vs_prev_bb = SOME split_lbl /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    (!x. MEM (Var x) inst.inst_operands ==>
       FLOOKUP sb.vs_vars x = FLOOKUP sa.vs_vars x) /\
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP sb.vs_vars new_v = FLOOKUP sa.vs_vars orig) /\
    step_inst_base inst sa = Error e ==>
    ?e'. step_inst_base
      (inst with inst_operands :=
        update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) sb =
      Error e'
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

(* PHI step: after parallel PHI semantics change, step_inst_base PHI always
   returns Error. PHI evaluation now happens in eval_phis at block entry.
   This theorem captures the forwarding property at the eval_one_phi level
   instead: if the original phi resolves and the forwarded phi doesn't match
   (because pred_lbl was split), the forwarded state gets an equivalent result
   via eval_one_phi. *)
Theorem step_inst_phi_forwarded[local]:
  !fuel ctx inst s1 s2 pred_lbl split_lbl var_repls out v val.
    inst.inst_opcode = PHI /\
    inst_wf inst /\
    inst.inst_outputs = [out] /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    resolve_phi pred_lbl inst.inst_operands = SOME (Var v) /\
    FLOOKUP s1.vs_vars v = SOME val /\
    (!x. MEM (Var x) inst.inst_operands ==>
       FLOOKUP s2.vs_vars x = FLOOKUP s1.vs_vars x) /\
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig) ==>
    step_inst fuel ctx inst s1 = Error "phi outside prefix" /\
    step_inst fuel ctx
      (inst with inst_operands :=
        update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) s2 =
      Error "phi outside prefix"
Proof
  rpt strip_tac >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

(* Complete characterization of step_inst_base for PHI --
   either succeeds with resolved Var and update, or returns Error;
   never returns Halt, Abort, or IntRet *)
Theorem step_inst_base_PHI_cases:
  !inst s prev.
    inst.inst_opcode = PHI /\ inst_wf inst /\ s.vs_prev_bb = SOME prev ==>
    (?out vn val'.
        inst.inst_outputs = [out] /\
        resolve_phi prev inst.inst_operands = SOME (Var vn) /\
        FLOOKUP s.vs_vars vn = SOME val' /\
        step_inst_base inst s = OK (update_var out val' s)) \/
    (?e. step_inst_base inst s = Error e)
Proof
  rpt strip_tac >> disj2_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

(* Corollary: extract OK facts from step_inst_base PHI *)
Theorem step_inst_base_PHI_OK_var:
  !inst s s' pred_lbl.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    phi_well_formed inst.inst_operands /\
    s.vs_prev_bb = SOME pred_lbl /\
    step_inst_base inst s = OK s' ==>
    ?out vn val.
      inst.inst_outputs = [out] /\
      resolve_phi pred_lbl inst.inst_operands = SOME (Var vn) /\
      FLOOKUP s.vs_vars vn = SOME val /\
      s' = update_var out val s
Proof
  rpt strip_tac >>
  mp_tac step_inst_base_PHI_cases >>
  disch_then (qspecl_then [`inst`, `s`, `pred_lbl`] mp_tac) >> simp[]
QED

(* Corollary: extract raw OK facts (used by forwarding_preserved_by_update_var) *)
Theorem step_inst_base_PHI_OK[local]:
  !inst s s'.
    inst.inst_opcode = PHI /\ inst_wf inst /\
    step_inst_base inst s = OK s' ==>
    ?out prev val_op v.
      inst.inst_outputs = [out] /\
      s.vs_prev_bb = SOME prev /\
      resolve_phi prev inst.inst_operands = SOME val_op /\
      eval_operand val_op s = SOME v /\
      s' = update_var out v s
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

(* Reusable helper: instruction output is in fn_all_vars *)
Theorem inst_output_in_fn_all_vars[local]:
  !func bb inst out.
    MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM out inst.inst_outputs ==>
    MEM out (fn_all_vars func)
Proof
  rw[] >>
  `fn_vars_in (set (fn_all_vars func)) func` by simp[fn_vars_in_fn_all_vars] >>
  fs[fn_vars_in_def] >>
  first_x_assum (qspec_then `bb` mp_tac) >> rw[] >>
  fs[block_vars_in_def] >>
  first_x_assum (qspec_then `inst` mp_tac) >> rw[]
QED

(* Reusable helper: operand Var name is in fn_all_vars *)
Theorem inst_operand_var_in_fn_all_vars:
  !func bb inst x.
    MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM (Var x) inst.inst_operands ==>
    MEM x (fn_all_vars func)
Proof
  rw[] >>
  `fn_vars_in (set (fn_all_vars func)) func` by simp[fn_vars_in_fn_all_vars] >>
  fs[fn_vars_in_def] >>
  first_x_assum (qspec_then `bb` mp_tac) >> rw[] >>
  fs[block_vars_in_def] >>
  first_x_assum (qspec_then `inst` mp_tac) >> rw[]
QED

(* Reusable helper: execution_equiv + var in fn_all_vars => FLOOKUP equal *)
Theorem execution_equiv_lookup_fn_var:
  !func s1 s2 x.
    execution_equiv (COMPL (set (fn_all_vars func))) s1 s2 /\
    MEM x (fn_all_vars func) ==>
    FLOOKUP s1.vs_vars x = FLOOKUP s2.vs_vars x
Proof
  rw[execution_equiv_def] >>
  `x NOTIN COMPL (set (fn_all_vars func))` by simp[] >>
  res_tac >> fs[lookup_var_def]
QED

(* Two blocks that agree on instructions from current index onward
   produce identical exec_block results *)
Theorem run_block_same_suffix[local]:
  !fuel ctx bb1 bb2 s.
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!k. s.vs_inst_idx <= k /\ k < LENGTH bb1.bb_instructions ==>
         EL k bb1.bb_instructions = EL k bb2.bb_instructions) ==>
    exec_block fuel ctx bb1 s = exec_block fuel ctx bb2 s
Proof
  completeInduct_on `LENGTH bb1.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  CONV_TAC (ONCE_REWRITE_CONV [exec_block_def]) >>
  Cases_on `get_instruction bb1 s.vs_inst_idx`
  >- (
    simp[] >>
    `get_instruction bb2 s.vs_inst_idx = NONE` by
      (fs[get_instruction_def] >> BasicProvers.every_case_tac >> fs[]) >>
    simp[]
  )
  >- (
    simp[] >>
    `s.vs_inst_idx < LENGTH bb1.bb_instructions` by
      fs[get_instruction_def, AllCaseEqs()] >>
    `get_instruction bb2 s.vs_inst_idx = SOME x` by (
      fs[get_instruction_def] >>
      `EL s.vs_inst_idx bb1.bb_instructions =
       EL s.vs_inst_idx bb2.bb_instructions` by (first_x_assum irule >> simp[]) >>
      fs[]) >>
    simp[] >>
    Cases_on `step_inst fuel ctx x s` >> simp[] >>
    Cases_on `is_terminator x.inst_opcode` >> simp[] >>
    first_x_assum (qspec_then
      `LENGTH bb1.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qspecl_then [`bb1`, `v with vs_inst_idx := SUC s.vs_inst_idx`]
      mp_tac) >>
    simp[] >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb2`] mp_tac) >>
    simp[]
  )
QED


Triviality step_inst_base_DRET_not_OK:
  !inst s r. inst.inst_opcode = DRET ==>
    step_inst_base inst s <> OK r
Proof
  rpt strip_tac >>
  gvs[step_inst_base_def] >>
  Cases_on `inst.inst_outputs = []` >> gvs[] >>
  Cases_on `parse_dret_shape inst` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `eval_operands inst.inst_operands s` >> gvs[] >>
  Cases_on `pair_dret_words
    (TAKE (2 * x1) (DROP (1 + x0) x))` >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Triviality step_inst_base_RETFMP_not_OK:
  !inst s r. inst.inst_opcode = RETFMP ==>
    step_inst_base inst s <> OK r
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  Cases_on `eval_operands inst.inst_operands s` >> gvs[] >>
  Cases_on `x` >> gvs[]
QED
val term_ok_jump_tac =
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, eval_operands_def, eval_operand_def,
       AllCaseEqs()] >>
  rpt CASE_TAC >> gvs[] >> rpt strip_tac >> pairarg_tac >> gvs[];

Triviality step_inst_base_ok_terminator_jump:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
    inst.inst_opcode = DJMP
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  TRY (rename1 `inst.inst_opcode = DRET` >>
       metis_tac[step_inst_base_DRET_not_OK]) >>
  TRY (rename1 `inst.inst_opcode = RETFMP` >>
       metis_tac[step_inst_base_RETFMP_not_OK]) >>
  TRY (rename1 `inst.inst_opcode = RET` >> term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = RETURN` >> term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = REVERT` >> term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = STOP` >> term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = SINK` >> term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = SELFDESTRUCT` >> term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = INVALID` >> term_ok_jump_tac)
QED

(* Unified helper: step_inst_base on a non-PHI instruction with
   execution_equiv states. For non-terminators: preserves execution_equiv +
   current_bb + inst_idx + ~halted. For terminators (jumps): additionally
   preserves prev_bb, giving full state_equiv. *)
Theorem step_non_phi_exec_equiv[local]:
  !inst s1 s2 func bb r1.
    fn_inst_wf func /\ MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst.inst_opcode <> PHI /\
    execution_equiv (COMPL (set (fn_all_vars func))) s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    ~s1.vs_halted /\
    step_inst_base inst s1 = OK r1 ==>
    ?r2. step_inst_base inst s2 = OK r2 /\
         execution_equiv (COMPL (set (fn_all_vars func))) r1 r2 /\
         r1.vs_current_bb = r2.vs_current_bb /\
         r1.vs_inst_idx = r2.vs_inst_idx /\
         (is_terminator inst.inst_opcode ==>
            state_equiv (COMPL (set (fn_all_vars func))) r1 r2) /\
         (~is_terminator inst.inst_opcode ==> ~r1.vs_halted)
Proof
  rpt strip_tac >>
  qabbrev_tac `s_mid = s2 with vs_prev_bb := s1.vs_prev_bb` >>
  `state_equiv (COMPL (set (fn_all_vars func))) s1 s_mid` by
    (fs[state_equiv_def, markerTheory.Abbrev_def, execution_equiv_def,
        lookup_var_def]) >>
  `!x. MEM (Var x) inst.inst_operands ==>
       x NOTIN COMPL (set (fn_all_vars func))` by
    (rw[pred_setTheory.IN_COMPL] >>
     irule inst_operand_var_in_fn_all_vars >>
     qexistsl_tac [`bb`, `inst`] >> simp[]) >>
  `result_equiv (COMPL (set (fn_all_vars func)))
     (step_inst_base inst s1) (step_inst_base inst s_mid)` by
    (irule step_inst_result_equiv >> simp[]) >>
  `?r_mid. step_inst_base inst s_mid = OK r_mid /\
           state_equiv (COMPL (set (fn_all_vars func))) r1 r_mid` by (
    qpat_x_assum `result_equiv _ _ _` mp_tac >>
    qpat_x_assum `step_inst_base inst s1 = _` (fn th => REWRITE_TAC[th]) >>
    Cases_on `step_inst_base inst s_mid` >>
    simp[result_equiv_def]) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP` by
      metis_tac[step_inst_base_ok_terminator_jump] >>
    `step_inst_base inst s_mid = step_inst_base inst s2` by (
      qunabbrev_tac `s_mid` >>
      simp[GSYM step_inst_base_jump_prev_bb]) >>
    `?r2. step_inst_base inst s2 = OK r2` by metis_tac[] >>
    qexists_tac `r2` >> gvs[] >>
    fs[state_equiv_def])
  >- (
    `step_inst_base inst s_mid =
       exec_result_map_prev_bb (\s'. s' with vs_prev_bb := s1.vs_prev_bb)
         (step_inst_base inst s2)` by (
      qunabbrev_tac `s_mid` >>
      irule step_inst_base_prev_bb_indep >> simp[]) >>
    `?r2. step_inst_base inst s2 = OK r2 /\
          r_mid = r2 with vs_prev_bb := s1.vs_prev_bb` by (
      qpat_x_assum `_ = exec_result_map_prev_bb _ _` mp_tac >>
      qpat_x_assum `step_inst_base inst s_mid = OK _`
        (fn th => REWRITE_TAC[th]) >>
      Cases_on `step_inst_base inst s2` >>
      simp[exec_result_map_prev_bb_def]) >>
    qexists_tac `r2` >> rpt conj_tac
    >- simp[]
    >- (fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
        rw[] >> res_tac >> fs[])
    >- fs[state_equiv_def]
    >- fs[state_equiv_def]
    >- simp[]
    >- (imp_res_tac step_inst_base_OK_preserves_halted >> fs[]))
QED

(* FOLDL update_var preserves vs_prev_bb *)
Theorem foldl_update_var_prev_bb[local]:
  !pairs s p.
    FOLDL (\s' (out,val). update_var out val s') (s with vs_prev_bb := p)
      pairs =
    (FOLDL (\s' (out,val). update_var out val s') s pairs)
      with vs_prev_bb := p
Proof
  Induct >> simp[] >>
  Cases >> rpt gen_tac >>
  simp[update_var_def] >>
  first_x_assum (qspecl_then
    [`s with vs_vars := s.vs_vars |+ (q, r)`, `p`] mp_tac) >>
  simp[update_var_def]
QED

Theorem adopt_return_fmp_prev_bb[local]:
  !ir s p.
    adopt_return_fmp ir (s with vs_prev_bb := p) =
    (adopt_return_fmp ir s) with vs_prev_bb := p
Proof
  rpt gen_tac >> Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, venom_state_component_equality]
QED

(* INVOKE OK: changing caller's prev_bb changes only result's prev_bb *)
Theorem step_inst_invoke_OK_prev_bb[local]:
  !fuel ctx inst s p r.
    inst.inst_opcode = INVOKE /\
    step_inst fuel ctx inst s = OK r ==>
    step_inst fuel ctx inst (s with vs_prev_bb := p) =
      OK (r with vs_prev_bb := p)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands x1 s` >> simp[] >>
  simp[setup_callee_def] >>
  Cases_on `NULL x.fn_blocks` >> simp[] >>
  Cases_on `NULL x'` >> simp[] >>
  qabbrev_tac `callee_s = s with <|vs_vars := FEMPTY; vs_prev_bb := NONE;
    vs_current_bb := (HD x.fn_blocks).bb_label;
    vs_inst_idx := 0; vs_halted := F; vs_params := x';
    vs_fmp := s.vs_fmp; vs_call_entry_fmp := s.vs_fmp;
    vs_return_pc_token := LAST x'; vs_allocas := FEMPTY|>` >>
  Cases_on `run_blocks fuel ctx x callee_s` >> simp[] >>
  simp[merge_callee_state_def, bind_outputs_def] >>
  Cases_on `LENGTH inst.inst_outputs = LENGTH i.iret_values` >> simp[] >>
  strip_tac >>
  simp[Once step_inst_def] >>
  `!ops. eval_operands ops (s with vs_prev_bb := p) = eval_operands ops s` by
    (Induct >> simp[eval_operands_def] >>
     Cases >> simp[eval_operand_def, lookup_var_def] >>
     BasicProvers.every_case_tac >> simp[]) >>
  simp[setup_callee_def] >>
  `(s with vs_prev_bb := p) with <|vs_vars := FEMPTY; vs_prev_bb := NONE;
    vs_current_bb := (HD x.fn_blocks).bb_label;
    vs_inst_idx := 0; vs_halted := F; vs_params := x';
    vs_fmp := s.vs_fmp; vs_call_entry_fmp := s.vs_fmp;
    vs_return_pc_token := LAST x'; vs_allocas := FEMPTY|> = callee_s` by
    (qunabbrev_tac `callee_s` >> simp[]) >>
  simp[merge_callee_state_def, bind_outputs_def] >>
  gvs[] >>
  `s with
     <|vs_memory := v.vs_memory; vs_transient := v.vs_transient;
       vs_prev_bb := p; vs_returndata := v.vs_returndata;
       vs_accounts := v.vs_accounts; vs_logs := v.vs_logs;
       vs_immutables := v.vs_immutables;
       vs_alloca_next := v.vs_alloca_next|> =
   (s with
     <|vs_memory := v.vs_memory; vs_transient := v.vs_transient;
       vs_returndata := v.vs_returndata; vs_accounts := v.vs_accounts;
       vs_logs := v.vs_logs; vs_immutables := v.vs_immutables;
       vs_alloca_next := v.vs_alloca_next|>) with vs_prev_bb := p` by simp[] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  simp[adopt_return_fmp_prev_bb, foldl_update_var_prev_bb]
QED

(* INVOKE case of step_inst execution equivalence, extracted for clean
   assumption context. Uses intermediate state trick + prev_bb independence. *)
Theorem step_inst_invoke_exec_equiv[local]:
  !fuel ctx inst s1 s2 func bb r1.
    fn_inst_wf func /\ MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst.inst_opcode = INVOKE /\
    execution_equiv (COMPL (set (fn_all_vars func))) s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    ~s1.vs_halted /\
    step_inst fuel ctx inst s1 = OK r1 ==>
    ?r2. step_inst fuel ctx inst s2 = OK r2 /\
         execution_equiv (COMPL (set (fn_all_vars func))) r1 r2 /\
         r1.vs_current_bb = r2.vs_current_bb /\
         r1.vs_inst_idx = r2.vs_inst_idx /\
         ~r1.vs_halted
Proof
  rpt strip_tac >>
  qabbrev_tac `s_mid = s2 with vs_prev_bb := s1.vs_prev_bb` >>
  (`state_equiv (COMPL (set (fn_all_vars func))) s1 s_mid` by
    (fs[state_equiv_def, markerTheory.Abbrev_def, execution_equiv_def,
        lookup_var_def])) >>
  (`!x. MEM (Var x) inst.inst_operands ==>
       x NOTIN COMPL (set (fn_all_vars func))` by
    (rw[pred_setTheory.IN_COMPL] >>
     irule inst_operand_var_in_fn_all_vars >>
     qexistsl_tac [`bb`, `inst`] >> simp[])) >>
  (`!x. MEM x inst.inst_outputs ==>
       x NOTIN COMPL (set (fn_all_vars func))` by
    (rw[pred_setTheory.IN_COMPL] >>
     irule inst_output_in_fn_all_vars >>
     qexistsl_tac [`bb`, `inst`] >> simp[])) >>
  (`result_equiv (COMPL (set (fn_all_vars func)))
     (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s_mid)` by
    (irule step_inst_invoke_frame >> simp[])) >>
  (`?r_mid. step_inst fuel ctx inst s_mid = OK r_mid /\
           state_equiv (COMPL (set (fn_all_vars func))) r1 r_mid` by (
    qpat_x_assum `result_equiv _ _ _` mp_tac >>
    qpat_x_assum `step_inst fuel ctx inst s1 = _` (fn th =>
      REWRITE_TAC[th]) >>
    Cases_on `step_inst fuel ctx inst s_mid` >>
    simp[result_equiv_def])) >>
  (`step_inst fuel ctx inst
     (s_mid with vs_prev_bb := s2.vs_prev_bb) =
     OK (r_mid with vs_prev_bb := s2.vs_prev_bb)` by
    (irule (REWRITE_RULE [AND_IMP_INTRO] step_inst_invoke_OK_prev_bb) >>
     simp[])) >>
  (`s_mid with vs_prev_bb := s2.vs_prev_bb = s2` by
    (qunabbrev_tac `s_mid` >> simp[venom_state_component_equality])) >>
  qexists_tac `r_mid with vs_prev_bb := s2.vs_prev_bb` >>
  gvs[] >>
  rpt conj_tac
  >- (fs[execution_equiv_def, state_equiv_def, lookup_var_def])
  >- (fs[state_equiv_def])
  >- (fs[state_equiv_def])
  >- (`~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
      imp_res_tac step_preserves_halted >> fs[])
QED

(* step_inst-level equiv for non-PHI non-terminator instructions.
   Handles INVOKE via step_inst_invoke_exec_equiv.
   Non-INVOKE via step_inst_base + step_non_phi_exec_equiv. *)
Theorem step_inst_non_phi_non_term_exec_equiv[local]:
  !fuel ctx inst s1 s2 func bb r1.
    fn_inst_wf func /\ MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
    execution_equiv (COMPL (set (fn_all_vars func))) s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    ~s1.vs_halted /\
    step_inst fuel ctx inst s1 = OK r1 ==>
    ?r2. step_inst fuel ctx inst s2 = OK r2 /\
         execution_equiv (COMPL (set (fn_all_vars func))) r1 r2 /\
         r1.vs_current_bb = r2.vs_current_bb /\
         r1.vs_inst_idx = r2.vs_inst_idx /\
         ~r1.vs_halted
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_exec_equiv >> strip_tac >>
      qexists_tac `r2` >> simp[])
  >- (
    `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
      (irule step_inst_non_invoke >> simp[]) >>
    `step_inst fuel ctx inst s2 = step_inst_base inst s2` by
      (irule step_inst_non_invoke >> simp[]) >>
    gvs[] >>
    drule_all step_non_phi_exec_equiv >> strip_tac >>
    qexists_tac `r2` >> simp[])
QED

Theorem is_terminator_not_INVOKE[local]:
  !op. is_terminator op ==> op <> INVOKE
Proof
  Cases >> simp[is_terminator_def]
QED

(* Helper for run_block_non_phi_equiv: terminator case.
   When the current non-PHI instruction is a terminator, running one step
   on exec-equiv states gives state-equiv results. *)
Theorem run_block_non_phi_terminator_case[local]:
  !fuel ctx bb s1 s2 func inst s1'.
    fn_inst_wf func /\ MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst_wf inst /\
    inst.inst_opcode <> PHI /\
    is_terminator inst.inst_opcode /\
    execution_equiv (COMPL (set (fn_all_vars func))) s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    ~s1.vs_halted /\
    get_instruction bb s2.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s1 = OK s1' /\
    (if s1'.vs_halted then Halt s1' else OK s1') = OK v1 ==>
    ?v2. exec_block fuel ctx bb s2 = OK v2 /\
         state_equiv (COMPL (set (fn_all_vars func))) v1 v2
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (imp_res_tac is_terminator_not_INVOKE >> simp[]) >>
  (`step_inst_base inst s1 = OK s1'` by
    (mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s1`] step_inst_non_invoke) >>
     simp[])) >>
  mp_tac (Q.SPECL [`inst`, `s1`, `s2`, `func`, `bb`, `s1'`]
    step_non_phi_exec_equiv) >>
  simp[] >> strip_tac >>
  (`step_inst fuel ctx inst s2 = step_inst_base inst s2` by
    (irule step_inst_non_invoke >> simp[])) >>
  `~s1'.vs_halted` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     Cases_on `s1'.vs_halted` >> simp[]) >>
  fs[] >> rpt BasicProvers.VAR_EQ_TAC >>
  CONV_TAC (ONCE_REWRITE_CONV [exec_block_def]) >>
  simp[] >>
  qexists_tac `r2` >> simp[] >>
  fs[state_equiv_def, execution_equiv_def]
QED

(* If all remaining instructions are non-PHI and two states agree on
   everything except vs_prev_bb (and vars outside fn_all_vars), then
   exec_block produces state_equiv results. Non-PHI non-terminators are
   prev_bb-independent; jump terminators overwrite prev_bb to the same
   value (SOME current_bb which agrees). *)
(* Inductive step for run_block_non_phi_equiv: handles one instruction.
   Takes the IH as a hypothesis. *)
(* Two execution-equiv states running the same non-PHI block produce state_equiv results.
   Direct induction on instruction count remaining. *)
Theorem run_block_non_phi_equiv[local]:
  !fuel ctx bb s1 s2 func v1.
    fn_inst_wf func /\
    bb_well_formed bb /\
    MEM bb func.fn_blocks /\
    execution_equiv (COMPL (set (fn_all_vars func))) s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    ~s1.vs_halted /\
    (!k. s1.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
         (EL k bb.bb_instructions).inst_opcode <> PHI) /\
    exec_block fuel ctx bb s1 = OK v1 ==>
    ?v2. exec_block fuel ctx bb s2 = OK v2 /\
         state_equiv (COMPL (set (fn_all_vars func))) v1 v2
Proof
  rpt gen_tac >> strip_tac >>
  (* Put state-dependent hypotheses back as implications for generalization *)
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  qpat_x_assum `!k. _` mp_tac >>
  qpat_x_assum `~_.vs_halted` mp_tac >>
  qpat_x_assum `_.vs_inst_idx = _.vs_inst_idx` mp_tac >>
  qpat_x_assum `_.vs_current_bb = _.vs_current_bb` mp_tac >>
  qpat_x_assum `execution_equiv _ _ _` mp_tac >>
  MAP_EVERY qid_spec_tac [`v1`, `s2`, `s1`] >>
  completeInduct_on `LENGTH bb.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ s1 = _` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s1` >> simp[] >>
  rename1 `OK s1'` >>
  (* Shared setup: establish facts about inst *)
  (`s1.vs_inst_idx < LENGTH bb.bb_instructions` by
    fs[get_instruction_def, AllCaseEqs()]) >>
  (`inst.inst_opcode <> PHI` by (
    first_x_assum (qspec_then `s1.vs_inst_idx` mp_tac) >>
    fs[get_instruction_def])) >>
  (`MEM inst bb.bb_instructions` by (
    fs[get_instruction_def, AllCaseEqs(), listTheory.MEM_EL] >>
    metis_tac[])) >>
  (`inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[])) >>
  (`get_instruction bb s2.vs_inst_idx = SOME inst` by gvs[]) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    simp[] >> strip_tac >>
    irule run_block_non_phi_terminator_case >>
    simp[] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  drule_all step_inst_non_phi_non_term_exec_equiv >> strip_tac >>
  rename1 `step_inst fuel ctx inst s2 = OK r2` >>
  CONV_TAC (ONCE_REWRITE_CONV [exec_block_def]) >>
  ASM_REWRITE_TAC[] >> simp[] >>
  (* Apply IH to get exec_block on r2's continuation *)
  first_x_assum irule >> simp[] >>
  qexists_tac `s1' with vs_inst_idx := SUC s2.vs_inst_idx` >>
  simp[] >> fs[execution_equiv_def, lookup_var_def]
QED
(* If a non-PHI instruction is at position i in a well-formed block,
   all instructions from i onward are non-PHI (PHIs form a prefix) *)
Theorem bb_non_phi_suffix[local]:
  !bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> PHI ==>
    !k. i <= k /\ k < LENGTH bb.bb_instructions ==>
      (EL k bb.bb_instructions).inst_opcode <> PHI
Proof
  rw[bb_well_formed_def] >>
  CCONTR_TAC >> gvs[] >>
  `i < k \/ i = k` by simp[] >> gvs[] >>
  metis_tac[]
QED

(* Once we reach a non-PHI instruction, update_phis_for_split doesn't change
   the remaining block, so exec_block gives the same result *)
Theorem run_block_update_phis_non_phi_suffix[local]:
  !fuel ctx bb s old_lbl new_lbl var_repls.
    bb_well_formed bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI ==>
    exec_block fuel ctx
      (update_phis_for_split old_lbl new_lbl var_repls bb) s =
    exec_block fuel ctx bb s
Proof
  rpt strip_tac >>
  irule run_block_same_suffix >>
  simp[update_phis_for_split_length] >>
  rpt strip_tac >>
  irule update_phis_for_split_non_phi >>
  simp[] >>
  drule_all bb_non_phi_suffix >> simp[]
QED

(* When starting from phi_prefix_length, update_phis_for_split preserves exec_block.
   This wraps run_block_update_phis_non_phi_suffix with the specific starting index. *)
Theorem exec_block_update_phis_from_ppl[local]:
  !fuel ctx bb s old_lbl new_lbl var_repls.
    bb_well_formed bb ==>
    exec_block fuel ctx (update_phis_for_split old_lbl new_lbl var_repls bb)
      (s with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
    exec_block fuel ctx bb
      (s with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions`
    by metis_tac[bb_well_formed_phi_prefix_length_lt] >>
  `(EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions).inst_opcode <> PHI`
    by metis_tac[phi_prefix_length_at_nonphi] >>
  irule run_block_update_phis_non_phi_suffix >>
  simp[]
QED

(* Same as exec_block_update_phis_from_ppl but uses the updated block's
   phi_prefix_length on both sides. This matches goal shapes where the
   index is written as phi_prefix_length (update_phis_for_split ... bb).bb_instructions *)
Theorem exec_block_update_phis_from_ppl_alt[local]:
  !fuel ctx bb s old_lbl new_lbl var_repls.
    bb_well_formed bb ==>
    exec_block fuel ctx (update_phis_for_split old_lbl new_lbl var_repls bb)
      (s with vs_inst_idx := phi_prefix_length
           (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions) =
    exec_block fuel ctx bb
      (s with vs_inst_idx := phi_prefix_length
           (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions)
Proof
  rpt strip_tac >>
  `phi_prefix_length (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions =
    phi_prefix_length bb.bb_instructions`
    by simp[phi_prefix_length_update_phis_for_split_eq] >>
  simp[exec_block_update_phis_from_ppl]
QED

(* Extract phi_well_formed from inst_wf when opcode is PHI.
   Avoids expanding the 90+ case inst_wf_def inline in proofs *)
Theorem inst_wf_phi_well_formed:
  !inst. inst.inst_opcode = PHI /\ inst_wf inst ==>
    phi_well_formed inst.inst_operands /\ LENGTH inst.inst_outputs = 1
Proof
  rpt strip_tac >> gvs[inst_wf_def]
QED

(* Helper: ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l *)
Theorem all_distinct_flat_mem[local]:
  !ls l. ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  fs[listTheory.ALL_DISTINCT_APPEND]
QED

(* Instructions in a block with distinct inst_ids are distinct at distinct positions *)
Theorem wf_block_distinct_insts[local]:
  !bb i j.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
    EL i bb.bb_instructions = EL j bb.bb_instructions ==> i = j
Proof
  rpt strip_tac >>
  `(EL i bb.bb_instructions).inst_id =
   (EL j bb.bb_instructions).inst_id` by simp[] >>
  CCONTR_TAC >>
  metis_tac[listTheory.ALL_DISTINCT_EL_IMP, listTheory.LENGTH_MAP,
            listTheory.EL_MAP]
QED
(* Helper: in a well-formed block, if instruction k is PHI and vs_inst_idx <= k,
   then the instruction at vs_inst_idx is also PHI (PHIs form a prefix). *)
Theorem inst_at_idx_is_phi[local]:
  !bb k s.
    bb_well_formed bb /\
    s.vs_inst_idx <= k /\
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode = PHI ==>
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = PHI
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  mp_tac phi_before_non_phi >>
  disch_then (qspecl_then [`bb`, `k`, `s.vs_inst_idx`] mp_tac) >>
  simp[] >> fs[arithmeticTheory.NOT_LESS]
QED

(* step_inst on PHI always returns Error *)
Theorem step_inst_phi_error[local]:
  !fuel ctx inst s.
    inst.inst_opcode = PHI /\ inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst s = Error "phi outside prefix"
Proof
  rpt strip_tac >>
  simp[step_inst_non_invoke] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >> simp[]
QED

(* If the first instruction of exec_block causes step_inst Error, exec_block returns Error *)
Theorem exec_block_first_step_error[local]:
  !fuel ctx bb s inst e.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = Error e ==>
    ?e'. exec_block fuel ctx bb s = Error e'
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >> simp[]
QED

(* Generalized: if exec_block does NOT return Error, PHI vars are in FDOM.
   After parallel PHI semantics change, this theorem is vacuously true:
   step_inst_base PHI = Error, so exec_block from any PHI index returns Error,
   contradicting the non-Error hypothesis. *)
Theorem run_block_non_error_phi_var_defined_gen[local]:
  !n fuel ctx bb s func pred_lbl inst vn k.
    n = k - s.vs_inst_idx /\
    (!e. exec_block fuel ctx bb s <> Error e) /\
    s.vs_inst_idx <= k /\
    k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst /\
    s.vs_prev_bb = SOME pred_lbl /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    fn_inst_wf func /\ fn_phi_labels_distinct func /\
    fn_phis_non_interfering func /\
    MEM bb func.fn_blocks /\
    bb_well_formed bb /\
    inst.inst_opcode = PHI /\
    resolve_phi pred_lbl inst.inst_operands = SOME (Var vn) ==>
    vn IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  (* The instruction at vs_inst_idx is PHI (PHIs form a prefix) *)
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[inst_at_idx_is_phi] >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE` by simp[] >>
  `inst_wf (EL s.vs_inst_idx bb.bb_instructions)` by (
    fs[fn_inst_wf_def] >>
    first_x_assum (qspec_then `bb` mp_tac) >> simp[] >>
    disch_then (qspec_then `EL s.vs_inst_idx bb.bb_instructions` mp_tac) >>
    simp[listTheory.MEM_EL] >> disch_then match_mp_tac >>
    qexists_tac `s.vs_inst_idx` >> simp[]) >>
  `get_instruction bb s.vs_inst_idx =
   SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def] >>
  (* step_inst on PHI = Error, so exec_block = Error, contradicting hypothesis *)
  `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s =
   Error "phi outside prefix"` by
    metis_tac[step_inst_phi_error] >>
  metis_tac[exec_block_first_step_error]
QED

(* Boundary lemma: removing a PHI from the front of a well-formed instruction
   list preserves well-formedness. *)
Theorem bb_well_formed_cons_phi_tail[local]:
  !h insts lbl.
    bb_well_formed <|bb_label := lbl; bb_instructions := h::insts|> /\
    h.inst_opcode = PHI ==>
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|>
Proof
  rw[bb_well_formed_def]
  >- (Cases_on `insts` >> gvs[is_terminator_def, listTheory.LAST_DEF])
  >- (Cases_on `insts` >> gvs[is_terminator_def, listTheory.LAST_DEF])
  >- (last_x_assum (qspec_then `SUC i` mp_tac) >>
      simp[rich_listTheory.EL_CONS])
  >- (qpat_x_assum `!i j. _` (qspec_then `SUC i` (qspec_then `SUC j` mp_tac)) >>
      simp[rich_listTheory.EL_CONS])
QED

(* Boundary lemma: in a well-formed block, a non-PHI at index 0
   implies no PHI at any later index *)
Theorem bb_well_formed_no_late_phi[local]:
  !h insts lbl j.
    bb_well_formed <|bb_label := lbl; bb_instructions := h::insts|> /\
    h.inst_opcode <> PHI /\
    j < LENGTH insts /\
    (EL j insts).inst_opcode = PHI ==>
    F
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  first_x_assum (qspec_then `0` (qspec_then `SUC j` mp_tac)) >>
  simp[rich_listTheory.EL_CONS]
QED

(* Bridge: bb_well_formed depends only on bb_instructions, not bb_label *)
Theorem bb_well_formed_same_instrs[local]:
  !bb. bb_well_formed bb ==>
    bb_well_formed <|bb_label := ""; bb_instructions := bb.bb_instructions|>
Proof
  rw[bb_well_formed_def]
QED

(* If eval_phis succeeds on a well-formed block's instructions,
   every PHI in the list has eval_one_phi succeed *)
Theorem eval_phis_OK_eval_one_phi_SOME[local]:
  !s insts s' inst.
    eval_phis s insts = OK s' /\
    bb_well_formed <| bb_label := ""; bb_instructions := insts |> /\
    MEM inst insts /\ inst.inst_opcode = PHI ==>
    ?out v. eval_one_phi s inst = SOME (out, v)
Proof
  Induct_on `insts`
  >- simp[]
  >> rpt strip_tac >> fs[eval_phis_def]
  >> Cases_on `h.inst_opcode = PHI` >> gvs[AllCaseEqs()]
  >- (first_x_assum irule >> simp[] >>
      drule bb_well_formed_cons_phi_tail >> simp[])
  >> `?j. j < LENGTH insts /\ EL j insts = inst` by metis_tac[listTheory.MEM_EL] >>
    metis_tac[bb_well_formed_no_late_phi]
QED

(* run_block_entry-level bridge: if run_block_entry doesn't error, then
   phi_fwd_vars are in FDOM s.vs_vars (via eval_phis success) *)
Theorem run_block_entry_non_error_phi_fwd_vars_defined[local]:
  !fuel ctx bb s func pred_lbl pred_bb var.
    (!e. run_block_entry fuel ctx bb s <> Error e) /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = SOME pred_lbl /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    bb_well_formed bb /\
    fn_inst_wf func /\ fn_phi_labels_distinct func /\
    fn_phis_non_interfering func /\
    MEM bb func.fn_blocks /\
    MEM var (phi_vars_needing_forward pred_lbl pred_bb bb.bb_instructions) ==>
    var IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_distinct]
  >- (rename [`eval_phis s bb.bb_instructions = OK s_phi`] >>
      imp_res_tac bb_well_formed_same_instrs >>
      mp_tac (Q.SPECL [`pred_lbl`, `pred_bb`, `bb.bb_instructions`, `var`,
                        `func`, `bb`] phi_vars_resolve_phi_full) >>
      simp[] >> strip_tac >>
      drule eval_phis_OK_eval_one_phi_SOME >> simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`inst'`] mp_tac) >> simp[] >> strip_tac >>
      gvs[eval_one_phi_def, AllCaseEqs()] >>
      gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF]) >>
  drule run_block_entry_eval_phis_Error >> metis_tac[]
QED
Theorem run_block_non_error_phi_fwd_vars_defined[local]:
  !fuel ctx bb s func pred_lbl pred_bb var.
    (!e. exec_block fuel ctx bb s <> Error e) /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = SOME pred_lbl /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    bb_well_formed bb /\
    fn_inst_wf func /\ fn_phi_labels_distinct func /\
    fn_phis_non_interfering func /\
    MEM bb func.fn_blocks /\
    MEM var (phi_vars_needing_forward pred_lbl pred_bb bb.bb_instructions) ==>
    var IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`pred_lbl`, `pred_bb`, `bb.bb_instructions`, `var`,
                    `func`, `bb`] phi_vars_resolve_phi_full) >>
  simp[] >> strip_tac >>
  `?k. k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst'` by
    metis_tac[listTheory.MEM_EL] >>
  mp_tac (Q.SPECL [`k`, `fuel`, `ctx`, `bb`, `s`, `func`, `pred_lbl`,
                    `inst'`, `var`, `k`] run_block_non_error_phi_var_defined_gen) >>
  simp[]
QED

(* update_var with same var/val on both sides preserves execution_equiv,
   provided the variable is NOT in the equiv set (i.e., it IS a function var) *)
Theorem update_var_preserves_execution_equiv[local]:
  !vars x v s1 s2.
    execution_equiv vars s1 s2 /\ x NOTIN vars ==>
    execution_equiv vars (update_var x v s1) (update_var x v s2)
Proof
  rw[execution_equiv_def, update_var_def, FLOOKUP_UPDATE, lookup_var_def]
QED

(* Forwarding invariant is maintained after update_var out val on both sides,
   given: (1) new_v's are not in fn_all_vars (so new_v <> out),
   (2) fn_phis_non_interfering prevents orig = out for different PHIs,
   (3) if orig = out for same PHI, val = FLOOKUP sa.vs_vars orig anyway *)
Theorem forwarding_preserved_by_update_var[local]:
  !var_repls sa sb out val func bb inst pred_lbl v.
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP sb.vs_vars new_v = FLOOKUP sa.vs_vars orig) ==>
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       ~MEM new_v (fn_all_vars func)) ==>
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       ?inst'. MEM inst' bb.bb_instructions /\ inst'.inst_opcode = PHI /\
         resolve_phi pred_lbl inst'.inst_operands = SOME (Var orig)) ==>
    fn_phis_non_interfering func ==>
    MEM bb func.fn_blocks ==>
    MEM inst bb.bb_instructions ==> inst.inst_opcode = PHI ==>
    MEM out inst.inst_outputs ==>
    resolve_phi pred_lbl inst.inst_operands = SOME (Var val) ==>
    FLOOKUP sa.vs_vars val = SOME v ==>
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP (update_var out v sb).vs_vars new_v =
       FLOOKUP (update_var out v sa).vs_vars orig)
Proof
  rpt strip_tac >>
  simp[update_var_def, FLOOKUP_UPDATE] >>
  (* new_v <> out because new_v not in fn_all_vars but out is *)
  (`out <> new_v` by (
    strip_tac >> gvs[] >>
    `MEM new_v (fn_all_vars func)` by (
      irule inst_output_in_fn_all_vars >>
      qexistsl_tac [`bb`, `inst`] >> simp[]) >>
    res_tac >> fs[])) >>
  simp[] >>
  (* Get forwarding fact and inst' witness using explicit instantiation *)
  (`FLOOKUP sb.vs_vars new_v = FLOOKUP sa.vs_vars orig` by res_tac) >>
  (`?inst'. MEM inst' bb.bb_instructions /\ inst'.inst_opcode = PHI /\
     resolve_phi pred_lbl inst'.inst_operands = SOME (Var orig)` by
    (first_x_assum (qspecl_then [`orig`, `new_v`] mp_tac) >> simp[])) >>
  Cases_on `out = orig` >> fs[]
  >- (
    (* Need: FLOOKUP sa.vs_vars orig = SOME v
       inst' resolves orig; if inst'=inst then orig=val; else contradiction *)
    Cases_on `inst' = inst`
    >- (
      (* inst' = inst: two resolve_phi give orig = val *)
      fs[])
    >- (
      (* inst' <> inst: fn_phis_non_interfering gives orig <> orig *)
      metis_tac[fn_phis_non_interfering_def]))
QED

(* Same as above but with update_var expanded in conclusion *)
Theorem forwarding_preserved_by_fupdate[local]:
  !var_repls sa sb out val func bb inst pred_lbl v.
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP sb.vs_vars new_v = FLOOKUP sa.vs_vars orig) ==>
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       ~MEM new_v (fn_all_vars func)) ==>
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       ?inst'. MEM inst' bb.bb_instructions /\ inst'.inst_opcode = PHI /\
         resolve_phi pred_lbl inst'.inst_operands = SOME (Var orig)) ==>
    fn_phis_non_interfering func ==>
    MEM bb func.fn_blocks ==>
    MEM inst bb.bb_instructions ==> inst.inst_opcode = PHI ==>
    MEM out inst.inst_outputs ==>
    resolve_phi pred_lbl inst.inst_operands = SOME (Var val) ==>
    FLOOKUP sa.vs_vars val = SOME v ==>
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP (sb.vs_vars |+ (out, v)) new_v =
       FLOOKUP (sa.vs_vars |+ (out, v)) orig)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`var_repls`, `sa`, `sb`, `out`, `val`, `func`,
    `bb`, `inst`, `pred_lbl`, `v`] forwarding_preserved_by_update_var) >>
  rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  disch_then (qspecl_then [`orig`, `new_v`] mp_tac) >>
  simp[update_var_def]
QED

(* eval_operands doesn't read vs_prev_bb *)
Theorem eval_operands_prev_bb[local]:
  !ops s p. eval_operands ops (s with vs_prev_bb := p) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >>
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

(* INVOKE step_inst: full prev_bb characterization.
   For ALL result types, step_inst on (s with vs_prev_bb := p) either
   equals step_inst on s (non-OK) or maps vs_prev_bb (OK). *)
Theorem step_inst_invoke_prev_bb[local]:
  !fuel ctx inst s p.
    inst.inst_opcode = INVOKE ==>
    (case step_inst fuel ctx inst s of
       OK r => step_inst fuel ctx inst (s with vs_prev_bb := p) =
               OK (r with vs_prev_bb := p)
     | Halt v => step_inst fuel ctx inst (s with vs_prev_bb := p) = Halt v
     | Abort a v => step_inst fuel ctx inst (s with vs_prev_bb := p) =
                    Abort a v
     | IntRet l v => step_inst fuel ctx inst (s with vs_prev_bb := p) =
                     IntRet l v
     | Error e => step_inst fuel ctx inst (s with vs_prev_bb := p) = Error e)
Proof
  rpt strip_tac >>
  simp[step_inst_def, eval_operands_prev_bb] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands x1 s` >> simp[] >>
  simp[setup_callee_def] >>
  Cases_on `NULL x.fn_blocks` >> simp[] >>
  Cases_on `NULL x'` >> simp[] >>
  Cases_on `run_blocks fuel ctx x
    (s with <|vs_vars := FEMPTY; vs_prev_bb := NONE;
      vs_current_bb := (HD x.fn_blocks).bb_label;
      vs_inst_idx := 0; vs_halted := F; vs_params := x';
      vs_fmp := s.vs_fmp; vs_call_entry_fmp := s.vs_fmp;
      vs_return_pc_token := LAST x'; vs_allocas := FEMPTY|>)` >>
  simp[merge_callee_state_def, bind_outputs_def] >>
  Cases_on `LENGTH inst.inst_outputs = LENGTH i.iret_values` >> simp[] >>
  (`s with <|vs_memory := v.vs_memory; vs_transient := v.vs_transient;
     vs_prev_bb := p; vs_returndata := v.vs_returndata;
     vs_accounts := v.vs_accounts; vs_logs := v.vs_logs;
     vs_immutables := v.vs_immutables; vs_alloca_next := v.vs_alloca_next|> =
   (s with <|vs_memory := v.vs_memory; vs_transient := v.vs_transient;
     vs_returndata := v.vs_returndata; vs_accounts := v.vs_accounts;
     vs_logs := v.vs_logs; vs_immutables := v.vs_immutables;
     vs_alloca_next := v.vs_alloca_next|>) with vs_prev_bb := p`
    by simp[venomStateTheory.venom_state_component_equality]) >>
  pop_assum (fn eq => REWRITE_TAC[eq]) >>
  simp[adopt_return_fmp_prev_bb, foldl_update_var_prev_bb]
QED

(* eval_operand doesn't read vs_prev_bb (single operand version) *)
Theorem eval_operand_prev_bb[local]:
  !op s p. eval_operand op (s with vs_prev_bb := p) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem mcopy_prev_bb[local]:
  !dst src sz s p.
    mcopy dst src sz (s with vs_prev_bb := p) =
    (mcopy dst src sz s) with vs_prev_bb := p
Proof
  simp[mcopy_def, write_memory_with_expansion_def,
       venom_state_component_equality]
QED

Theorem pack_dret_dynamic_prev_bb[local]:
  !pairs cursor s ptrs final_cursor s' p.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,s') ==>
    pack_dret_dynamic cursor pairs (s with vs_prev_bb := p) =
      (ptrs,final_cursor,s' with vs_prev_bb := p)
Proof
  Induct
  >- simp[pack_dret_dynamic_def]
  >> rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  Cases_on `pack_dret_dynamic (cursor + n2w (ceil32 (w2n h1))) pairs
              (mcopy (w2n cursor) (w2n h0) (w2n h1) s)` >>
  Cases_on `r` >>
  gvs[pack_dret_dynamic_def, mcopy_prev_bb] >>
  first_x_assum drule >>
  disch_then (fn th => rewrite_tac[th]) >> simp[]
QED

Theorem pack_dret_dynamic_prev_bb_eq[local]:
  !pairs cursor s p.
    pack_dret_dynamic cursor pairs (s with vs_prev_bb := p) =
      case pack_dret_dynamic cursor pairs s of
        (ptrs,final_cursor,s') =>
          (ptrs,final_cursor,s' with vs_prev_bb := p)
Proof
  rpt gen_tac >>
  Cases_on `pack_dret_dynamic cursor pairs s` >>
  Cases_on `r` >>
  gvs[] >>
  irule pack_dret_dynamic_prev_bb >>
  simp[]
QED

val nonjump_term_prev_bb_tac =
  simp[step_inst_base_def, eval_operand_prev_bb,
       eval_operands_prev_bb, halt_state_def, revert_state_def,
       set_returndata_def, exec_result_map_prev_bb_def,
       read_memory_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[exec_result_map_prev_bb_def,
       venomStateTheory.venom_state_component_equality];


val dret_prev_bb_tac =
  simp[step_inst_base_def, eval_operand_prev_bb,
       eval_operands_prev_bb, halt_state_def, revert_state_def,
       set_returndata_def, exec_result_map_prev_bb_def,
       read_memory_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[pack_dret_dynamic_prev_bb_eq, exec_result_map_prev_bb_def,
      venomStateTheory.venom_state_component_equality];
Triviality step_inst_base_non_jump_terminator_prev_bb:
  !inst (s:venom_state) p.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (step_inst_base inst s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  TRY (rename1 `inst.inst_opcode = DRET` >> dret_prev_bb_tac) >>
  TRY (rename1 `inst.inst_opcode = RET` >> nonjump_term_prev_bb_tac) >>
  TRY (rename1 `inst.inst_opcode = RETFMP` >> nonjump_term_prev_bb_tac) >>
  TRY (rename1 `inst.inst_opcode = RETURN` >> nonjump_term_prev_bb_tac) >>
  TRY (rename1 `inst.inst_opcode = REVERT` >> nonjump_term_prev_bb_tac) >>
  TRY (rename1 `inst.inst_opcode = STOP` >> nonjump_term_prev_bb_tac) >>
  TRY (rename1 `inst.inst_opcode = SINK` >> nonjump_term_prev_bb_tac) >>
  TRY (rename1 `inst.inst_opcode = SELFDESTRUCT` >> nonjump_term_prev_bb_tac) >>
  TRY (rename1 `inst.inst_opcode = INVALID` >> nonjump_term_prev_bb_tac) >>
  dret_prev_bb_tac
QED

(* For non-PHI, non-JMP/JNZ/DJMP opcodes, step_inst_base commutes with
   vs_prev_bb via exec_result_map_prev_bb. Extends step_inst_base_prev_bb_indep
   to cover non-jump terminators (RET, RETURN, REVERT, STOP, SINK, etc.) *)
Theorem step_inst_base_non_jump_prev_bb[local]:
  !inst (s:venom_state) p.
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (step_inst_base inst s)
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_non_jump_terminator_prev_bb]
  >> irule step_inst_base_prev_bb_indep >> simp[]
QED

(* Narrowing: among terminators, only JMP/JNZ/DJMP produce OK non-halted *)
Theorem step_inst_base_ok_not_halted_is_jump[local]:
  !inst s res.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK res /\ ~res.vs_halted ==>
    inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
    inst.inst_opcode = DJMP
Proof
  metis_tac[step_inst_base_ok_terminator_jump]
QED

(* result_equiv is reflexive for any vars. Generalizes result_equiv_UNIV_refl. *)
Theorem result_equiv_refl[local]:
  !vars r. result_equiv vars r r
Proof
  gen_tac >> Cases >>
  simp[result_equiv_def, state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* execution_equiv ignores vs_prev_bb, so changing it preserves equiv. *)
Theorem execution_equiv_prev_bb[local]:
  !vars s p. execution_equiv vars s (s with vs_prev_bb := p)
Proof
  simp[execution_equiv_def, lookup_var_def]
QED

(* For non-PHI instruction blocks, changing vs_prev_bb preserves
   result_equiv for ANY vars. PHI is the only opcode reading vs_prev_bb,
   so removing it makes exec_block independent of vs_prev_bb up to
   result_equiv (which ignores vs_prev_bb in Halt/Abort/IntRet/Error,
   and the OK case only arises from terminators which reset vs_prev_bb). *)
Theorem run_block_non_phi_prev_bb_result_equiv[local]:
  !fuel ctx bb s p vars.
    (!k. s.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
         (EL k bb.bb_instructions).inst_opcode <> PHI) ==>
    result_equiv vars
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx bb (s with vs_prev_bb := p))
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >>
  simp[result_equiv_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  (* Extract idx < LENGTH and EL = inst from get_instruction *)
  qpat_x_assum `get_instruction _ _ = SOME _`
    (fn th => assume_tac (SIMP_RULE (srw_ss()) [get_instruction_def] th)) >>
  (* Derive inst.inst_opcode <> PHI: specialize at s.vs_inst_idx, then resolve *)
  Q.PAT_ASSUM `!k. _ ==> _ <> PHI`
    (fn th => assume_tac th >>
       mp_tac (Q.SPEC `s.vs_inst_idx` th)) >>
  (impl_tac >- fs[]) >>
  disch_then assume_tac >>
  (* Case 1: INVOKE *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `p`]
         step_inst_invoke_prev_bb) >>
    simp[] >>
    Cases_on `step_inst fuel ctx inst s` >>
    simp[result_equiv_def, is_terminator_def] >>
    TRY (strip_tac >> simp[execution_equiv_refl] >> NO_TAC) >>
    strip_tac >>
    Q.PAT_ASSUM `!y. _ ==> !s'. _`
      (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
    (impl_tac >- simp[arithmeticTheory.ADD1]) >>
    disch_then (qspec_then `v with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
    (impl_tac >- simp[]) >>
    (impl_tac >- (
      rpt strip_tac >>
      Q.PAT_ASSUM `!k. _ ==> _ <> PHI`
        (qspec_then `k` mp_tac) >>
      simp[]))
    >> simp[]
  )
  (* Non-INVOKE: rewrite step_inst to step_inst_base *)
  >> mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`] step_inst_non_invoke) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s with vs_prev_bb := p`] step_inst_non_invoke) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  (* Case 2: JMP/JNZ/DJMP — both sides identical *)
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/ inst.inst_opcode = DJMP`
  >- (
    mp_tac (Q.SPECL [`inst`, `s`, `p`] step_inst_base_jump_prev_bb) >>
    (impl_tac >- simp[]) >>
    disch_then (fn eq => REWRITE_TAC[eq]) >>
    simp[result_equiv_refl]
  )
  (* Case 3: Non-INVOKE, non-JMP/JNZ/DJMP — split conjunction, substitute inst *)
  >> qpat_x_assum `_ /\ _`
       (fn th => assume_tac (CONJUNCT1 th) >> assume_tac (CONJUNCT2 th)) >>
  qpat_x_assum `_ = inst` SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`inst`, `s`, `p`] step_inst_base_non_jump_prev_bb) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (fn eq => REWRITE_TAC[eq]) >>
  Cases_on `step_inst_base inst s` >>
  simp[exec_result_map_prev_bb_def, result_equiv_def] >>
  (* Non-OK: execution_equiv_prev_bb closes Halt/Abort/IntRet *)
  TRY (simp[execution_equiv_prev_bb] >> NO_TAC) >>
  (* OK case: case split on is_terminator *)
  rename1 `step_inst_base _ _ = OK s_base` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    (* Terminator OK: halted → Halt (exec_equiv_prev_bb), not_halted → contradiction *)
    Cases_on `s_base.vs_halted` >>
    simp[result_equiv_def, execution_equiv_prev_bb] >>
    mp_tac (Q.SPECL [`inst`, `s`, `s_base`] step_inst_base_ok_not_halted_is_jump) >>
    simp[]
  ) >>
  (* Non-terminator OK: IH closes via simp *)
  simp[]
QED

(* General: execution_equiv states on the same non-PHI block produce result_equiv
   results, even when vs_prev_bb differs. Subsumes run_block_non_phi_equiv
   and run_block_non_phi_terminator_case for ALL result types.
   Proof: chain prev_bb independence + run_block_preserves_R. *)
Theorem run_block_non_phi_result_equiv[local]:
  !fuel ctx bb s1 s2 func.
    fn_inst_wf func /\
    MEM bb func.fn_blocks /\
    execution_equiv (COMPL (set (fn_all_vars func))) s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!k. s1.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
         (EL k bb.bb_instructions).inst_opcode <> PHI) ==>
    result_equiv (COMPL (set (fn_all_vars func)))
      (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)
Proof
  rpt strip_tac >>
  (* Step 1: s1 -> s1 with s2's prev_bb: prev_bb independence *)
  irule (GEN_ALL stateEquivPropsTheory.result_equiv_trans) >>
  qexists_tac `exec_block fuel ctx bb (s1 with vs_prev_bb := s2.vs_prev_bb)` >>
  conj_tac
  >- (irule run_block_non_phi_prev_bb_result_equiv >> simp[]) >>
  (* Step 2: s1-with-s2's-prev_bb -> s2: state_equiv, use run_block_preserves_R *)
  mp_tac (Q.SPEC `COMPL (set (fn_all_vars func))`
    stateEquivPropsTheory.result_equiv_is_lift_result) >>
  disch_then (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  mp_tac (Q.SPECL [
    `state_equiv (COMPL (set (fn_all_vars func)))`,
    `execution_equiv (COMPL (set (fn_all_vars func)))`,
    `func`] execEquivParamPropsTheory.exec_block_preserves_R) >>
  (impl_tac >- (
    simp[execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel] >>
    rpt conj_tac
    >- metis_tac[stateEquivPropsTheory.state_equiv_trans]
    >- metis_tac[stateEquivPropsTheory.execution_equiv_trans]
    >- (
      rpt strip_tac >>
      fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
      first_x_assum match_mp_tac >>
      simp[pred_setTheory.IN_COMPL] >>
      irule inst_operand_var_in_fn_all_vars >>
      metis_tac[]))) >>
  strip_tac >>
  first_x_assum irule >> simp[] >>
  (* Show state_equiv between s1-with-prev_bb and s2 *)
  simp[state_equiv_def] >>
  fs[execution_equiv_def, lookup_var_def]
QED
(* run_block_update_phis_forwarded_full: for ALL result types.
   When exec_block on original bb returns ANY result, the updated block
   returns a result_equiv-related result. *)
Theorem run_block_update_phis_forwarded_full[local]:
  !fuel ctx bb s1 s2 pred_lbl split_lbl var_repls func.
    wf_function_no_ids func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    ~MEM split_lbl (fn_labels func) /\
    fn_inst_wf func /\
    MEM bb func.fn_blocks /\
    ~s1.vs_halted /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_current_bb = s2.vs_current_bb /\
    execution_equiv (COMPL (set (fn_all_vars func))) s1 s2 /\
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig) /\
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       ~MEM new_v (fn_all_vars func)) /\
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       ?inst'. MEM inst' bb.bb_instructions /\ inst'.inst_opcode = PHI /\
         resolve_phi pred_lbl inst'.inst_operands = SOME (Var orig)) ==>
    result_equiv (COMPL (set (fn_all_vars func)))
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx
         (update_phis_for_split pred_lbl split_lbl var_repls bb) s2)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `execution_equiv _ _ _` mp_tac >>
  qpat_x_assum `~s1.vs_halted` mp_tac >>
  qpat_x_assum `s1.vs_inst_idx = _` mp_tac >>
  qpat_x_assum `s1.vs_current_bb = _` mp_tac >>
  qpat_x_assum `!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
     FLOOKUP s2.vs_vars new_v = _` mp_tac >>
  qpat_x_assum `s1.vs_prev_bb = _` mp_tac >>
  qpat_x_assum `s2.vs_prev_bb = _` mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`] >>
  completeInduct_on `LENGTH bb.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >>
  rename1 `execution_equiv _ sa sb` >>
  (* === Base case: no more instructions === *)
  Cases_on `get_instruction bb sa.vs_inst_idx`
  >- (
    sg `~(sa.vs_inst_idx < LENGTH bb.bb_instructions)`
    >- (qpat_x_assum `get_instruction _ _ = NONE`
          (fn th => assume_tac (SIMP_RULE (srw_ss()) [get_instruction_def] th)) >>
        simp[]) >>
    sg `get_instruction (update_phis_for_split pred_lbl split_lbl var_repls bb)
       sb.vs_inst_idx = NONE`
    >- (simp[get_instruction_def, update_phis_for_split_length]) >>
    PURE_ONCE_REWRITE_TAC[exec_block_def] >>
    simp[result_equiv_def])
  >> rename1 `SOME inst` >>
  (* === Common setup for SOME inst case === *)
  sg `sa.vs_inst_idx < LENGTH bb.bb_instructions`
  >- (qpat_x_assum `get_instruction _ _ = SOME _`
        (fn th => assume_tac (SIMP_RULE (srw_ss()) [get_instruction_def, AllCaseEqs()] th)) >>
      simp[]) >>
  sg `MEM inst bb.bb_instructions`
  >- (simp[listTheory.MEM_EL] >> qexists_tac `sa.vs_inst_idx` >>
      qpat_x_assum `get_instruction _ _ = SOME _`
        (fn th => assume_tac (SIMP_RULE (srw_ss()) [get_instruction_def, AllCaseEqs()] th)) >>
      simp[]) >>
  sg `inst_wf inst`
  >- (qpat_x_assum `fn_inst_wf func` (fn th =>
        mp_tac (REWRITE_RULE [fn_inst_wf_def] th)) >>
      disch_then (qspecl_then [`bb`, `inst`] mp_tac) >> simp[]) >>
  sg `bb_well_formed bb`
  >- (qpat_x_assum `wf_function_no_ids func` (fn th =>
        mp_tac (REWRITE_RULE [wf_function_no_ids_def] th)) >>
      simp[listTheory.EVERY_MEM]) >>
  sg `EL sb.vs_inst_idx bb.bb_instructions = inst`
  >- (qpat_assum `get_instruction _ _ = SOME _`
        (fn th => mp_tac (SIMP_RULE (srw_ss()) [get_instruction_def, AllCaseEqs()] th)) >>
      simp[]) >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    (* === PHI case: step_inst_base PHI always returns Error "phi outside prefix".
         Both exec_blocks return Error. result_equiv vars (Error e1) (Error e2) = T.
         After parallel PHI change, PHI in step_inst_base always errors
         regardless of state, so we don't need any forwarding lemmas. === *)
    `step_inst fuel ctx inst sa = Error "phi outside prefix"`
      by (irule step_inst_phi_error >> simp[]) >>
    `?e1. exec_block fuel ctx bb sa = Error e1`
      by metis_tac[exec_block_first_step_error] >>
    `get_instruction (update_phis_for_split pred_lbl split_lbl var_repls bb)
         sb.vs_inst_idx = SOME
      (inst with inst_operands :=
         update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands)`
      by (simp[get_instruction_def, update_phis_for_split_def,
           listTheory.EL_MAP, update_phis_for_split_length]) >>
    `(inst with inst_operands :=
         update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands).inst_opcode = PHI`
      by simp[] >>
    `step_inst fuel ctx
      (inst with inst_operands :=
         update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) sb =
      Error "phi outside prefix"`
      by (irule step_inst_phi_error >> simp[]) >>
    `?e2. exec_block fuel ctx
      (update_phis_for_split pred_lbl split_lbl var_repls bb) sb = Error e2`
      by metis_tac[exec_block_first_step_error] >>
    simp[result_equiv_def])
  >> (
    (* === Non-PHI case === *)
    sg `(EL sa.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI`
    >- simp[] >>
    sg `exec_block fuel ctx
         (update_phis_for_split pred_lbl split_lbl var_repls bb) sb =
       exec_block fuel ctx bb sb`
    >- (irule run_block_update_phis_non_phi_suffix >> simp[]) >>
    pop_assum (fn eq => REWRITE_TAC[eq]) >>
    irule run_block_non_phi_result_equiv >>
    simp[] >> rpt strip_tac >>
    mp_tac (Q.SPECL [`bb`, `sa.vs_inst_idx`] bb_non_phi_suffix) >>
    impl_tac >- simp[] >>
    disch_then (qspec_then `k` mp_tac) >> simp[])
QED
(* One step of insert_split simulation for target_bb *)
Theorem insert_split_target_step[local]:
  !func pred_bb target_bb id_base func' split_lbl n ctx s cur_bb.
    wf_function_no_ids func /\
    fn_inst_wf func /\
    ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    s.vs_current_bb = target_bb.bb_label /\
    s.vs_current_bb <> pred_bb.bb_label /\
    s.vs_prev_bb <> SOME pred_bb.bb_label /\
    s.vs_prev_bb <> SOME split_lbl /\
    s.vs_inst_idx = 0 /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME cur_bb /\
    s.vs_labels = FEMPTY /\
    (!ctx' s'.
       ~s'.vs_halted /\
       s'.vs_current_bb <> split_lbl /\
       s'.vs_inst_idx = 0 /\
       s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <> SOME split_lbl) ==>
      ?fuel'. fuel' >= n /\
        result_equiv UNIV (run_blocks n ctx' func s')
                          (run_blocks fuel' ctx' func' s')) ==>
    ?fuel'. fuel' >= SUC n /\
      result_equiv UNIV (run_blocks (SUC n) ctx func s)
                        (run_blocks fuel' ctx func' s)
Proof
  rpt strip_tac >>
  qpat_x_assum `func' = _` SUBST_ALL_TAC >>
  qpat_x_assum `split_lbl = _` SUBST_ALL_TAC >>
  (* lookup in func': update_phis_for_split applied to target_bb *)
  `?split_bb var_repls.
     lookup_block target_bb.bb_label
       (insert_split func pred_bb target_bb id_base).fn_blocks =
     SOME (update_phis_for_split pred_bb.bb_label split_bb.bb_label
             var_repls target_bb) /\
     split_bb.bb_label = split_block_name pred_bb.bb_label target_bb.bb_label` by
    (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
               lookup_insert_split_target) >>
     simp[] >> metis_tac[]) >>
  (* run_block on updated target_bb = run_block on original target_bb
     since s.vs_prev_bb doesn't match pred_bb or split_bb labels *)
  `!fuel2. run_block fuel2 ctx
      (update_phis_for_split pred_bb.bb_label split_bb.bb_label
        var_repls target_bb) s =
     run_block fuel2 ctx target_bb s` by (
    gen_tac >> irule run_block_update_phis_for_split_target >>
    Cases_on `s.vs_prev_bb` >> simp[] >> metis_tac[]) >>

  `lookup_block target_bb.bb_label func.fn_blocks = SOME target_bb` by
    metis_tac[MEM_lookup_block, fn_labels_def] >>
  `cur_bb = target_bb` by (
    `SOME cur_bb = SOME target_bb` by metis_tac[] >> fs[]) >>
  pop_assum SUBST_ALL_TAC >>
  (* Unfold LHS run_blocks (SUC n) using run_blocks_unfold *)
  ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[Excl "run_block_def"] >>
  qpat_x_assum `split_bb.bb_label = _` SUBST_ALL_TAC >>
  Cases_on `run_block_entry n ctx target_bb s` >> fs[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >>
  (* Non-OK cases: both sides produce the same result *)
  TRY (qexists_tac `SUC n` >> ONCE_REWRITE_TAC[run_blocks_unfold] >>
       simp[result_equiv_UNIV_refl] >> NO_TAC) >>
  (* Only OK case remains *)
  rename1 `OK v` >>
  Cases_on `v.vs_halted` >> fs[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >>
  TRY (qexists_tac `SUC n` >> ONCE_REWRITE_TAC[run_blocks_unfold] >>
       simp[result_equiv_UNIV_refl] >> NO_TAC) >>
  `v.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
  `v.vs_current_bb <> split_block_name pred_bb.bb_label target_bb.bb_label /\
   (v.vs_current_bb = target_bb.bb_label ==>
    v.vs_prev_bb <> SOME pred_bb.bb_label /\
    v.vs_prev_bb <> SOME (split_block_name pred_bb.bb_label target_bb.bb_label))` by
    (mp_tac insert_split_ih_maintained >>
     disch_then (qspecl_then [`func`, `pred_bb`, `target_bb`,
       `split_block_name pred_bb.bb_label target_bb.bb_label`,
       `n`, `ctx`, `target_bb`, `s`, `v`] mp_tac) >>
       simp[Excl "run_block_def"] >> metis_tac[MEM_lookup_block, fn_labels_def]) >>
  `v.vs_labels = FEMPTY` by (
    imp_res_tac venomExecPropsTheory.run_block_preserves_labels >> fs[Excl "run_block_def"]) >>
  first_x_assum (qspecl_then [`ctx`, `v`] mp_tac) >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >>
  strip_tac >>
  rename [`result_equiv _ _ (run_blocks fuel2 _ _ _)`] >>
  `run_block_entry fuel2 ctx target_bb s = OK v` by (
    drule venomExecPropsTheory.run_block_fuel_mono_OK >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >>
  qexists_tac `SUC fuel2` >> conj_tac >- simp[] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[Excl "run_block_def"]
QED

(* subst_label_op does not affect eval_operand when vs_labels agrees *)
Theorem eval_operand_subst_label[local]:
  !old new op s.
    FLOOKUP s.vs_labels old = FLOOKUP s.vs_labels new ==>
    eval_operand (subst_label_op old new op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_label_op_def, eval_operand_def]
QED

(* subst_label_op does not affect eval_operands when vs_labels agrees *)
Theorem eval_operands_subst_label[local]:
  !old new ops s.
    FLOOKUP s.vs_labels old = FLOOKUP s.vs_labels new ==>
    eval_operands (MAP (subst_label_op old new) ops) s =
    eval_operands ops s
Proof
  Induct_on `ops` >>
  rw[eval_operands_def, eval_operand_subst_label]
QED

(* extract_labels after subst_label_op remaps the labels *)
Theorem extract_labels_subst_label[local]:
  !ops old new lbls.
    extract_labels ops = SOME lbls ==>
    extract_labels (MAP (subst_label_op old new) ops) =
    SOME (MAP (\l. if l = old then new else l) lbls)
Proof
  Induct_on `ops` >> rw[extract_labels_def, subst_label_op_def] >>
  Cases_on `h` >> gvs[subst_label_op_def, extract_labels_def] >>
  Cases_on `extract_labels ops` >> gvs[] >>
  res_tac >> rw[extract_labels_def]
QED

Theorem parse_dret_shape_subst_label[local]:
  !inst old_lbl new_lbl.
    parse_dret_shape
      (inst with inst_operands :=
         MAP (subst_label_op old_lbl new_lbl) inst.inst_operands) =
    parse_dret_shape inst
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_operands` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def] >>
  Cases_on `h` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def, subst_label_op_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

val subst_label_nonjump_tac =
  gvs[step_inst_base_def, subst_label_inst_def,
      eval_operands_subst_label, eval_operand_subst_label,
      parse_dret_shape_subst_label] >>
  BasicProvers.every_case_tac >>
  gvs[eval_operand_subst_label, parse_dret_shape_subst_label];

(* For non-jump terminators, subst_label_inst has no effect on step_inst_base
   when vs_labels agrees on old and new labels *)
Theorem step_inst_base_subst_label_non_jump[local]:
  !inst s old_lbl new_lbl.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\ inst.inst_opcode <> INVOKE /\
    FLOOKUP s.vs_labels old_lbl = FLOOKUP s.vs_labels new_lbl ==>
    step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
  >- subst_label_nonjump_tac
  >- subst_label_nonjump_tac
  >- subst_label_nonjump_tac
  >- subst_label_nonjump_tac
  >- subst_label_nonjump_tac
  >- subst_label_nonjump_tac
  >- subst_label_nonjump_tac
  >- subst_label_nonjump_tac
  >- subst_label_nonjump_tac
QED

(* Full JMP: covers all result types including Error *)
Theorem step_inst_base_subst_label_JMP_full[local]:
  !inst s old_lbl new_lbl.
    inst.inst_opcode = JMP ==>
    step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
    (case step_inst_base inst s of
       OK v => OK (if v.vs_current_bb = old_lbl
                   then v with vs_current_bb := new_lbl
                   else v)
     | Halt v1 => Halt v1
     | Abort v2 v3 => Abort v2 v3
     | IntRet v4 v5 => IntRet v4 v5
     | Error v6 => Error v6)
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, subst_label_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[subst_label_op_def, jump_to_def] >>
  rw[]
QED

(* Full JNZ: covers all result types.
   Requires vs_labels agrees on old and new labels. *)
Theorem step_inst_base_subst_label_JNZ_full[local]:
  !inst s old_lbl new_lbl.
    inst.inst_opcode = JNZ /\
    FLOOKUP s.vs_labels old_lbl = FLOOKUP s.vs_labels new_lbl ==>
    step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
    (case step_inst_base inst s of
       OK v => OK (if v.vs_current_bb = old_lbl
                   then v with vs_current_bb := new_lbl
                   else v)
     | Halt v1 => Halt v1
     | Abort v2 v3 => Abort v2 v3
     | IntRet v4 v5 => IntRet v4 v5
     | Error v6 => Error v6)
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, subst_label_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h'` >> simp[subst_label_op_def] >>
  Cases_on `t'` >> simp[COND_RAND, COND_RATOR] >>
  Cases_on `h'`
  >> simp[subst_label_op_def]
  >> Cases_on `t` >> simp[eval_operand_subst_label]
  >> Cases_on `s' = old_lbl` >> Cases_on `s'' = old_lbl`
  >> gvs[jump_to_def]
  >> Cases_on `eval_operand h s` >> gvs[jump_to_def]
  >> Cases_on `x <> 0w` >> gvs[]
QED

(* extract_labels NONE case: subst_label_op preserves NONE *)
Theorem extract_labels_subst_label_none[local]:
  !ops old new.
    extract_labels ops = NONE ==>
    extract_labels (MAP (subst_label_op old new) ops) = NONE
Proof
  Induct_on `ops` >> rw[extract_labels_def, subst_label_op_def] >>
  Cases_on `h` >> gvs[subst_label_op_def, extract_labels_def] >>
  Cases_on `extract_labels ops` >> gvs[] >>
  res_tac >> simp[extract_labels_def, COND_RAND, COND_RATOR]
QED

(* Full DJMP: covers all result types.
   Requires vs_labels agrees on old and new labels. *)
Theorem step_inst_base_subst_label_DJMP_full[local]:
  !inst s old_lbl new_lbl.
    inst.inst_opcode = DJMP /\
    FLOOKUP s.vs_labels old_lbl = FLOOKUP s.vs_labels new_lbl ==>
    step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
    (case step_inst_base inst s of
       OK v => OK (if v.vs_current_bb = old_lbl
                   then v with vs_current_bb := new_lbl
                   else v)
     | Halt v1 => Halt v1
     | Abort v2 v3 => Abort v2 v3
     | IntRet v4 v5 => IntRet v4 v5
     | Error v6 => Error v6)
Proof
  rpt strip_tac >>
  gvs[step_inst_base_def, subst_label_inst_def,
      eval_operand_subst_label] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  simp[eval_operand_subst_label] >>
  Cases_on `eval_operand h s` >> gvs[] >>
  Cases_on `extract_labels t` >> gvs[]
  >- (imp_res_tac extract_labels_subst_label_none >> gvs[])
  >> imp_res_tac extract_labels_subst_label >> gvs[] >>
  Cases_on `w2n x < LENGTH x'` >> gvs[] >>
  simp[listTheory.EL_MAP, subst_label_op_def, jump_to_def] >>
  rw[]
QED

(* Full version covering all terminators except INVOKE.
   Requires vs_labels agrees on old and new labels. *)
Theorem step_inst_base_subst_label_full[local]:
  !inst s old_lbl new_lbl.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    FLOOKUP s.vs_labels old_lbl = FLOOKUP s.vs_labels new_lbl ==>
    step_inst_base (subst_label_inst old_lbl new_lbl inst) s =
    (case step_inst_base inst s of
       OK v => OK (if v.vs_current_bb = old_lbl
                   then v with vs_current_bb := new_lbl
                   else v)
     | Halt v1 => Halt v1
     | Abort v2 v3 => Abort v2 v3
     | IntRet v4 v5 => IntRet v4 v5
     | Error v6 => Error v6)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
  >- simp[step_inst_base_subst_label_JMP_full]
  >- simp[step_inst_base_subst_label_JNZ_full]
  >- simp[step_inst_base_subst_label_DJMP_full]
  >> (* Non-jump terminators: subst has no effect and cannot return OK. *)
     gvs[step_inst_base_subst_label_non_jump, is_terminator_def] >>
     Cases_on `step_inst_base inst s` >> gvs[] >>
     `is_terminator inst.inst_opcode` by gvs[is_terminator_def] >>
     `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
      inst.inst_opcode = DJMP` by
       (irule step_inst_base_ok_terminator_jump >> metis_tac[]) >>
     gvs[]
QED

Theorem get_instruction_subst_label_terminator[local]:
  !old new bb idx.
    get_instruction (subst_label_terminator old new bb) idx =
    OPTION_MAP (\inst. if is_terminator inst.inst_opcode
                       then subst_label_inst old new inst else inst)
               (get_instruction bb idx)
Proof
  rw[get_instruction_def, subst_label_terminator_length] >>
  rw[subst_label_terminator_def, listTheory.EL_MAP]
QED

Theorem subst_label_inst_opcode[local]:
  !old new inst.
    (subst_label_inst old new inst).inst_opcode = inst.inst_opcode
Proof
  rw[subst_label_inst_def]
QED

(* Lift step_inst_base_subst_label_full to step_inst level *)
Theorem step_inst_subst_label_full[local]:
  !fuel ctx inst s old_lbl new_lbl.
    is_terminator inst.inst_opcode /\
    FLOOKUP s.vs_labels old_lbl = FLOOKUP s.vs_labels new_lbl ==>
    step_inst fuel ctx (subst_label_inst old_lbl new_lbl inst) s =
    (case step_inst fuel ctx inst s of
       OK v => OK (if v.vs_current_bb = old_lbl
                   then v with vs_current_bb := new_lbl
                   else v)
     | Halt v1 => Halt v1
     | Abort v2 v3 => Abort v2 v3
     | IntRet v4 v5 => IntRet v4 v5
     | Error v6 => Error v6)
Proof
  rpt strip_tac >>
  imp_res_tac is_terminator_not_INVOKE >>
  simp[step_inst_non_invoke, subst_label_inst_opcode,
       step_inst_base_subst_label_full]
QED

(* Running a label-substituted block: non-terminator instructions are
   unchanged, so execution is identical except the terminator may jump
   to new_lbl instead of old_lbl.
   General version covers all result types. Requires ~s.vs_halted.
   Requires vs_labels agrees on old and new labels. *)
Theorem run_block_subst_label_general[local]:
  !n ctx bb s old_lbl new_lbl.
    ~s.vs_halted /\
    s.vs_labels = FEMPTY ==>
    exec_block n ctx (subst_label_terminator old_lbl new_lbl bb) s =
    (case exec_block n ctx bb s of
       OK v => OK (if v.vs_current_bb = old_lbl
                   then v with vs_current_bb := new_lbl
                   else v)
     | other => other)
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP s.vs_labels old_lbl = FLOOKUP s.vs_labels new_lbl` by
    fs[finite_mapTheory.FLOOKUP_DEF] >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >> rw[] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_subst_label_terminator] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `is_terminator inst.inst_opcode` >>
  fs[subst_label_inst_opcode]
  >- ((* Terminator: use step_inst_subst_label_full, then show halted preserved *)
    simp[Once step_inst_subst_label_full] >>
    imp_res_tac is_terminator_not_INVOKE >>
    (`step_inst n ctx inst s = step_inst_base inst s` by
      simp[step_inst_non_invoke]) >>
    Cases_on `step_inst_base inst s` >> gvs[] >>
    rename1 `OK v` >>
    imp_res_tac step_inst_base_OK_preserves_halted >>
    gvs[COND_RAND, COND_RATOR])
  >> (* Non-terminator: instruction unchanged, use IH *)
  Cases_on `step_inst n ctx inst s` >> gvs[] >>
  rename1 `OK s''` >>
  imp_res_tac step_preserves_labels >>
  Q.PAT_ASSUM `!m. _` (qspec_then
    `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (
    `s.vs_inst_idx < LENGTH bb.bb_instructions` by
      fs[get_instruction_def, AllCaseEqs()] >>
    simp[]
  )) >>
  disch_then (qspecl_then [`bb`,
    `s'' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >>
  imp_res_tac step_preserves_halted >> gvs[]
QED
(* Convenient corollary: OK case *)
Theorem run_block_subst_label_terminator[local]:
  !n ctx bb s old_lbl new_lbl v.
    ~s.vs_halted /\
    s.vs_labels = FEMPTY /\
    exec_block n ctx bb s = OK v ==>
    exec_block n ctx (subst_label_terminator old_lbl new_lbl bb) s =
    OK (if v.vs_current_bb = old_lbl
        then v with vs_current_bb := new_lbl
        else v)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`n`, `ctx`, `bb`, `s`, `old_lbl`, `new_lbl`]
            run_block_subst_label_general) >>
  simp[]
QED

(* ================================================================
   Helper: running the split block forwards vars and jumps to target
   ================================================================ *)

(* General helper: one non-terminator step of exec_block *)
Theorem run_block_non_term_step[local]:
  !fuel ctx bb s inst s' i.
    s.vs_inst_idx = i /\
    get_instruction bb i = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    exec_block fuel ctx bb s =
    exec_block fuel ctx bb (s' with vs_inst_idx := SUC i)
Proof
  rpt strip_tac >> gvs[] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[]
QED

(* Helper: step_inst for an ASSIGN instruction *)
Theorem step_assign_ok[local]:
  !fuel ctx id_base var out val s.
    FLOOKUP s.vs_vars var = SOME val ==>
    step_inst fuel ctx
      <|inst_id := id_base; inst_opcode := ASSIGN;
        inst_operands := [Var var]; inst_outputs := [out]|> s =
    OK (update_var out val s)
Proof
  rpt strip_tac >>
  simp[step_inst_non_invoke, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def]
QED

(* Helper: one ASSIGN at position LENGTH prefix peels off from exec_block *)
Theorem run_block_assign_step[local]:
  !fuel ctx bb s prefix id_val var out val rest.
    bb.bb_instructions = prefix ++
      [<|inst_id := id_val; inst_opcode := ASSIGN;
         inst_operands := [Var var]; inst_outputs := [out]|>] ++ rest /\
    s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
    FLOOKUP s.vs_vars var = SOME val ==>
    exec_block fuel ctx bb s =
    exec_block fuel ctx bb
      ((update_var out val s) with vs_inst_idx := SUC (LENGTH prefix))
Proof
  rpt strip_tac >>
  irule run_block_non_term_step >>
  simp[get_instruction_def, listTheory.EL_APPEND_EQN,
       is_terminator_def, step_assign_ok]
QED

(* MAP SND of build_forwarding_assigns: all forwarding var names *)
Theorem build_fwd_assigns_map_snd[local]:
  !split_label id_base vars repls insts.
    build_forwarding_assigns split_label id_base vars = (repls, insts) ==>
    MAP SND repls = MAP (\v. STRCAT (STRCAT split_label "_fwd_") v) vars
Proof
  Induct_on `vars` >>
  rw[build_forwarding_assigns_def, LET_THM] >>
  pairarg_tac >> gvs[] >> res_tac
QED

(* Cons-step composition for forwarding assigns: given IH about rest_repls
   and an ASSIGN step, derive properties about (var,fwd)::rest_repls.
   Extracted as standalone lemma to avoid first_x_assum ambiguity in batch. *)
(* Key freshness: ALOOKUP key is not a fwd name *)
Theorem alookup_key_not_fwd:
  !split_label id_base vars rest_repls rest_insts w orig new_v.
    build_forwarding_assigns split_label id_base vars =
      (rest_repls, rest_insts) /\
    (!v. MEM v vars ==>
       !w. v <> STRCAT (STRCAT split_label "_fwd_") w) /\
    ALOOKUP rest_repls orig = SOME new_v
    ==>
    orig <> STRCAT (STRCAT split_label "_fwd_") w
Proof
  rpt strip_tac >>
  imp_res_tac build_forwarding_assigns_repls >>
  Q.PAT_ASSUM `MAP FST rest_repls = vars`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  Q.PAT_ASSUM `!v. MEM v (MAP FST rest_repls) ==> _`
    (qspec_then `orig` mp_tac) >>
  (impl_tac >- (
    CCONTR_TAC >>
    fs[GSYM alistTheory.ALOOKUP_NONE])) >>
  disch_then (qspec_then `w` mp_tac) >> simp[]
QED

(* If var is not in vars, then STRCAT split_label "_fwd_" var is not in
   MAP SND repls (since MAP SND repls = MAP (\v. STRCAT ...) vars). *)
Theorem fwd_not_in_map_snd:
  !split_label id_base vars repls insts var.
    build_forwarding_assigns split_label id_base vars = (repls, insts) /\
    ~MEM var vars ==>
    ~MEM (STRCAT (STRCAT split_label "_fwd_") var) (MAP SND repls)
Proof
  rpt strip_tac >>
  imp_res_tac build_fwd_assigns_map_snd >>
  Q.PAT_ASSUM `MAP SND repls = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  fs[listTheory.MEM_MAP, stringTheory.STRCAT_11]
QED

(* If var is in vars and MAP FST repls = vars, then ALOOKUP repls var = SOME. *)
Theorem mem_alookup_some:
  !repls vars var.
    MAP FST repls = vars /\ MEM var vars ==>
    ?rv. ALOOKUP repls var = SOME rv
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP repls var` >> gvs[alistTheory.ALOOKUP_NONE]
QED

(* --- Composition helpers for run_fwd_assigns inductive step --- *)
(* Each is a standalone theorem with explicit premises, avoiding batch divergence
   from ambient assumption manipulation. *)

(* Helper 1: Chain exec_block equations: step equation + IH equation *)
Theorem fwd_compose_run_block[local]:
  !fuel ctx bb s s' prefix id_base var fwd val rest_insts insts.
    insts = <|inst_id := id_base; inst_opcode := ASSIGN;
       inst_operands := [Var var]; inst_outputs := [fwd]|> :: rest_insts /\
    exec_block fuel ctx bb s =
      exec_block fuel ctx bb
        (update_var fwd val s with vs_inst_idx := SUC (LENGTH prefix)) /\
    exec_block fuel ctx bb
      (update_var fwd val s with vs_inst_idx := SUC (LENGTH prefix)) =
    exec_block fuel ctx bb
      (s' with vs_inst_idx :=
         LENGTH (prefix ++ [<|inst_id := id_base; inst_opcode := ASSIGN;
           inst_operands := [Var var]; inst_outputs := [fwd]|>]) +
         LENGTH rest_insts)
    ==>
    exec_block fuel ctx bb s =
      exec_block fuel ctx bb
        (s' with vs_inst_idx := LENGTH insts + LENGTH prefix)
Proof
  rpt strip_tac >> fs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD1]
QED

(* Helper 2: ALOOKUP on (var,fwd)::rest_repls using IH ALOOKUP + non-MEM *)
Theorem fwd_compose_alookup:
  !split_label id_base vars rest_repls rest_insts var fwd val s s'.
    build_forwarding_assigns split_label (id_base + 1) vars =
      (rest_repls, rest_insts) /\
    fwd = STRCAT (STRCAT split_label "_fwd_") var /\
    ~MEM var vars /\
    FLOOKUP s.vs_vars var = SOME val /\
    (!v. v = var \/ MEM v vars ==>
       !w. v <> STRCAT (STRCAT split_label "_fwd_") w) /\
    (!orig new_v. ALOOKUP rest_repls orig = SOME new_v ==>
       FLOOKUP s'.vs_vars new_v =
       FLOOKUP (update_var fwd val s).vs_vars orig) /\
    (!x. ~MEM x (MAP SND rest_repls) ==>
       FLOOKUP s'.vs_vars x = FLOOKUP (update_var fwd val s).vs_vars x) ==>
    !orig new_v. ALOOKUP ((var,fwd)::rest_repls) orig = SOME new_v ==>
       FLOOKUP s'.vs_vars new_v = FLOOKUP s.vs_vars orig
Proof
  rpt strip_tac >>
  fs[alistTheory.ALOOKUP_def] >>
  Cases_on `var = orig` >> fs[]
  >- (
    (* orig = var: new_v = fwd *)
    imp_res_tac fwd_not_in_map_snd >>
    Q.PAT_ASSUM `!x. ~MEM x (MAP SND rest_repls) ==> _`
      (qspec_then `fwd` mp_tac) >>
    (impl_tac >- fs[]) >> strip_tac >>
    fs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE])
  >- (
    (* orig <> var *)
    imp_res_tac alookup_key_not_fwd >>
    Q.PAT_ASSUM `!orig' new_v'. ALOOKUP rest_repls orig' = SOME new_v' ==> _`
      (qspecl_then [`orig`, `new_v`] mp_tac) >>
    (impl_tac >- fs[]) >> strip_tac >>
    fs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE])
QED

(* Helper 3: FDOM composition through update_var *)
Theorem fwd_compose_fdom:
  !fwd val s s'.
    (!x. x IN FDOM (update_var fwd val s).vs_vars ==> x IN FDOM s'.vs_vars) ==>
    !x. x IN FDOM s.vs_vars ==> x IN FDOM s'.vs_vars
Proof
  rpt strip_tac >>
  first_x_assum match_mp_tac >>
  fs[update_var_def, finite_mapTheory.FDOM_FUPDATE]
QED

(* Helper 4: non-MEM FLOOKUP composition through update_var *)
Theorem fwd_compose_flookup:
  !fwd var rest_repls s s' val.
    (!x. ~MEM x (MAP SND rest_repls) ==>
       FLOOKUP s'.vs_vars x = FLOOKUP (update_var fwd val s).vs_vars x) ==>
    !x. ~MEM x (MAP SND ((var,fwd)::rest_repls)) ==>
       FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x
Proof
  rpt strip_tac >>
  `x <> fwd /\ ~MEM x (MAP SND rest_repls)` by
    (fs[listTheory.MAP, listTheory.MEM]) >>
  Q.PAT_ASSUM `!x. ~MEM x (MAP SND rest_repls) ==> _`
    (qspec_then `x` mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  fs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Master composition: combines IH result (relative to update_var) with
   ASSIGN step to produce result relative to original state s.
   All premises explicit -- no ambient assumptions needed. *)
Theorem fwd_step_compose[local]:
  !split_label id_base vars rest_repls rest_insts h val1 s s'
   prefix rest fuel ctx bb.
    build_forwarding_assigns split_label (id_base + 1) vars =
      (rest_repls, rest_insts) /\
    ~MEM h vars /\
    FLOOKUP s.vs_vars h = SOME val1 /\
    (!v. v = h \/ MEM v vars ==>
       !w. v <> STRCAT (STRCAT split_label "_fwd_") w) /\
    bb.bb_instructions =
      prefix ++ <|inst_id := id_base; inst_opcode := ASSIGN;
        inst_operands := [Var h];
        inst_outputs := [STRCAT (STRCAT split_label "_fwd_") h]|> ::
        rest_insts ++ rest /\
    exec_block fuel ctx bb s =
      exec_block fuel ctx bb
        (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s with
         vs_inst_idx := SUC (LENGTH prefix)) /\
    (* IH conclusion relative to update_var ... s *)
    exec_block fuel ctx bb
      (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s with
       vs_inst_idx := LENGTH (prefix ++ [<|inst_id := id_base;
         inst_opcode := ASSIGN; inst_operands := [Var h];
         inst_outputs := [STRCAT (STRCAT split_label "_fwd_") h]|>])) =
    exec_block fuel ctx bb
      (s' with vs_inst_idx :=
         LENGTH rest_insts + LENGTH (prefix ++ [<|inst_id := id_base;
           inst_opcode := ASSIGN; inst_operands := [Var h];
           inst_outputs := [STRCAT (STRCAT split_label "_fwd_") h]|>])) /\
    ~s'.vs_halted /\
    (!orig new_v. ALOOKUP rest_repls orig = SOME new_v ==>
       FLOOKUP s'.vs_vars new_v =
       FLOOKUP (update_var (STRCAT (STRCAT split_label "_fwd_") h)
                  val1 s).vs_vars orig) /\
    (!x. x IN FDOM
       (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s).vs_vars ==>
       x IN FDOM s'.vs_vars) /\
    (!x. ~MEM x (MAP SND rest_repls) ==>
       FLOOKUP s'.vs_vars x =
       FLOOKUP (update_var (STRCAT (STRCAT split_label "_fwd_") h)
                  val1 s).vs_vars x) /\
    s'.vs_current_bb =
      (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s).vs_current_bb /\
    s'.vs_prev_bb =
      (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s).vs_prev_bb /\
    s' with <| vs_vars :=
      (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s).vs_vars;
      vs_inst_idx :=
      (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s).vs_inst_idx
    |> = update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s
    ==>
    ?s''. exec_block fuel ctx bb s =
      exec_block fuel ctx bb
        (s'' with vs_inst_idx :=
           LENGTH (<|inst_id := id_base; inst_opcode := ASSIGN;
             inst_operands := [Var h];
             inst_outputs := [STRCAT (STRCAT split_label "_fwd_") h]|> ::
             rest_insts) + LENGTH prefix) /\
    ~s''.vs_halted /\
    (!orig new_v. ALOOKUP ((h, STRCAT (STRCAT split_label "_fwd_") h)::
                           rest_repls) orig = SOME new_v ==>
       FLOOKUP s''.vs_vars new_v = FLOOKUP s.vs_vars orig) /\
    (!x. x IN FDOM s.vs_vars ==> x IN FDOM s''.vs_vars) /\
    (!x. ~MEM x (MAP SND ((h, STRCAT (STRCAT split_label "_fwd_") h)::
                          rest_repls)) ==>
       FLOOKUP s''.vs_vars x = FLOOKUP s.vs_vars x) /\
    s''.vs_current_bb = s.vs_current_bb /\
    s''.vs_prev_bb = s.vs_prev_bb /\
    s'' with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |> = s
Proof
  rpt strip_tac >>
  qexists_tac `s'` >>
  (* Establish key fact: fwd_h not in MAP SND rest_repls *)
  (`~MEM (STRCAT (STRCAT split_label "_fwd_") h) (MAP SND rest_repls)` by (
    mp_tac (Q.SPECL [`split_label`, `id_base + 1`, `vars`, `rest_repls`,
      `rest_insts`, `h`] fwd_not_in_map_snd) >> simp[])) >>
  (* Establish: FLOOKUP s' fwd_h = SOME val1 *)
  (`FLOOKUP s'.vs_vars (STRCAT (STRCAT split_label "_fwd_") h) = SOME val1` by (
    Q.PAT_ASSUM `!x. ~MEM x (MAP SND rest_repls) ==> _`
      (qspec_then `STRCAT (STRCAT split_label "_fwd_") h` mp_tac) >>
    simp[update_var_def, finite_mapTheory.FLOOKUP_UPDATE])) >>
  (* Derive record identity from IH *)
  (`s' with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |> = s` by (
    Q.PAT_ASSUM `s' with <| vs_vars := _; vs_inst_idx := _ |> = _` mp_tac >>
    simp[update_var_def, venomStateTheory.venom_state_component_equality])) >>
  (* Close 6 of 7 conjuncts via fs *)
  fs[update_var_def, listTheory.LENGTH_APPEND,
     arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD1,
     finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FDOM_FUPDATE] >>
  (* Remaining: ALOOKUP composition *)
  rpt strip_tac >>
  Cases_on `h = orig` >> fs[] >>
  (* h <> orig: ALOOKUP rest_repls orig = SOME new_v *)
  (* Need: fwd_h <> orig to resolve if-then-else in IH *)
  `orig <> STRCAT (STRCAT split_label "_fwd_") h` by (
    mp_tac (Q.SPECL [`split_label`, `id_base + 1`, `vars`, `rest_repls`,
      `rest_insts`, `h`, `orig`, `new_v`] alookup_key_not_fwd) >>
    simp[]) >>
  `STRCAT (STRCAT split_label "_fwd_") h <> orig` by
    fs[] >>
  Q.PAT_ASSUM `!orig new_v. ALOOKUP rest_repls orig = SOME new_v ==> _`
    (drule_then assume_tac) >>
  simp[]
QED

(* Running a sequence of forwarding assigns advances inst_idx and preserves
   variable lookups; ALL_DISTINCT eliminates MEM-in-tail cases *)
Theorem run_fwd_assigns[local]:
  !vars split_label id_base repls insts.
    build_forwarding_assigns split_label id_base vars = (repls, insts) ==>
    ALL_DISTINCT vars ==>
    !prefix rest fuel ctx s bb.
    bb.bb_instructions = prefix ++ insts ++ rest /\
    bb.bb_label = split_label /\
    s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
    (!var. MEM var vars ==> var IN FDOM s.vs_vars) /\
    (!v. MEM v vars ==>
       !w. v <> STRCAT (STRCAT split_label "_fwd_") w) ==>
    ?s'. exec_block fuel ctx bb s =
         exec_block fuel ctx bb
           (s' with vs_inst_idx := LENGTH prefix + LENGTH insts) /\
         ~s'.vs_halted /\
         (!orig new_v. ALOOKUP repls orig = SOME new_v ==>
            FLOOKUP s'.vs_vars new_v = FLOOKUP s.vs_vars orig) /\
         (!x. x IN FDOM s.vs_vars ==> x IN FDOM s'.vs_vars) /\
         (!x. ~MEM x (MAP SND repls) ==>
            FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x) /\
         s'.vs_current_bb = s.vs_current_bb /\
         s'.vs_prev_bb = s.vs_prev_bb /\
         s' with <| vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx |> = s
Proof
  Induct_on `vars`
  >- (rpt strip_tac >>
      fs[build_forwarding_assigns_def] >>
      qexists_tac `s` >>
      (`s with vs_inst_idx := LENGTH prefix = s`
        by fs[venomStateTheory.venom_state_component_equality]) >>
      simp[venomStateTheory.venom_state_component_equality])
  >> (
    rpt strip_tac >>
    fs[build_forwarding_assigns_def, LET_THM] >>
    BETA_TAC >> fs[] >>
    pairarg_tac >> fs[] >>
    Q.PAT_ASSUM `_ :: rest_insts = insts`
      (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >>
                REWRITE_TAC [GSYM th]) >>
    Q.PAT_ASSUM `_ :: rest_repls = repls`
      (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >>
                REWRITE_TAC [GSYM th]) >>
    qabbrev_tac `fwd = STRCAT (STRCAT split_label "_fwd_") h` >>
    `h IN FDOM s.vs_vars` by
      (Q.PAT_ASSUM `!v. v = h \/ _ ==> v IN FDOM s.vs_vars`
         (qspec_then `h` mp_tac) >> simp[]) >>
    `?val1. FLOOKUP s.vs_vars h = SOME val1` by
      fs[finite_mapTheory.FLOOKUP_DEF] >>
    (* Step 1: exec_block assign step *)
    `exec_block fuel ctx bb s =
     exec_block fuel ctx bb
       (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s with
        vs_inst_idx := SUC (LENGTH prefix))` by (
      Q.UNABBREV_TAC `fwd` >>
      irule run_block_assign_step >>
      simp[listTheory.APPEND, listTheory.APPEND_ASSOC]) >>
    (* Step 2: establish FDOM for IH precondition *)
    `!var. MEM var vars ==> var IN FDOM
       (update_var (STRCAT (STRCAT split_label "_fwd_") h) val1 s).vs_vars` by (
      simp[update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
      rpt strip_tac >> DISJ2_TAC >>
      Q.PAT_ASSUM `!var. var = h \/ MEM var vars ==> _`
        (qspec_then `var` mp_tac) >> simp[]) >>
    (* Step 3: apply IH -- use state with updated inst_idx *)
    qabbrev_tac `s1 = update_var (STRCAT (STRCAT split_label "_fwd_") h)
                         val1 s with vs_inst_idx := SUC (LENGTH prefix)` >>
    Q.PAT_ASSUM `!sl ib rp ins. _ ==> _`
      (mp_tac o Q.SPECL [`split_label`, `id_base + 1`,
                          `rest_repls`, `rest_insts`]) >>
    simp[] >>
    disch_then (mp_tac o Q.SPECL
      [`prefix ++ [<|inst_id := id_base; inst_opcode := ASSIGN;
          inst_operands := [Var h];
          inst_outputs := [STRCAT (STRCAT split_label "_fwd_") h]|>]`,
       `rest`, `fuel`, `ctx`, `s1`, `bb`]) >>
    Q.UNABBREV_TAC `s1` >>
    simp[update_var_def, listTheory.LENGTH_APPEND,
         finite_mapTheory.FDOM_FUPDATE,
         listTheory.APPEND_ASSOC, listTheory.APPEND,
         arithmeticTheory.ADD1] >>
    strip_tac >>
    (* Step 4: apply master composition -- discharge antecedent from asms *)
    mp_tac (Q.SPECL [
      `split_label`, `id_base`, `vars`, `rest_repls`, `rest_insts`,
      `h`, `val1`, `s`, `s'`, `prefix`, `rest`, `fuel`, `ctx`, `bb`]
      fwd_step_compose) >>
    simp[update_var_def, arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >> simp[] >>
    rpt strip_tac >> TRY res_tac >>
    fs[update_var_def, venomStateTheory.venom_state_component_equality])
QED

(* Running split block: succeeds, forwards vars, jumps to target *)
Theorem run_split_block:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx s.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    s.vs_current_bb = split_bb.bb_label /\
    (!var. MEM var (nub (phi_vars_needing_forward
             pred_bb.bb_label pred_bb target_bb.bb_instructions)) ==>
       var IN FDOM s.vs_vars) /\
    (!v. MEM v (nub (phi_vars_needing_forward
             pred_bb.bb_label pred_bb target_bb.bb_instructions)) ==>
       !w. v <> STRCAT (STRCAT
             (split_block_name pred_bb.bb_label target_bb.bb_label)
             "_fwd_") w) ==>
    ?v. exec_block fuel ctx split_bb s = OK v /\
        v.vs_current_bb = target_bb.bb_label /\
        v.vs_prev_bb = SOME split_bb.bb_label /\
        v.vs_inst_idx = 0 /\ ~v.vs_halted /\
        (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
           FLOOKUP v.vs_vars new_v = FLOOKUP s.vs_vars orig) /\
        (!x. x IN FDOM s.vs_vars ==> x IN FDOM v.vs_vars) /\
        (!x. ~MEM x (MAP SND var_repls) ==>
           FLOOKUP v.vs_vars x = FLOOKUP s.vs_vars x) /\
        v with <| vs_vars := s.vs_vars;
                  vs_current_bb := s.vs_current_bb;
                  vs_prev_bb := s.vs_prev_bb;
                  vs_inst_idx := s.vs_inst_idx |> = s
Proof
  rw[build_split_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.SPECL [
    `nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
            target_bb.bb_instructions)`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `id_base`] run_fwd_assigns) >>
  simp[] >>
  disch_then (qspecl_then [
    `[]`,
    `[<| inst_id := id_base + LENGTH (nub (phi_vars_needing_forward
           pred_bb.bb_label pred_bb target_bb.bb_instructions));
         inst_opcode := JMP;
         inst_operands := [Label target_bb.bb_label];
         inst_outputs := [] |>]`,
    `fuel`, `ctx`, `s`,
    `<| bb_label := split_block_name pred_bb.bb_label target_bb.bb_label;
        bb_instructions := fwd_insts ++
          [<| inst_id := id_base + LENGTH (nub (phi_vars_needing_forward
                pred_bb.bb_label pred_bb target_bb.bb_instructions));
              inst_opcode := JMP;
              inst_operands := [Label target_bb.bb_label];
              inst_outputs := [] |>] |>`] mp_tac) >>
  simp[] >>
  disch_then strip_assume_tac >>
  (* Extract field equalities from record identity *)
  Q.PAT_ASSUM `_ with <|vs_vars := _; vs_inst_idx := _|> = _`
    (fn th => ASSUME_TAC (REWRITE_RULE
       [venomStateTheory.venom_state_component_equality] th)) >>
  pop_assum (fn th => EVERY (map ASSUME_TAC (CONJUNCTS th))) >>
  (* Rewrite exec_block equation *)
  Q.PAT_ASSUM `exec_block _ _ _ s = exec_block _ _ _ _`
    (fn eq => REWRITE_TAC [eq]) >>
  qexists_tac `s' with <| vs_current_bb := target_bb.bb_label;
    vs_prev_bb := SOME (split_block_name pred_bb.bb_label target_bb.bb_label);
    vs_inst_idx := 0 |>` >>
  simp[Once exec_block_def, get_instruction_def, listTheory.EL_APPEND_EQN,
       is_terminator_def, step_inst_non_invoke,
       step_inst_base_def, jump_to_def,
       venomStateTheory.venom_state_component_equality] >>
  fs[]
QED

(* ASSIGN with undefined variable gives Error *)
Theorem step_assign_error[local]:
  !fuel ctx id_base var out s.
    var NOTIN FDOM s.vs_vars ==>
    ?e. step_inst fuel ctx
      <|inst_id := id_base; inst_opcode := ASSIGN;
        inst_operands := [Var var]; inst_outputs := [out]|> s = Error e
Proof
  rpt strip_tac >>
  simp[step_inst_non_invoke, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def] >>
  fs[finite_mapTheory.FLOOKUP_DEF]
QED

(* exec_block on a block with ASSIGN at position LENGTH prefix errors
   when the assigned variable is not in FDOM *)
Theorem run_block_assign_error[local]:
  !fuel ctx bb s prefix id_base var out rest.
    bb.bb_instructions = prefix ++
      [<|inst_id := id_base; inst_opcode := ASSIGN;
         inst_operands := [Var var]; inst_outputs := [out]|>] ++ rest /\
    s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
    var NOTIN FDOM s.vs_vars ==>
    ?e. exec_block fuel ctx bb s = Error e
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def, listTheory.EL_APPEND_EQN,
       step_inst_non_invoke, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_DEF]
QED

(* When head var is not in FDOM, the first ASSIGN errors *)
Theorem fwd_assigns_head_not_fdom[local]:
  !fuel ctx bb s prefix id_base h fwd_name rest_insts rest.
    bb.bb_instructions = prefix ++
      [<|inst_id := id_base; inst_opcode := ASSIGN;
         inst_operands := [Var h]; inst_outputs := [fwd_name]|>] ++
      rest_insts ++ rest /\
    s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
    h NOTIN FDOM s.vs_vars ==>
    ?e. exec_block fuel ctx bb s = Error e
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `prefix`, `id_base`,
    `h`, `fwd_name`, `rest_insts ++ rest`] run_block_assign_error) >>
  simp[listTheory.APPEND_ASSOC]
QED

(* If any fwd var is not in FDOM, the forwarding assigns error.
   Proof by induction on vars: either the current head fails its ASSIGN
   (if not in FDOM) or succeeds and we recurse on the tail. *)
Theorem fwd_assigns_not_fdom_error[local]:
  !vars split_label id_base repls insts.
    build_forwarding_assigns split_label id_base vars = (repls, insts) ==>
    ALL_DISTINCT vars ==>
    !prefix rest fuel ctx s bb var.
    bb.bb_instructions = prefix ++ insts ++ rest /\
    bb.bb_label = split_label /\
    s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
    MEM var vars /\ var NOTIN FDOM s.vs_vars /\
    (!v. MEM v vars ==>
       !w. v <> STRCAT (STRCAT split_label "_fwd_") w) ==>
    ?e. exec_block fuel ctx bb s = Error e
Proof
  Induct_on `vars` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `build_forwarding_assigns split_label (id_base + 1) vars` >>
  rename1 `_ = (rest_repls, rest_insts)` >>
  gvs[build_forwarding_assigns_def, LET_THM] >>
  rpt strip_tac >>
  Cases_on `h IN FDOM s.vs_vars`
  >- (
    (* h in FDOM, var = h: contradicts var NOTIN FDOM *)
    gvs[])
  >- (
    (* h not in FDOM, var = h: first ASSIGN errors *)
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `prefix`, `id_base`,
      `h`, `STRCAT (STRCAT split_label "_fwd_") h`,
      `rest_insts`, `rest`] fwd_assigns_head_not_fdom) >>
    simp[])
  >- (
    (* h in FDOM, MEM var vars: first ASSIGN succeeds, reduce to tail *)
    `FLOOKUP s.vs_vars h = SOME (FAPPLY s.vs_vars h)` by
      simp[finite_mapTheory.FLOOKUP_DEF] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `prefix`, `id_base`,
      `h`, `STRCAT (STRCAT split_label "_fwd_") h`,
      `FAPPLY s.vs_vars h`, `rest_insts ++ rest`]
      run_block_assign_step) >>
    simp[] >> disch_then (fn eq => REWRITE_TAC[eq]) >>
    first_x_assum (qspecl_then [`split_label`, `id_base + 1`] mp_tac) >>
    simp[] >>
    disch_then (qspecl_then [`prefix ++
      [<|inst_id := id_base; inst_opcode := ASSIGN;
         inst_operands := [Var h];
         inst_outputs := [STRCAT (STRCAT split_label "_fwd_") h]|>]`,
      `rest`, `fuel`, `ctx`,
      `(update_var (STRCAT (STRCAT split_label "_fwd_") h)
                   (FAPPLY s.vs_vars h) s) with
         vs_inst_idx := SUC (LENGTH prefix)`,
      `bb`, `var`] mp_tac) >>
    PURE_REWRITE_TAC[rich_listTheory.APPEND_ASSOC_CONS] >>
    simp[update_var_def, venomStateTheory.venom_state_component_equality] >>
    disch_then irule >>
    simp[finite_mapTheory.FDOM_FUPDATE] >>
    `var <> STRCAT (STRCAT split_label "_fwd_") h` by (
      CCONTR_TAC >> gvs[] >>
      first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
    simp[])
  >- (
    (* h not in FDOM, MEM var vars: first ASSIGN errors *)
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `prefix`, `id_base`,
      `h`, `STRCAT (STRCAT split_label "_fwd_") h`,
      `rest_insts`, `rest`] fwd_assigns_head_not_fdom) >>
    simp[])
QED

(* If split block returns OK, all phi vars must have been in FDOM *)
Theorem split_block_ok_implies_fdom:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx s v.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    exec_block fuel ctx split_bb s = OK v /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    s.vs_current_bb = split_bb.bb_label /\
    (!v. MEM v (nub (phi_vars_needing_forward
             pred_bb.bb_label pred_bb target_bb.bb_instructions)) ==>
       !w. v <> STRCAT (STRCAT
             (split_block_name pred_bb.bb_label target_bb.bb_label)
             "_fwd_") w) ==>
    !var. MEM var (nub (phi_vars_needing_forward pred_bb.bb_label
                    pred_bb target_bb.bb_instructions)) ==>
       var IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  fs[build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  mp_tac (Q.SPECL [`nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
                      target_bb.bb_instructions)`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `id_base`] fwd_assigns_not_fdom_error) >>
  strip_tac >>
  first_x_assum (qspecl_then [`var_repls'`, `fwd_insts`] mp_tac) >>
  (impl_tac >- simp[]) >>
  (impl_tac >- simp[listTheory.all_distinct_nub]) >>
  disch_then (qspecl_then [`[]`,
    `[<| inst_id := id_base + LENGTH (nub (phi_vars_needing_forward
           pred_bb.bb_label pred_bb target_bb.bb_instructions));
         inst_opcode := JMP;
         inst_operands := [Label target_bb.bb_label];
         inst_outputs := [] |>]`,
    `fuel`, `ctx`, `s`,
    `split_bb`,
    `var`] mp_tac) >>
  gvs[]
QED

(* phi_pairs membership implies Var v is in the operand list *)
Theorem phi_pairs_mem_var:
  !ops l v. MEM (l, v) (phi_pairs ops) ==> MEM (Var v) ops
Proof
  ho_match_mp_tac venomInstTheory.phi_pairs_ind >>
  rpt strip_tac >> fs[venomInstTheory.phi_pairs_def] >>
  metis_tac[]
QED

(* phi_vars_needing_forward produces vars that are in fn_all_vars *)
Theorem phi_fwd_var_in_fn_all_vars:
  !func target_bb pred_lbl pred_bb v.
    MEM target_bb func.fn_blocks /\
    MEM v (phi_vars_needing_forward pred_lbl pred_bb
             target_bb.bb_instructions) ==>
    MEM v (fn_all_vars func)
Proof
  rpt strip_tac >>
  drule phi_vars_resolve_phi >> strip_tac >>
  drule phi_pairs_mem_var >> strip_tac >>
  irule inst_operand_var_in_fn_all_vars >>
  MAP_EVERY qexists_tac [`target_bb`, `inst'`] >> simp[]
QED

(* Bridge: build_split_block -> build_forwarding_assigns properties *)
Theorem build_split_block_repls:
  !pred_bb target_bb id_base split_bb var_repls.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) ==>
    MAP FST var_repls = nub (phi_vars_needing_forward pred_bb.bb_label
      pred_bb target_bb.bb_instructions) /\
    (!v new_v. ALOOKUP var_repls v = SOME new_v ==>
       new_v = STRCAT (STRCAT (split_block_name pred_bb.bb_label
         target_bb.bb_label) "_fwd_") v)
Proof
  rpt strip_tac >>
  fs[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  mp_tac (Q.SPECL [`split_block_name pred_bb.bb_label target_bb.bb_label`,
    `id_base`,
    `nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
            target_bb.bb_instructions)`]
    cfgNormSimTheory.build_forwarding_assigns_repls) >>
  simp[]
QED

(* var_repls new names are not in fn_all_vars *)
Theorem var_repls_new_not_in_fn_all_vars:
  !func pred_bb target_bb id_base split_bb var_repls orig new_v.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    (!var. ~MEM (STRCAT (STRCAT (split_block_name pred_bb.bb_label
                  target_bb.bb_label) "_fwd_") var)
                (fn_all_vars func)) /\
    ALOOKUP var_repls orig = SOME new_v ==>
    ~MEM new_v (fn_all_vars func)
Proof
  rpt strip_tac >>
  drule build_split_block_repls >> strip_tac >>
  `new_v = STRCAT (STRCAT (split_block_name pred_bb.bb_label
     target_bb.bb_label) "_fwd_") orig` by metis_tac[] >>
  metis_tac[]
QED

(* Strengthening: any element of MAP SND var_repls is not in fn_all_vars *)
Theorem var_repls_snd_not_in_fn_all_vars:
  !func pred_bb target_bb id_base split_bb var_repls v.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    (!var. ~MEM (STRCAT (STRCAT (split_block_name pred_bb.bb_label
                  target_bb.bb_label) "_fwd_") var)
                (fn_all_vars func)) /\
    MEM v (MAP SND var_repls) ==>
    ~MEM v (fn_all_vars func)
Proof
  rpt strip_tac >>
  fs[listTheory.MEM_MAP] >>
  Cases_on `y` >> fs[] >>
  drule build_split_block_repls >> strip_tac >>
  `ALL_DISTINCT (MAP FST var_repls)` by
    metis_tac[listTheory.all_distinct_nub] >>
  `ALOOKUP var_repls q = SOME v` by
    metis_tac[alistTheory.ALOOKUP_ALL_DISTINCT_MEM] >>
  metis_tac[var_repls_new_not_in_fn_all_vars]
QED

(* var_repls resolve to PHI instructions *)
Theorem var_repls_resolve_phi:
  !func pred_bb target_bb id_base split_bb var_repls orig new_v.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    fn_inst_wf func /\ fn_phi_labels_distinct func /\
    MEM target_bb func.fn_blocks /\
    ALOOKUP var_repls orig = SOME new_v ==>
    ?inst'. MEM inst' target_bb.bb_instructions /\
      inst'.inst_opcode = PHI /\
      resolve_phi pred_bb.bb_label inst'.inst_operands = SOME (Var orig)
Proof
  rpt strip_tac >>
  drule build_split_block_repls >> strip_tac >>
  `MEM (orig, new_v) var_repls` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `MEM orig (MAP FST var_repls)` by (
    simp[listTheory.MEM_MAP] >> qexists_tac `(orig, new_v)` >> simp[]) >>
  `MEM orig (phi_vars_needing_forward pred_bb.bb_label
     pred_bb target_bb.bb_instructions)` by metis_tac[listTheory.MEM_nub] >>
  mp_tac phi_vars_resolve_phi_full >>
  disch_then (qspecl_then [`pred_bb.bb_label`, `pred_bb`,
    `target_bb.bb_instructions`, `orig`, `func`, `target_bb`] mp_tac) >>
  simp[]
QED

(* run_blocks on the same function with state_equiv states gives
   result_equiv results. Reusable across all pass proofs. *)
Theorem run_function_same_fn_state_equiv[local]:
  !func fuel ctx s1 s2.
    state_equiv (COMPL (set (fn_all_vars func))) s1 s2 ==>
    lift_result
      (state_equiv (COMPL (set (fn_all_vars func))))
      (execution_equiv (COMPL (set (fn_all_vars func))))
      (execution_equiv (COMPL (set (fn_all_vars func))))
      (run_blocks fuel ctx func s1)
      (run_blocks fuel ctx func s2)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (ISPECL [
    ``state_equiv (COMPL (set (fn_all_vars (func : ir_function))))``,
    ``execution_equiv (COMPL (set (fn_all_vars (func : ir_function))))``,
    ``func : ir_function``]
    execEquivParamPropsTheory.exec_block_preserves_R) >>
  simp[execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel] >>
  impl_tac
  >- (rpt strip_tac
      >- metis_tac[stateEquivPropsTheory.state_equiv_trans]
      >- metis_tac[stateEquivPropsTheory.execution_equiv_trans]
      >> (`MEM x (fn_all_vars func)` by
            metis_tac[inst_operand_var_in_fn_all_vars] >>
          mp_tac stateEquivPropsTheory.eval_operand_equiv >>
          disch_then (qspecl_then [
            `COMPL (set (fn_all_vars func))`,
            `Var x`, `s1'`, `s2'`] mp_tac) >>
          simp[venomStateTheory.eval_operand_def, pred_setTheory.IN_COMPL]))
  >> (strip_tac >> metis_tac[])
QED

(* Helper: when execution reaches target_bb from pred_bb, the transformed
   function routes through split_bb first. This is the hard case of
   insert_split correctness.
   Proof structure:
   1. Unfold LHS one step to get exec_block m ctx target_bb v1
   2. Apply run_split_block to get v_split from split block execution
   3. Apply run_block_update_phis_forwarded_full for block-level equivalence
   4. For OK continuation: bridge states via run_block_preserves_R, then IH
   5. Pick fuel' = fuel_ih + 3 to accommodate pred_bb + split_bb + target_bb *)
(* Helper: 3-step unfolding of run_blocks through pred -> split -> target *)
Theorem run_function_2step:
  !func' bb1 bb2 lbl1 lbl2 f ctx s v1.
    lookup_block lbl1 func'.fn_blocks = SOME bb1 /\
    lookup_block lbl2 func'.fn_blocks = SOME bb2 /\
    s.vs_current_bb = lbl1 /\
    run_block_entry f ctx bb1 s = OK v1 /\
    ~v1.vs_halted /\
    v1.vs_current_bb = lbl2 ==>
    run_blocks (SUC (SUC f)) ctx func' s =
      case run_block_entry f ctx bb2 v1 of
        OK v' => if v'.vs_halted then Halt v' else run_blocks f ctx func' v'
      | Halt v => Halt v
      | Abort a v => Abort a v
      | IntRet vals v => IntRet vals v
      | Error e => Error e
Proof
  rpt strip_tac >>
  `!k. k >= f ==> run_block_entry k ctx bb1 s = OK v1` by (
    rpt strip_tac >>
    drule venomExecPropsTheory.run_block_fuel_mono_OK >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >>
  ntac 2 (
    ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[Excl "run_block_def"])
QED

(*
 * 3-step run_blocks unfolding (flexible fuel form).
 * Blocks 1 and 2 succeed at individual fuels f1, f2 (which are <=
 * the actual fuel they receive: SUC (SUC f) and SUC f respectively).
 * Block 3 uses exactly fuel f. Result fuel is SUC (SUC (SUC f)).
 *
 * This handles the common pattern where different blocks were proved
 * at different fuel levels (e.g. pred at SUC m, split at m).
 *)
Theorem run_function_3step:
  !func' bb1 bb2 bb3 lbl1 lbl2 lbl3 f f1 f2 ctx s v1 v2.
    lookup_block lbl1 func'.fn_blocks = SOME bb1 /\
    lookup_block lbl2 func'.fn_blocks = SOME bb2 /\
    lookup_block lbl3 func'.fn_blocks = SOME bb3 /\
    s.vs_current_bb = lbl1 /\
    run_block_entry f1 ctx bb1 s = OK v1 /\
    f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\
    v1.vs_current_bb = lbl2 /\
    run_block_entry f2 ctx bb2 v1 = OK v2 /\
    f2 <= SUC f /\
    ~v2.vs_halted /\
    v2.vs_current_bb = lbl3 ==>
    run_blocks (SUC (SUC (SUC f))) ctx func' s =
      case run_block_entry f ctx bb3 v2 of
        OK v' => if v'.vs_halted then Halt v' else run_blocks f ctx func' v'
      | Halt v => Halt v
      | Abort a v => Abort a v
      | IntRet vals v => IntRet vals v
      | Error e => Error e
Proof
  rpt strip_tac >>
  `run_block_entry (SUC (SUC f)) ctx bb1 s = OK v1` by (
    qpat_x_assum `run_block_entry f1 ctx bb1 s = OK v1`
      (fn th => mp_tac (Q.SPECL [`f1`, `SUC (SUC f)`, `ctx`, `bb1`, `s`, `v1`]
        venomExecPropsTheory.run_block_fuel_mono_OK) >> mp_tac th) >>
    simp[]) >>
  `run_block_entry (SUC f) ctx bb2 v1 = OK v2` by (
    qpat_x_assum `run_block_entry f2 ctx bb2 v1 = OK v2`
      (fn th => mp_tac (Q.SPECL [`f2`, `SUC f`, `ctx`, `bb2`, `v1`, `v2`]
        venomExecPropsTheory.run_block_fuel_mono_OK) >> mp_tac th) >>
    simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >>
  ntac 3 (
    ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[Excl "run_block_def"])
QED

(* run_function_3step specialized for the OK + not-halted case.
   Avoids case expressions entirely -- gives a direct equation. *)
Theorem run_function_3step_ok[local]:
  !func' bb1 bb2 bb3 lbl1 lbl2 lbl3 f f1 f2 ctx s v1 v2 v3.
    lookup_block lbl1 func'.fn_blocks = SOME bb1 /\
    lookup_block lbl2 func'.fn_blocks = SOME bb2 /\
    lookup_block lbl3 func'.fn_blocks = SOME bb3 /\
    s.vs_current_bb = lbl1 /\
    run_block_entry f1 ctx bb1 s = OK v1 /\
    f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\ v1.vs_current_bb = lbl2 /\
    run_block_entry f2 ctx bb2 v1 = OK v2 /\
    f2 <= SUC f /\
    ~v2.vs_halted /\ v2.vs_current_bb = lbl3 /\
    run_block_entry f ctx bb3 v2 = OK v3 /\
    ~v3.vs_halted ==>
    run_blocks (SUC (SUC (SUC f))) ctx func' s =
      run_blocks f ctx func' v3
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func'`, `bb1`, `bb2`, `bb3`, `lbl1`, `lbl2`, `lbl3`,
    `f`, `f1`, `f2`, `ctx`, `s`, `v1`, `v2`] run_function_3step) >>
  simp[]
QED

(* run_function_3step specialized for the Error case on bb3. *)
Theorem run_function_3step_error[local]:
  !func' bb1 bb2 bb3 lbl1 lbl2 lbl3 f f1 f2 ctx s v1 v2 e.
    lookup_block lbl1 func'.fn_blocks = SOME bb1 /\
    lookup_block lbl2 func'.fn_blocks = SOME bb2 /\
    lookup_block lbl3 func'.fn_blocks = SOME bb3 /\
    s.vs_current_bb = lbl1 /\
    run_block_entry f1 ctx bb1 s = OK v1 /\
    f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\ v1.vs_current_bb = lbl2 /\
    run_block_entry f2 ctx bb2 v1 = OK v2 /\
    f2 <= SUC f /\
    ~v2.vs_halted /\ v2.vs_current_bb = lbl3 /\
    run_block_entry f ctx bb3 v2 = Error e ==>
    run_blocks (SUC (SUC (SUC f))) ctx func' s = Error e
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func'`, `bb1`, `bb2`, `bb3`, `lbl1`, `lbl2`, `lbl3`,
    `f`, `f1`, `f2`, `ctx`, `s`, `v1`, `v2`] run_function_3step) >>
  simp[]
QED

(* Well-formedness facts about a block in a well-formed function *)
Theorem wf_block_facts[local]:
  !func bb. wf_function_no_ids func /\ fn_inst_wf func /\
            MEM bb func.fn_blocks ==>
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    !i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed bb` by
    (fs[wf_function_no_ids_def] >> metis_tac[]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >>
     fs[venomWfTheory.fn_inst_wf_def] >> metis_tac[]) >>
  fs[venomWfTheory.bb_well_formed_def] >> rpt strip_tac >> res_tac >> fs[]
QED

(* result_equiv (any vars) (Error e) r ==> r is also Error *)
Theorem result_equiv_Error_elim[local]:
  !vars e r. result_equiv vars (Error e) r ==> ?e'. r = Error e'
Proof
  rpt gen_tac >> Cases_on `r` >> simp[stateEquivTheory.result_equiv_def]
QED

(* Helper: derive execution_equiv from run_split_block outputs.
   The split block only adds _fwd_ variables (not in fn_all_vars) and
   preserves all other state fields, so execution_equiv holds. *)
Theorem split_block_execution_equiv:
  !v1 v_split var_repls func lbl1 lbl2.
    (!x. ~MEM x (MAP SND var_repls) ==>
       FLOOKUP v_split.vs_vars x = FLOOKUP v1.vs_vars x) /\
    (v_split with <|vs_vars := v1.vs_vars;
       vs_prev_bb := SOME lbl1;
       vs_current_bb := lbl2;
       vs_inst_idx := 0|> =
     v1 with vs_current_bb := lbl2) /\
    (!v. MEM v (MAP SND var_repls) ==> ~MEM v (fn_all_vars func))
    ==>
    execution_equiv (COMPL (set (fn_all_vars func))) v1 v_split
Proof
  rpt gen_tac >> strip_tac >>
  simp[stateEquivTheory.execution_equiv_def,
       venomStateTheory.lookup_var_def] >>
  conj_tac >- (
    rpt strip_tac >>
    `~MEM v (MAP SND var_repls)` by metis_tac[] >>
    metis_tac[]) >>
  fs[venomStateTheory.venom_state_component_equality]
QED

(* Helper: given split_bb returned OK, derive all properties needed for
   forwarded_full. Packages run_split_block + execution_equiv + forwarded_full. *)
Theorem split_block_forwarded_result_equiv[local]:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx v1 v_split func
   split_lbl.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    exec_block fuel ctx split_bb (v1 with vs_current_bb := split_lbl) =
      OK v_split /\
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    MEM target_bb func.fn_blocks /\
    ALL_DISTINCT (fn_labels func) /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    v1.vs_inst_idx = 0 /\ ~v1.vs_halted /\
    v1.vs_prev_bb = SOME pred_bb.bb_label /\
    v1.vs_current_bb = target_bb.bb_label
  ==>
    ~v_split.vs_halted /\
    v_split.vs_current_bb = target_bb.bb_label /\
    v_split.vs_inst_idx = 0 /\
    v_split.vs_prev_bb = SOME (split_block_name pred_bb.bb_label target_bb.bb_label) /\
    execution_equiv (COMPL (set (fn_all_vars func))) v1 v_split /\
    (!orig new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP v_split.vs_vars new_v = FLOOKUP v1.vs_vars orig) /\
    (!f. result_equiv (COMPL (set (fn_all_vars func)))
       (exec_block f ctx target_bb v1)
       (exec_block f ctx
          (update_phis_for_split pred_bb.bb_label split_lbl var_repls
             target_bb) v_split))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `split_lbl = _` SUBST_ALL_TAC >>
  drule cfgNormSimTheory.build_split_block_label >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
    `split_bb`, `var_repls`] var_repls_snd_not_in_fn_all_vars) >>
  simp[] >> strip_tac >>
  `!v. MEM v (nub (phi_vars_needing_forward pred_bb.bb_label
           pred_bb target_bb.bb_instructions)) ==>
     !w. v <> STRCAT (STRCAT
           (split_block_name pred_bb.bb_label target_bb.bb_label)
           "_fwd_") w` by
   (rpt strip_tac >> CCONTR_TAC >> fs[] >>
    mp_tac (Q.SPECL [`func`, `target_bb`, `pred_bb.bb_label`,
      `pred_bb`, `v`] phi_fwd_var_in_fn_all_vars) >>
    simp[] >> metis_tac[listTheory.MEM_nub]) >>
  (* Derive FDOM from the OK result, so run_split_block's preconditions
     are all satisfied and no residual implication remains *)
  mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
    `var_repls`, `fuel`, `ctx`,
    `v1 with vs_current_bb :=
       split_block_name pred_bb.bb_label target_bb.bb_label`,
    `v_split`] split_block_ok_implies_fdom) >>
  simp[] >> strip_tac >>
  (* Now apply run_split_block with all preconditions satisfied *)
  mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
    `var_repls`] run_split_block) >>
  simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`,
    `v1 with vs_current_bb :=
       split_block_name pred_bb.bb_label target_bb.bb_label`] mp_tac) >>
  simp[] >>
  strip_tac >>
  (* Apply split_block_execution_equiv while record equality still exists *)
  drule_all split_block_execution_equiv >> strip_tac >>
  (* Now safe to use fs[] to simplify *)
  fs[] >>
  simp[] >> gen_tac >>
  irule run_block_update_phis_forwarded_full >>
  conj_tac
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
        `split_bb`, `var_repls`, `orig`, `new_v`]
        var_repls_resolve_phi) >> simp[])
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
        `split_bb`, `var_repls`, `orig`, `new_v`]
        var_repls_new_not_in_fn_all_vars) >> simp[])
QED
Theorem execution_equiv_FLOOKUP_vars[local]:
  !vars s1 s2 var.
    execution_equiv vars s1 s2 /\ var NOTIN vars ==>
    FLOOKUP s2.vs_vars var = FLOOKUP s1.vs_vars var
Proof
  simp[stateEquivTheory.execution_equiv_def, venomStateTheory.lookup_var_def]
QED

(* Helper: resolve_phi on updated_ops is NONE when resolve_phi pred_lbl original = NONE *)
Theorem eval_one_phi_backward_resolve_NONE[local]:
  !s1 s2 pred_lbl split_lbl var_repls inst vars out.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    resolve_phi pred_lbl inst.inst_operands = NONE /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    eval_one_phi s1 inst = NONE ==>
    eval_one_phi s2
        (inst with inst_operands :=
          update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  simp[eval_one_phi_def] >>
  Cases_on `resolve_phi split_lbl
     (update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands)` >> gvs[] >>
  imp_res_tac resolve_phi_update_phi_ops_match_rev >>
  gvs[]
QED

(* Helper: when resolve_phi pred_lbl = SOME val_op but eval_operand val_op s1 = NONE,
   the updated phi also evaluates to NONE *)
Theorem eval_one_phi_backward_resolve_SOME_eval_NONE[local]:
  !s1 s2 pred_lbl split_lbl var_repls inst vars out val_op.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    resolve_phi pred_lbl inst.inst_operands = SOME val_op /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig /\
         new_v NOTIN vars) /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==> orig NOTIN vars) /\
    eval_operand val_op s1 = NONE ==>
    eval_one_phi s2
        (inst with inst_operands :=
          update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`pred_lbl`, `split_lbl`, `var_repls`,
             `inst.inst_operands`, `val_op`]
      resolve_phi_update_phi_ops_match) >>
  simp[] >> strip_tac >>
  simp[eval_one_phi_def] >>
  Cases_on `val_op` >> gvs[eval_operand_def, AllCaseEqs(), lookup_var_def] >>
  TRY (
    (* Label case: need FLOOKUP s2.vs_labels s = NONE from execution_equiv *)
    `s1.vs_labels = s2.vs_labels` by
      (qpat_x_assum `execution_equiv vars s1 s2` mp_tac >>
       simp[stateEquivTheory.execution_equiv_def]) >>
    gvs[] >> NO_TAC) >>
  (* Var case: case-split on ALOOKUP *)
  Cases_on `ALOOKUP var_repls s` >> gvs[eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s1.vs_vars s` >> gvs[] >>
  imp_res_tac execution_equiv_FLOOKUP_vars >> gvs[]
QED

(* Boundary lemmas: eval_one_phi = NONE for trivial output structures.
   These handle the record-update case directly so consumers don't need
   to fight the simplifier's inability to pattern-match through record updates. *)
Theorem eval_one_phi_none_empty[local]:
  !s inst. inst.inst_outputs = [] ==> eval_one_phi s inst = NONE
Proof
  rpt strip_tac >> gvs[eval_one_phi_def, AllCaseEqs()]
QED

Theorem eval_one_phi_none_multi[local]:
  !s inst h h' rest. inst.inst_outputs = h::h'::rest ==>
    eval_one_phi s inst = NONE
Proof
  rpt strip_tac >> Cases_on `s.vs_prev_bb` >> gvs[eval_one_phi_def, AllCaseEqs()]
QED

(* Version of eval_one_phi_none_empty that absorbs the record update *)
Theorem eval_one_phi_none_empty_update[local]:
  !s inst new_ops. inst.inst_outputs = [] ==>
    eval_one_phi s (inst with inst_operands := new_ops) = NONE
Proof
  rpt strip_tac >> simp[eval_one_phi_def, instruction_accfupds]
QED

(* Version of eval_one_phi_none_multi that absorbs the record update *)
Theorem eval_one_phi_none_multi_update[local]:
  !s inst h h' rest new_ops. inst.inst_outputs = h::h'::rest ==>
    eval_one_phi s (inst with inst_operands := new_ops) = NONE
Proof
  rpt strip_tac >> Cases_on `s.vs_prev_bb` >>
  simp[eval_one_phi_def, instruction_accfupds]
QED
(* Backward direction for single PHI: if eval_one_phi s1 inst = NONE,
   then eval_one_phi s2 (updated inst) = NONE too. *)
Theorem eval_one_phi_backward_NONE[local]:
  !s1 s2 pred_lbl split_lbl var_repls inst vars.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    inst.inst_opcode = PHI /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig /\
         new_v NOTIN vars) /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==> orig NOTIN vars) /\
    eval_one_phi s1 inst = NONE
    ==> eval_one_phi s2
        (inst with inst_operands :=
          update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs`
  >- (irule eval_one_phi_none_empty_update >> simp[])
  >- (
    Cases_on `t`
    >- (
      rename1 `inst.inst_outputs = [out]` >>
      Cases_on `resolve_phi pred_lbl inst.inst_operands`
      >- (
        mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`inst`,`vars`,`out`]
            eval_one_phi_backward_resolve_NONE) >>
        simp[])
      >- (
        rename1 `resolve_phi pred_lbl inst.inst_operands = SOME val_op` >>
        Cases_on `eval_operand val_op s1`
        >- (
          mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`inst`,`vars`,`out`,`val_op`]
              eval_one_phi_backward_resolve_SOME_eval_NONE) >>
          simp[])
        >- (
          gvs[eval_one_phi_def, AllCaseEqs()])))
    >- (irule eval_one_phi_none_multi_update >> simp[]))
QED

(* v2: Same as eval_one_phi_backward_NONE but WITHOUT new_v NOTIN vars in
   the FLOOKUP precondition. The NOTIN condition is unprovable for
   forwarded vars when vars = COMPL(set(fn_all_vars)). *)
(* v2: Same as eval_one_phi_backward_resolve_SOME_eval_NONE but without
   new_v NOTIN vars in the FLOOKUP precondition. Uses the FLOOKUP
   precondition directly for the ALOOKUP=SOME case instead of
   execution_equiv_FLOOKUP_vars. *)
Theorem eval_one_phi_backward_resolve_SOME_eval_NONE_v2[local]:
  !s1 s2 pred_lbl split_lbl var_repls inst vars out val_op.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    resolve_phi pred_lbl inst.inst_operands = SOME val_op /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig) /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==> orig NOTIN vars) /\
    eval_operand val_op s1 = NONE ==>
    eval_one_phi s2
        (inst with inst_operands :=
          update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`pred_lbl`, `split_lbl`, `var_repls`,
             `inst.inst_operands`, `val_op`]
      resolve_phi_update_phi_ops_match) >>
  simp[] >> strip_tac >>
  simp[eval_one_phi_def, instruction_accfupds] >>
  Cases_on `val_op` >>
  gvs[eval_operand_def, AllCaseEqs(), lookup_var_def]
  >- (
    (* Var case: first remaining after Lit auto-closes *)
    Cases_on `ALOOKUP var_repls s` >>
    gvs[eval_operand_def, lookup_var_def] >>
    imp_res_tac execution_equiv_FLOOKUP_vars >> gvs[])
  >- (
    (* Label case *)
    `s1.vs_labels = s2.vs_labels` by
      (qpat_x_assum `execution_equiv vars s1 s2` mp_tac >>
       simp[stateEquivTheory.execution_equiv_def]) >>
    gvs[])
QED

Theorem eval_one_phi_backward_NONE_v2[local]:
  !s1 s2 pred_lbl split_lbl var_repls inst vars.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    inst.inst_opcode = PHI /\
    resolve_phi split_lbl inst.inst_operands = NONE /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig) /\
    (!orig. resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==> orig NOTIN vars) /\
    eval_one_phi s1 inst = NONE
    ==> eval_one_phi s2
        (inst with inst_operands :=
          update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs`
  >- (irule eval_one_phi_none_empty_update >> simp[])
  >- (
    Cases_on `t`
    >- (
      rename1 `inst.inst_outputs = [out]` >>
      Cases_on `resolve_phi pred_lbl inst.inst_operands`
      >- (
        mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`inst`,`vars`,`out`]
            eval_one_phi_backward_resolve_NONE) >>
        simp[])
      >- (
        rename1 `resolve_phi pred_lbl inst.inst_operands = SOME val_op` >>
        Cases_on `eval_operand val_op s1`
        >- (
          mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`inst`,`vars`,`out`,`val_op`]
              eval_one_phi_backward_resolve_SOME_eval_NONE_v2) >>
          simp[])
        >- (
          gvs[eval_one_phi_def, AllCaseEqs()])))
    >- (irule eval_one_phi_none_multi_update >> simp[]))
QED
(* Backward direction: if LHS eval_phis fails on original instructions,
   RHS eval_phis also fails on updated instructions.
   Contrapositive of eval_phis_update_phis_for_split_forwarded. *)
Theorem eval_phis_update_phis_for_split_backward[local]:
  !s1 s2 pred_lbl split_lbl var_repls insts vars e1.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
       resolve_phi split_lbl inst.inst_operands = NONE) /\
    (!inst orig. MEM inst insts /\ inst.inst_opcode = PHI /\
       resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig /\
         new_v NOTIN vars) /\
    (!inst orig. MEM inst insts /\ inst.inst_opcode = PHI /\
       resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==>
       orig NOTIN vars) /\
    eval_phis s1 insts = Error e1
    ==> ?e2. eval_phis s2
         (MAP (\inst. if inst.inst_opcode <> PHI then inst
           else inst with inst_operands :=
             update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands)
           insts) = Error e2
Proof
  qid_spec_tac `e1` >>
  Induct_on `insts` >> rpt gen_tac >> strip_tac
  >- (gvs[eval_phis_def]) >>
  qpat_x_assum `eval_phis s1 (h::insts) = Error e1` mp_tac >>
  PURE_ONCE_REWRITE_TAC[eval_phis_def] >>
  IF_CASES_TAC
  >- (
    (* h is not PHI: eval_phis returns OK s1, contradicting Error e1 *)
    simp[]) >>
  (* h is PHI *)
  simp[] >>
  Cases_on `eval_one_phi s1 h` >> gvs[exec_result_distinct]
  >- (
    (* eval_one_phi s1 h = NONE: backward lemma gives eval_one_phi s2 h' = NONE *)
    strip_tac >>
    mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`h`,`vars`]
        eval_one_phi_backward_NONE) >>
    impl_tac >- (
      rpt conj_tac >- simp[] >- simp[] >- simp[] >- simp[] >- metis_tac[] >-
      metis_tac[] >- metis_tac[] >- simp[]) >>
    strip_tac >>
    PURE_ONCE_REWRITE_TAC[eval_phis_def] >> simp[])
  >- (
    (* eval_one_phi s1 h = SOME (out,val): forward lemma gives eval_one_phi s2 h' = SOME *)
    PairCases_on `x` >> gvs[] >>
    imp_res_tac eval_one_phi_imp_outputs >> gvs[] >>
    Cases_on `eval_phis s1 insts` >> gvs[exec_result_distinct] >>
    strip_tac >>
    mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`h`,`x0`,`x1`]
        eval_one_phi_forwarded_resolve) >>
    impl_tac >- (
      rpt conj_tac >- simp[] >- simp[] >- simp[] >- simp[] >- simp[] >-
      metis_tac[] >- simp[] >- metis_tac[] >- metis_tac[]) >>
    strip_tac >>
    PURE_ONCE_REWRITE_TAC[eval_phis_def] >> simp[] >>
    first_x_assum (qspecl_then
      [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`vars`,`s`] mp_tac) >>
    impl_tac >- (rpt conj_tac >- simp[] >- simp[] >- simp[] >- simp[] >- simp[] >-
      metis_tac[] >- metis_tac[] >- metis_tac[] >- simp[]) >>
    strip_tac >> simp[])
QED

(* v2: Same as eval_phis_update_phis_for_split_backward but WITHOUT
   new_v NOTIN vars in the FLOOKUP precondition. *)
Theorem eval_phis_update_phis_for_split_backward_v2[local]:
  !s1 s2 pred_lbl split_lbl var_repls insts vars e1.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = SOME pred_lbl /\
    s2.vs_prev_bb = SOME split_lbl /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==>
       resolve_phi split_lbl inst.inst_operands = NONE) /\
    (!inst orig. MEM inst insts /\ inst.inst_opcode = PHI /\
       resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP s2.vs_vars new_v = FLOOKUP s1.vs_vars orig) /\
    (!inst orig. MEM inst insts /\ inst.inst_opcode = PHI /\
       resolve_phi pred_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==>
       orig NOTIN vars) /\
    eval_phis s1 insts = Error e1
    ==> ?e2. eval_phis s2
         (MAP (\inst. if inst.inst_opcode <> PHI then inst
           else inst with inst_operands :=
             update_phi_ops pred_lbl split_lbl var_repls inst.inst_operands)
           insts) = Error e2
Proof
  qid_spec_tac `e1` >>
  Induct_on `insts` >> rpt gen_tac >> strip_tac
  >- (gvs[eval_phis_def]) >>
  qpat_x_assum `eval_phis s1 (h::insts) = Error e1` mp_tac >>
  PURE_ONCE_REWRITE_TAC[eval_phis_def] >>
  IF_CASES_TAC
  >- (
    (* h is not PHI: eval_phis returns OK s1, contradicting Error e1 *)
    simp[]) >>
  (* h is PHI *)
  simp[] >>
  Cases_on `eval_one_phi s1 h` >> gvs[exec_result_distinct]
  >- (
    (* eval_one_phi s1 h = NONE: backward lemma gives eval_one_phi s2 h' = NONE *)
    strip_tac >>
    mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`h`,`vars`]
        eval_one_phi_backward_NONE_v2) >>
    impl_tac >- (
      rpt conj_tac
      >- simp[]
      >- simp[]
      >- simp[]
      >- simp[]
      >- metis_tac[]
      >- metis_tac[]
      >- metis_tac[]
      >- simp[]) >>
    strip_tac >>
    PURE_ONCE_REWRITE_TAC[eval_phis_def] >> simp[])
  >- (
    (* eval_one_phi s1 h = SOME (out,val): forward lemma gives eval_one_phi s2 h' = SOME *)
    PairCases_on `x` >> gvs[] >>
    imp_res_tac eval_one_phi_imp_outputs >> gvs[] >>
    Cases_on `eval_phis s1 insts` >> gvs[exec_result_distinct] >>
    strip_tac >>
    mp_tac (Q.SPECL [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`h`,`x0`,`x1`]
        eval_one_phi_forwarded_resolve_v2) >>
    impl_tac >- (
      rpt conj_tac
      >- simp[]
      >- simp[]
      >- simp[]
      >- simp[]
      >- simp[]
      >- metis_tac[]
      >- simp[]
      >- metis_tac[]
      >- metis_tac[]) >>
    strip_tac >>
    PURE_ONCE_REWRITE_TAC[eval_phis_def] >> simp[] >>
    first_x_assum (qspecl_then
      [`s1`,`s2`,`pred_lbl`,`split_lbl`,`var_repls`,`vars`,`s`] mp_tac) >>
    impl_tac >- (
      rpt conj_tac
      >- simp[]
      >- simp[]
      >- simp[]
      >- simp[]
      >- simp[]
      >- metis_tac[]
      >- metis_tac[]
      >- metis_tac[]
      >- simp[]) >>
    strip_tac >> simp[])
QED

(*
 * The split block (ASSIGN + JMP only) returns OK or Error, never
 * Halt/Abort/IntRet, provided the initial state is not halted.
 *)
(* Helper: when ~EVERY FDOM, split block errors *)
Theorem split_block_not_fdom_error[local]:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx s.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    s.vs_current_bb = split_bb.bb_label /\
    (!v. MEM v (nub (phi_vars_needing_forward
             pred_bb.bb_label pred_bb target_bb.bb_instructions)) ==>
       !w. v <> STRCAT (STRCAT
             (split_block_name pred_bb.bb_label target_bb.bb_label)
             "_fwd_") w) /\
    ~EVERY (\v. v IN FDOM s.vs_vars)
      (nub (phi_vars_needing_forward
         pred_bb.bb_label pred_bb target_bb.bb_instructions)) ==>
    ?e. exec_block fuel ctx split_bb s = Error e
Proof
  rpt strip_tac >>
  fs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >>
  fs[build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  mp_tac (Q.SPECL [
    `nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
            target_bb.bb_instructions)`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `id_base`] fwd_assigns_not_fdom_error) >>
  simp[listTheory.all_distinct_nub] >>
  disch_then (qspecl_then [`[]`,
    `[<|inst_id := id_base +
          LENGTH (nub (phi_vars_needing_forward pred_bb.bb_label
                   pred_bb target_bb.bb_instructions));
        inst_opcode := JMP;
        inst_operands := [Label target_bb.bb_label];
        inst_outputs := []|>]`,
    `fuel`, `ctx`, `s`, `split_bb`, `e`] mp_tac) >>
  simp[listTheory.MEM_nub] >>
  disch_then irule >> gvs[]
QED

Theorem split_block_result_cases:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx s.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    s.vs_current_bb = split_bb.bb_label /\
    (!v. MEM v (nub (phi_vars_needing_forward
             pred_bb.bb_label pred_bb target_bb.bb_instructions)) ==>
       !w. v <> STRCAT (STRCAT
             (split_block_name pred_bb.bb_label target_bb.bb_label)
             "_fwd_") w) ==>
    (?v. exec_block fuel ctx split_bb s = OK v /\ ~v.vs_halted /\
         v.vs_current_bb = target_bb.bb_label /\
         v.vs_inst_idx = 0) \/
    (?e. exec_block fuel ctx split_bb s = Error e)
Proof
  rpt strip_tac >>
  Cases_on `EVERY (\v. v IN FDOM s.vs_vars)
              (nub (phi_vars_needing_forward
                pred_bb.bb_label pred_bb target_bb.bb_instructions))`
  >- (
    DISJ1_TAC >>
    mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
      `var_repls`, `fuel`, `ctx`, `s`] run_split_block) >>
    (impl_tac >- fs[listTheory.EVERY_MEM, listTheory.MEM_nub]) >>
    strip_tac >> qexists_tac `v` >> simp[])
  >- (
    DISJ2_TAC >>
    mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
      `var_repls`, `fuel`, `ctx`, `s`] split_block_not_fdom_error) >>
    simp[] >>
    disch_then match_mp_tac >>
    fs[combinTheory.o_DEF, listTheory.NOT_EVERY])
QED

(* lift_result (OK v1) r implies r = OK v2 with R_ok v1 v2 *)
Theorem lift_result_OK_elim[local]:
  !R_ok R_term R_abort v1 r.
    lift_result R_ok R_term R_abort (OK v1) r ==> ?v2. r = OK v2 /\ R_ok v1 v2
Proof
  Cases_on `r` >> simp[stateEquivTheory.lift_result_def]
QED

(* result_equiv with larger vars is implied by result_equiv with smaller vars.
   Direct corollary: COMPL X SUBSET UNIV, so result_equiv (COMPL X) ==> result_equiv UNIV *)
Theorem result_equiv_weaken_to_UNIV[local]:
  !vars r1 r2. result_equiv vars r1 r2 ==> result_equiv UNIV r1 r2
Proof
  rpt strip_tac >>
  irule stateEquivPropsTheory.result_equiv_subset >>
  qexists_tac `vars` >> simp[pred_setTheory.SUBSET_UNIV]
QED

(* Terminal 3step: when run_block_entry on target_bb gives a terminal result
   (anything except OK-not-halted), and we have the 3step setup,
   the modified function is result_equiv UNIV with the original. *)
Theorem insert_split_3step_terminal[local]:
  !func func' subst_pred split_bb updated_target
   pred_lbl split_lbl target_lbl f f1 f2 ctx s v1 v_split vars r_target.
    lookup_block pred_lbl func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_lbl func'.fn_blocks = SOME updated_target /\
    s.vs_current_bb = pred_lbl /\
    run_block_entry f1 ctx subst_pred s = OK v1 /\ f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\ v1.vs_current_bb = split_lbl /\
    run_block_entry f2 ctx split_bb v1 = OK v_split /\ f2 <= SUC f /\
    ~v_split.vs_halted /\ v_split.vs_current_bb = target_lbl /\
    result_equiv vars r_target (run_block_entry f ctx updated_target v_split) /\
    (!v'. r_target = OK v' ==> v'.vs_halted) ==>
    result_equiv UNIV
      (case r_target of
         OK s'' => if s''.vs_halted then Halt s''
                   else run_blocks f ctx func s''
       | Halt v => Halt v | Abort a s' => Abort a s'
       | IntRet vals s' => IntRet vals s' | Error e => Error e)
      (run_blocks (SUC (SUC (SUC f))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func'`, `subst_pred`, `split_bb`, `updated_target`,
    `pred_lbl`, `split_lbl`, `target_lbl`,
    `f`, `f1`, `f2`, `ctx`, `s`, `v1`, `v_split`]
    run_function_3step) >>
  simp[] >> strip_tac >>
  `?r2. run_block_entry f ctx updated_target v_split = r2` by metis_tac[] >>
  Cases_on `r_target` >> Cases_on `r2` >>
  fs[stateEquivPropsTheory.result_equiv_is_lift_result,
     stateEquivTheory.lift_result_def,
     stateEquivTheory.state_equiv_def,
     stateEquivTheory.execution_equiv_def]
QED

(* Specialized versions of insert_split_3step_terminal for each constructor.
   These avoid the case-expression in the conclusion so irule can match. *)

Theorem insert_split_3step_ok_halted[local]:
  !func func' subst_pred split_bb updated_target
   pred_lbl split_lbl target_lbl f f1 f2 ctx s v1 v_split vars s''.
    lookup_block pred_lbl func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_lbl func'.fn_blocks = SOME updated_target /\
    s.vs_current_bb = pred_lbl /\
    run_block_entry f1 ctx subst_pred s = OK v1 /\ f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\ v1.vs_current_bb = split_lbl /\
    run_block_entry f2 ctx split_bb v1 = OK v_split /\ f2 <= SUC f /\
    ~v_split.vs_halted /\ v_split.vs_current_bb = target_lbl /\
    result_equiv vars (OK s'') (run_block_entry f ctx updated_target v_split) /\
    s''.vs_halted ==>
    result_equiv UNIV (Halt s'')
      (run_blocks (SUC (SUC (SUC f))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `func'`, `subst_pred`, `split_bb`, `updated_target`,
    `pred_lbl`, `split_lbl`, `target_lbl`,
    `f`, `f1`, `f2`, `ctx`, `s`, `v1`, `v_split`, `vars`, `OK s''`]
    insert_split_3step_terminal) >>
  simp[stateEquivPropsTheory.result_equiv_is_lift_result,
       stateEquivTheory.lift_result_def]
QED

Theorem insert_split_3step_halt[local]:
  !func func' subst_pred split_bb updated_target
   pred_lbl split_lbl target_lbl f f1 f2 ctx s v1 v_split vars v.
    lookup_block pred_lbl func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_lbl func'.fn_blocks = SOME updated_target /\
    s.vs_current_bb = pred_lbl /\
    run_block_entry f1 ctx subst_pred s = OK v1 /\ f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\ v1.vs_current_bb = split_lbl /\
    run_block_entry f2 ctx split_bb v1 = OK v_split /\ f2 <= SUC f /\
    ~v_split.vs_halted /\ v_split.vs_current_bb = target_lbl /\
    result_equiv vars (Halt v) (run_block_entry f ctx updated_target v_split) ==>
    result_equiv UNIV (Halt v)
      (run_blocks (SUC (SUC (SUC f))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `func'`, `subst_pred`, `split_bb`, `updated_target`,
    `pred_lbl`, `split_lbl`, `target_lbl`,
    `f`, `f1`, `f2`, `ctx`, `s`, `v1`, `v_split`, `vars`, `Halt v`]
    insert_split_3step_terminal) >>
  simp[stateEquivPropsTheory.result_equiv_is_lift_result,
       stateEquivTheory.lift_result_def]
QED

Theorem insert_split_3step_abort[local]:
  !func func' subst_pred split_bb updated_target
   pred_lbl split_lbl target_lbl f f1 f2 ctx s v1 v_split vars a v.
    lookup_block pred_lbl func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_lbl func'.fn_blocks = SOME updated_target /\
    s.vs_current_bb = pred_lbl /\
    run_block_entry f1 ctx subst_pred s = OK v1 /\ f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\ v1.vs_current_bb = split_lbl /\
    run_block_entry f2 ctx split_bb v1 = OK v_split /\ f2 <= SUC f /\
    ~v_split.vs_halted /\ v_split.vs_current_bb = target_lbl /\
    result_equiv vars (Abort a v) (run_block_entry f ctx updated_target v_split) ==>
    result_equiv UNIV (Abort a v)
      (run_blocks (SUC (SUC (SUC f))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `func'`, `subst_pred`, `split_bb`, `updated_target`,
    `pred_lbl`, `split_lbl`, `target_lbl`,
    `f`, `f1`, `f2`, `ctx`, `s`, `v1`, `v_split`, `vars`, `Abort a v`]
    insert_split_3step_terminal) >>
  simp[stateEquivPropsTheory.result_equiv_is_lift_result,
       stateEquivTheory.lift_result_def]
QED

Theorem insert_split_3step_intret[local]:
  !func func' subst_pred split_bb updated_target
   pred_lbl split_lbl target_lbl f f1 f2 ctx s v1 v_split vals v.
    lookup_block pred_lbl func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_lbl func'.fn_blocks = SOME updated_target /\
    s.vs_current_bb = pred_lbl /\
    run_block_entry f1 ctx subst_pred s = OK v1 /\ f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\ v1.vs_current_bb = split_lbl /\
    run_block_entry f2 ctx split_bb v1 = OK v_split /\ f2 <= SUC f /\
    ~v_split.vs_halted /\ v_split.vs_current_bb = target_lbl /\
    result_equiv vars (IntRet vals v) (run_block_entry f ctx updated_target v_split) ==>
    result_equiv UNIV (IntRet vals v)
      (run_blocks (SUC (SUC (SUC f))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `func'`, `subst_pred`, `split_bb`, `updated_target`,
    `pred_lbl`, `split_lbl`, `target_lbl`,
    `f`, `f1`, `f2`, `ctx`, `s`, `v1`, `v_split`, `vars`, `IntRet vals v`]
    insert_split_3step_terminal) >>
  simp[stateEquivPropsTheory.result_equiv_is_lift_result,
       stateEquivTheory.lift_result_def]
QED

(* Error case: same pattern as halt/abort/intret but with Error result *)
Theorem insert_split_3step_error[local]:
  !func func' subst_pred split_bb updated_target
   pred_lbl split_lbl target_lbl f f1 f2 ctx s v1 v_split vars e.
    lookup_block pred_lbl func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_lbl func'.fn_blocks = SOME updated_target /\
    s.vs_current_bb = pred_lbl /\
    run_block_entry f1 ctx subst_pred s = OK v1 /\ f1 <= SUC (SUC f) /\
    ~v1.vs_halted /\ v1.vs_current_bb = split_lbl /\
    run_block_entry f2 ctx split_bb v1 = OK v_split /\ f2 <= SUC f /\
    ~v_split.vs_halted /\ v_split.vs_current_bb = target_lbl /\
    result_equiv vars (Error e) (run_block_entry f ctx updated_target v_split) ==>
    result_equiv UNIV (Error e)
      (run_blocks (SUC (SUC (SUC f))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `func'`, `subst_pred`, `split_bb`, `updated_target`,
    `pred_lbl`, `split_lbl`, `target_lbl`,
    `f`, `f1`, `f2`, `ctx`, `s`, `v1`, `v_split`, `vars`, `Error e`]
    insert_split_3step_terminal) >>
  simp[stateEquivPropsTheory.result_equiv_is_lift_result,
       stateEquivTheory.lift_result_def]
QED

(* Helper: When split_bb = Error, the 2step gives Error and result_equiv UNIV holds *)
Theorem error_case_split_bb_error[local]:
  !func' subst_pred split_bb pred_lbl split_lbl m ctx s v1 e e'.
    lookup_block pred_lbl func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    s.vs_current_bb = pred_lbl /\
    run_block_entry (SUC m) ctx subst_pred s = OK (v1 with vs_current_bb := split_lbl) /\
    ~v1.vs_halted /\
    run_block_entry (SUC m) ctx split_bb (v1 with vs_current_bb := split_lbl) = Error e' ==>
    result_equiv UNIV (Error e)
      (run_blocks (SUC (SUC (SUC m))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func'`, `subst_pred`, `split_bb`,
    `pred_lbl`, `split_lbl`,
    `SUC m`, `ctx`, `s`,
    `v1 with vs_current_bb := split_lbl`]
    run_function_2step) >>
  simp[] >>
  strip_tac >> fs[stateEquivTheory.result_equiv_def]
QED

(* bb_well_formed preserved by MAP with opcode-preserving function *)
Theorem bb_well_formed_map_opcode_preserving[local]:
  !f bb. (!inst. (f inst).inst_opcode = inst.inst_opcode) ==>
    bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions := MAP f bb.bb_instructions)
Proof
  rw[bb_well_formed_def] >>
  `!n. n < LENGTH bb.bb_instructions ==>
    (MAP f bb.bb_instructions)❲n❳.inst_opcode =
    bb.bb_instructions❲n❳.inst_opcode` by
    simp[listTheory.EL_MAP] >>
  res_tac >> fs[]
QED

(* bb_well_formed preserved by subst_label_terminator *)
Theorem bb_well_formed_subst_label_terminator[local]:
  !old_lbl new_lbl bb.
    bb_well_formed bb ==>
    bb_well_formed (subst_label_terminator old_lbl new_lbl bb)
Proof
  rw[cfgTransformTheory.subst_label_terminator_def] >>
  irule bb_well_formed_map_opcode_preserving >> rw[] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  simp[cfgTransformTheory.subst_label_inst_def]
QED

(* bb_well_formed preserved by update_phis_for_split *)
Theorem bb_well_formed_update_phis[local]:
  !old_lbl new_lbl var_repls bb.
    bb_well_formed bb ==>
    bb_well_formed (update_phis_for_split old_lbl new_lbl var_repls bb)
Proof
  rw[cfgNormDefsTheory.update_phis_for_split_def] >>
  irule bb_well_formed_map_opcode_preserving >> rw[]
QED

(* Helper: if any instruction in a well-formed block is PHI, then instruction 0 is PHI *)
Theorem wf_block_phi_implies_first_phi[local]:
  !bb i.
    bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
    bb.bb_instructions❲i❳.inst_opcode = PHI ==>
    bb.bb_instructions❲0❳.inst_opcode = PHI
Proof
  rpt strip_tac >>
  Cases_on `i = 0` >> simp[] >>
  mp_tac (Q.SPECL [`bb`, `i`, `0`] phi_before_non_phi) >> simp[]
QED

(* exec_block OK from inst_idx=0 on a well-formed block implies no PHIs *)
Theorem exec_block_OK_imp_no_phis[local]:
  !fuel ctx bb s v.
    bb_well_formed bb /\
    exec_block fuel ctx bb s = OK v /\
    s.vs_inst_idx = 0 ==>
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions
Proof
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  strip_tac >>
  spose_not_then strip_assume_tac >>
  fs[listTheory.NOT_EVERY_EXISTS_FIRST] >>
  imp_res_tac wf_block_phi_implies_first_phi >>
  `0 < LENGTH bb.bb_instructions` by fs[] >>
  `get_instruction bb 0 = SOME (EL 0 bb.bb_instructions)` by simp[get_instruction_def] >>
  `step_inst fuel ctx (EL 0 bb.bb_instructions) s = Error "phi outside prefix"`
    by (irule step_inst_phi_error >> simp[]) >>
  imp_res_tac exec_block_first_step_error >>
  pop_assum (qspecl_then [`bb`] mp_tac) >>
  simp[] >> strip_tac >>
  fs[]
QED

(* run_block_entry = run_block_non_phis when exec_block OK from idx=0 on well-formed block *)
Theorem run_block_entry_eq_exec_block_OK[local]:
  !fuel ctx bb s v.
    bb_well_formed bb /\
    exec_block fuel ctx bb s = OK v /\
    s.vs_inst_idx = 0 ==>
    run_block_entry fuel ctx bb s = OK v
Proof
  rpt strip_tac >>
  imp_res_tac exec_block_OK_imp_no_phis >>
  imp_res_tac run_block_no_phis_eq_exec_block >>
  fs[venom_state_component_equality]
QED

(* subst_label_inst preserves inst_opcode *)
Theorem subst_label_inst_opcode[local]:
  !old_lbl new_lbl inst.
    (subst_label_inst old_lbl new_lbl inst).inst_opcode = inst.inst_opcode
Proof
  rw[cfgTransformTheory.subst_label_inst_def]
QED

(* Helper: conditional subst preserves inst_opcode *)
Theorem subst_label_terminator_inst_opcode[local]:
  !old_lbl new_lbl inst.
    (if is_terminator inst.inst_opcode then subst_label_inst old_lbl new_lbl inst
     else inst).inst_opcode = inst.inst_opcode
Proof
  Cases_on `is_terminator inst.inst_opcode` >>
  simp[subst_label_inst_opcode]
QED

(* subst_label_terminator preserves no-PHI property *)
Theorem subst_label_terminator_no_phis[local]:
  !old_lbl new_lbl bb.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (subst_label_terminator old_lbl new_lbl bb).bb_instructions
Proof
  simp[cfgTransformTheory.subst_label_terminator_def,
       listTheory.EVERY_MAP,
       subst_label_terminator_inst_opcode]
QED

(* Fuel monotonicity lifted to run_block_entry for no-PHI blocks *)
Theorem run_block_entry_fuel_mono_no_phis[local]:
  !s bb fuel ctx v.
    s.vs_inst_idx = 0 /\
    bb_well_formed bb /\
    exec_block fuel ctx bb s = OK v /\
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
    !f. f >= fuel ==> run_block_entry f ctx bb s = OK v
Proof
  rpt strip_tac >>
  `exec_block f ctx bb s = OK v` by (
    drule (cj 2 venomExecProofsTheory.fuel_mono) >>
    simp[]) >>
  irule run_block_entry_eq_exec_block_OK >> simp[]
QED

(* Boundary lemma: run_block_entry-level equivalence for target_bb vs updated_target.
   Lifts split_block_forwarded_result_equiv from exec_block-level to run_block_entry-level.
   Key: run_block_entry = eval_phis then exec_block from phi_prefix_length.
   Three components all equivalent: eval_phis (by v2 forward/backward),
   phi_prefix_length (by update_phis_for_split eq),
   exec_block from that index (by non_phi_suffix + execution_equiv). *)

Theorem eval_phis_preserves_halted[local]:
  !s insts s'. eval_phis s insts = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> fs[eval_phis_def])
  >> rpt strip_tac >> fs[eval_phis_def]
  >> Cases_on `h.inst_opcode = PHI` >> fs[] >> rfs[]
  >> Cases_on `eval_one_phi s h` >> fs[]
  >> PairCases_on `x` >> fs[]
  >> Cases_on `eval_phis s insts` >> fs[]
  >> `v.vs_halted = s.vs_halted`
     by (qsuff_tac `∀s''. eval_phis s insts = OK s'' ⇒ s''.vs_halted = s.vs_halted`
         >- metis_tac[] >> metis_tac[])
  >> fs[update_var_def]
  >> `s' = v with vs_vars := v.vs_vars⟨x0 ↦ x1⟩` by metis_tac[]
  >> fs[]
QED

(* Helper: phi_prefix_length of update_phis_for_split = phi_prefix_length of original block.
   Proved standalone to avoid `by` block abbreviation issues. *)
Theorem phi_prefix_length_update_phis_eq[local]:
  !target_bb pred_lbl split_lbl var_repls.
    phi_prefix_length
      (update_phis_for_split pred_lbl split_lbl var_repls target_bb).bb_instructions =
    phi_prefix_length target_bb.bb_instructions
Proof
  simp[phi_prefix_length_update_phis_for_split_eq]
QED

Theorem phi_prefix_length_non_phi_suffix[local]:
  !bb. bb_well_formed bb ==>
    !k. phi_prefix_length bb.bb_instructions <= k /\
        k < LENGTH bb.bb_instructions ==>
        (EL k bb.bb_instructions).inst_opcode <> PHI
Proof
  metis_tac[bb_non_phi_suffix, bb_well_formed_phi_prefix_length_lt,
            phi_prefix_length_at_nonphi]
QED

Theorem execution_equiv_inst_idx_update[local]:
  !vars s1 s2 k.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (s1 with vs_inst_idx := k) (s2 with vs_inst_idx := k)
Proof
  simp[execution_equiv_def, lookup_var_def]
QED

(* Standalone lemma for the ok_case of split_block_run_block_entry_equiv.
   Extracted because the ok_case goal state exceeds 4KB when inside the
   main proof, making irule/simp fail. *)
Theorem split_block_ok_case_lem[local]:
  !target_bb func fuel2 ctx s_phi s2_phi.
    fn_inst_wf func /\ MEM target_bb func.fn_blocks /\
    bb_well_formed target_bb /\
    execution_equiv (COMPL (set (fn_all_vars func))) s_phi s2_phi /\
    s2_phi.vs_current_bb = s_phi.vs_current_bb /\
    s2_phi.vs_inst_idx = s_phi.vs_inst_idx ==>
    result_equiv (COMPL (set (fn_all_vars func)))
      (exec_block fuel2 ctx target_bb
         (s_phi with vs_inst_idx := phi_prefix_length target_bb.bb_instructions))
      (exec_block fuel2 ctx target_bb
         (s2_phi with vs_inst_idx := phi_prefix_length target_bb.bb_instructions))
Proof
  rpt strip_tac >>
  irule run_block_non_phi_result_equiv >>
  simp[execution_equiv_inst_idx_update, phi_prefix_length_non_phi_suffix,
       phi_prefix_length_le]
QED

Theorem split_block_error_case[local]:
  !v1 v_split pred_bb_lbl split_lbl var_repls target_bb updated_target
     vars fuel2 ctx e.
    execution_equiv vars v1 v_split /\
    v1.vs_prev_bb = SOME pred_bb_lbl /\
    v_split.vs_prev_bb = SOME split_lbl /\
    v1.vs_current_bb = v_split.vs_current_bb /\
    v1.vs_inst_idx = v_split.vs_inst_idx /\
    (!inst. MEM inst target_bb.bb_instructions /\ inst.inst_opcode = PHI ==>
       resolve_phi split_lbl inst.inst_operands = NONE) /\
    (!inst orig. MEM inst target_bb.bb_instructions /\ inst.inst_opcode = PHI /\
       resolve_phi pred_bb_lbl inst.inst_operands = SOME (Var orig) ==>
       !new_v. ALOOKUP var_repls orig = SOME new_v ==>
         FLOOKUP v_split.vs_vars new_v = FLOOKUP v1.vs_vars orig) /\
    (!inst orig. MEM inst target_bb.bb_instructions /\ inst.inst_opcode = PHI /\
       resolve_phi pred_bb_lbl inst.inst_operands = SOME (Var orig) /\
       ALOOKUP var_repls orig = NONE ==>
       orig NOTIN vars) /\
    updated_target =
      update_phis_for_split pred_bb_lbl split_lbl var_repls target_bb /\
    eval_phis v1 target_bb.bb_instructions = Error e
    ==> ?e2. run_block_entry fuel2 ctx updated_target v_split = Error e2
Proof
  rpt gen_tac >> strip_tac >>
  `?e2. eval_phis v_split updated_target.bb_instructions = Error e2`
    by (imp_res_tac eval_phis_update_phis_for_split_backward_v2 >>
        simp[update_phis_for_split_def]) >>
  imp_res_tac run_block_entry_eval_phis_Error >>
  metis_tac[]
QED

Theorem split_block_run_block_entry_equiv[local]:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx v1 v_split func
   split_lbl.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    exec_block fuel ctx split_bb (v1 with vs_current_bb := split_lbl) =
      OK v_split /\
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    MEM target_bb func.fn_blocks /\
    ALL_DISTINCT (fn_labels func) /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    v1.vs_inst_idx = 0 /\ ~v1.vs_halted /\
    v1.vs_prev_bb = SOME pred_bb.bb_label /\
    v1.vs_current_bb = target_bb.bb_label ==>
    !fuel2. result_equiv (COMPL (set (fn_all_vars func)))
      (run_block_entry fuel2 ctx target_bb v1)
      (run_block_entry fuel2 ctx
         (update_phis_for_split pred_bb.bb_label split_lbl var_repls
            target_bb) v_split)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `updated_target =
    update_phis_for_split pred_bb.bb_label split_lbl var_repls
      target_bb` >>
  mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
    `var_repls`, `fuel`, `ctx`, `v1`, `v_split`, `func`, `split_lbl`]
    split_block_forwarded_result_equiv) >>
  impl_tac >- simp[Abbr `updated_target`] >> strip_tac >>
  qabbrev_tac `vars = COMPL (set (fn_all_vars func))` >>
  `phi_prefix_length updated_target.bb_instructions =
    phi_prefix_length target_bb.bb_instructions`
    by metis_tac[phi_prefix_length_update_phis_for_split_eq] >>
  `bb_well_formed target_bb` by
    (fs[wf_function_no_ids_def] >> metis_tac[]) >>
  `bb_well_formed updated_target` by
    metis_tac[bb_well_formed_update_phis] >>
  `!inst orig. MEM inst target_bb.bb_instructions /\ inst.inst_opcode = PHI /\
     resolve_phi pred_bb.bb_label inst.inst_operands = SOME (Var orig) ==>
     !new_v. ALOOKUP var_repls orig = SOME new_v ==>
       FLOOKUP (v_split.vs_vars) new_v = FLOOKUP (v1.vs_vars) orig` by (
    rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `!inst orig. MEM inst target_bb.bb_instructions /\ inst.inst_opcode = PHI /\
     resolve_phi pred_bb.bb_label inst.inst_operands = SOME (Var orig) /\
     ALOOKUP var_repls orig = NONE ==> orig NOTIN vars` by (
    rpt strip_tac >> imp_res_tac resolve_phi_MEM_operands >>
    fs[] >> imp_res_tac inst_operand_var_in_fn_all_vars >>
    fs[Abbr `vars`]) >>
  `!inst. MEM inst target_bb.bb_instructions /\ inst.inst_opcode = PHI ==>
     resolve_phi split_lbl inst.inst_operands = NONE` by
    metis_tac[resolve_phi_fresh_label] >>
  DISJ_CASES_TAC (Q.SPECL [`v1`, `target_bb.bb_instructions`]
                    eval_phis_ok_or_error_defs)
  >- (
    (* ok_case: eval_phis v1 target_bb.bb_instructions = OK s_phi *)
    first_x_assum strip_assume_tac >>
    rename1 `eval_phis v1 _ = OK s_phi` >>
    imp_res_tac eval_phis_preserves_inst_idx >>
    imp_res_tac eval_phis_preserves_current_bb >>
    imp_res_tac eval_phis_preserves_halted >>
    mp_tac (Q.SPECL [`s_phi`, `v1`, `v_split`, `pred_bb.bb_label`,
      `split_lbl`, `var_repls`, `target_bb.bb_instructions`, `vars`, `func`]
      (GEN_ALL eval_phis_update_phis_for_split_forwarded_v2)) >>
    impl_tac >- metis_tac[] >> strip_tac >>
    rename1 `eval_phis v_split _ = OK s2_phi` >>
    imp_res_tac eval_phis_preserves_inst_idx >>
    imp_res_tac eval_phis_preserves_current_bb >>
    imp_res_tac eval_phis_preserves_halted >>
    qpat_x_assum `split_lbl = _` SUBST_ALL_TAC >>
    `eval_phis v_split updated_target.bb_instructions = OK s2_phi` by
      simp[Abbr `updated_target`, update_phis_for_split_def] >>
    gen_tac >>
    (* Rewrite both run_block_entry → exec_block *)
    `run_block_entry fuel2 ctx target_bb v1 =
      exec_block fuel2 ctx target_bb
        (s_phi with vs_inst_idx :=
           phi_prefix_length target_bb.bb_instructions)`
      by metis_tac[run_block_entry_eval_phis_OK] >>
    `run_block_entry fuel2 ctx updated_target v_split =
      exec_block fuel2 ctx updated_target
        (s2_phi with vs_inst_idx :=
           phi_prefix_length updated_target.bb_instructions)`
      by metis_tac[run_block_entry_eval_phis_OK] >>
    qunabbrev_tac `vars` >>
    (* Substitute exec_block equalities into the goal *)
    pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
    pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
    (* Equate exec_block on updated_target with exec_block on target_bb *)
    `exec_block fuel2 ctx updated_target
        (s2_phi with vs_inst_idx :=
           phi_prefix_length updated_target.bb_instructions) =
      exec_block fuel2 ctx target_bb
        (s2_phi with vs_inst_idx :=
           phi_prefix_length target_bb.bb_instructions)`
      by metis_tac[exec_block_update_phis_from_ppl_alt] >>
    pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
    simp[phi_prefix_length_update_phis_eq] >>
    irule split_block_ok_case_lem >> simp[]
  ) >- (
    (* error_case: eval_phis v1 target_bb.bb_instructions = Error _ *)
    first_x_assum strip_assume_tac >>
    gen_tac >>
    `run_block_entry fuel2 ctx target_bb v1 = Error e`
      by metis_tac[run_block_entry_eval_phis_Error] >>
    pop_assum (ONCE_REWRITE_TAC o single) >>
    qunabbrev_tac `updated_target` >> qunabbrev_tac `vars` >>
    `?e2. run_block_entry fuel2 ctx
       (update_phis_for_split pred_bb.bb_label split_lbl var_repls target_bb)
       v_split = Error e2`
      by (irule split_block_error_case >>
          qexistsl [`e`, `pred_bb.bb_label`, `split_lbl`,
                    `target_bb`, `v1`, `var_repls`,
                    `COMPL (set (fn_all_vars func))`] >>
          simp[] >> metis_tac[pred_setTheory.IN_COMPL]) >>
    first_x_assum strip_assume_tac >>
    simp[result_equiv_def])
QED

(* bb_succs for non-empty blocks: uses LAST instruction's successors *)
Theorem bb_succs_nonempty[local]:
  !bb. bb.bb_instructions <> [] ==>
    bb_succs bb = nub (REVERSE (get_successors (LAST bb.bb_instructions)))
Proof
  rw[bb_succs_def] >> Cases_on `bb.bb_instructions` >> fs[]
QED

(* Split block's successors = [target label] *)
Theorem bb_succs_split_bb[local]:
  !pred_bb target_bb id_base split_bb var_repls.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) ==>
    bb_succs split_bb = [target_bb.bb_label]
Proof
  rw[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  simp[bb_succs_nonempty, rich_listTheory.LAST_APPEND_NOT_NIL,
       get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.nub_def]
QED

(* Split block is well-formed *)
Theorem bb_well_formed_split_bb[local]:
  !pred_bb target_bb id_base split_bb var_repls.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) ==>
    bb_well_formed split_bb
Proof
  rw[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  simp[bb_well_formed_def, rich_listTheory.LAST_APPEND,
       venomInstTheory.is_terminator_def] >>
  rpt conj_tac >-
  (rw[] >>
   imp_res_tac cfgNormSimTheory.build_forwarding_assigns_insts >>
   Cases_on `i < LENGTH fwd_insts` >-
   (fs[rich_listTheory.EL_APPEND1] >>
    `(EL i fwd_insts).inst_opcode = ASSIGN` by simp[] >>
    fs[venomInstTheory.is_terminator_def]) >>
   fs[rich_listTheory.EL_APPEND2] >>
   `i - LENGTH fwd_insts = 0` by DECIDE_TAC >>
   fs[venomInstTheory.is_terminator_def]) >>
  rw[] >>
  imp_res_tac cfgNormSimTheory.build_forwarding_assigns_insts >>
  Cases_on `j < LENGTH fwd_insts` >-
  (`(EL j fwd_insts).inst_opcode = ASSIGN` by simp[] >>
   fs[rich_listTheory.EL_APPEND1]) >>
  `j = LENGTH fwd_insts` by DECIDE_TAC >>
  fs[rich_listTheory.EL_APPEND2]
QED

(* Forwarding assigns are all well-formed (ASSIGN with 1 operand, 1 output) *)
Theorem build_forwarding_assigns_inst_wf[local]:
  !split_label id_base vars repls insts.
    build_forwarding_assigns split_label id_base vars = (repls, insts) ==>
    EVERY inst_wf insts
Proof
  rpt strip_tac >>
  imp_res_tac cfgNormSimTheory.build_forwarding_assigns_insts >>
  rw[listTheory.EVERY_EL, venomWfTheory.inst_wf_def]
QED

(* Split block instructions are all well-formed: forwarding assigns + JMP *)
Theorem build_split_block_inst_wf[local]:
  !pred_bb target_bb id_base split_bb var_repls.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) ==>
    EVERY inst_wf split_bb.bb_instructions
Proof
  rpt strip_tac >>
  qpat_x_assum `build_split_block _ _ _ = _` mp_tac >>
  rw[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  imp_res_tac build_forwarding_assigns_inst_wf >>
  rw[listTheory.EVERY_APPEND, venomWfTheory.inst_wf_def]
QED

(* Combined: exec_block OK on split_bb implies v.vs_current_bb = target *)
Theorem exec_block_split_bb_current_bb[local]:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx s v.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    s.vs_inst_idx <= LENGTH split_bb.bb_instructions /\
    exec_block fuel ctx split_bb s = OK v ==>
    v.vs_current_bb = target_bb.bb_label
Proof
  rpt strip_tac >>
  `bb_well_formed split_bb` by metis_tac[bb_well_formed_split_bb] >>
  `bb_succs split_bb = [target_bb.bb_label]` by metis_tac[bb_succs_split_bb] >>
  `split_bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  imp_res_tac bb_well_formed_no_early_terminator >>
  `EVERY inst_wf split_bb.bb_instructions` by metis_tac[build_split_block_inst_wf] >>
  imp_res_tac venomExecProofsTheory.exec_block_current_bb_in_succs >>
  metis_tac[listTheory.MEM]
QED

(* Standalone lemma: exec_block on split_bb with state having inst_idx=0
   gives current_bb = target. Extracted from error_case_split_bb_ok to avoid
   by-block batch mode failure. *)
Theorem exec_block_split_bb_current_bb_from_idx0[local]:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx v1 sbn v.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    v1.vs_inst_idx = 0 /\
    exec_block fuel ctx split_bb (v1 with vs_current_bb := sbn) = OK v ==>
    v.vs_current_bb = target_bb.bb_label
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`, `var_repls`,
    `fuel`, `ctx`, `v1 with vs_current_bb := sbn`, `v`]
    exec_block_split_bb_current_bb) >>
  simp[venom_state_component_equality] >>
  decide_tac
QED

(* Helper: When split_bb = OK, apply terminal 3step *)
Theorem error_case_split_bb_ok[local]:
  !func func' pred_bb target_bb id_base split_bb var_repls
   subst_pred updated_target split_lbl m ctx s v1 v e.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT (split_block_name pred_bb.bb_label
                  target_bb.bb_label) "_fwd_") var)
                (fn_all_vars func)) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_lbl /\
    subst_pred = subst_label_terminator target_bb.bb_label split_lbl pred_bb /\
    updated_target = update_phis_for_split pred_bb.bb_label split_lbl
                       var_repls target_bb /\
    lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target /\
    s.vs_current_bb = pred_bb.bb_label /\ s.vs_inst_idx = 0 /\
    exec_block (SUC m) ctx subst_pred s =
      OK (v1 with vs_current_bb := split_lbl) /\
    ~v1.vs_halted /\ v1.vs_inst_idx = 0 /\
    v1.vs_prev_bb = SOME pred_bb.bb_label /\
    v1.vs_current_bb = target_bb.bb_label /\
    exec_block (SUC m) ctx split_bb (v1 with vs_current_bb := split_lbl) = OK v /\
    run_block_entry m ctx target_bb v1 = Error e /\
    (!v. MEM v (nub (phi_vars_needing_forward pred_bb.bb_label
           pred_bb target_bb.bb_instructions)) ==>
       !w. v <> STRCAT (STRCAT split_lbl "_fwd_") w) ==>
    result_equiv UNIV (Error e)
      (run_blocks (SUC (SUC (SUC m))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  `v.vs_inst_idx = 0`
    by metis_tac[venomExecPropsTheory.exec_block_OK_inst_idx_0] >>
  qpat_x_assum `split_lbl = _` SUBST_ALL_TAC >>
  qabbrev_tac `sbn = split_block_name pred_bb.bb_label target_bb.bb_label` >>
  (* Bridge exec_block to run_block_entry for subst_pred and split_bb *)
  `bb_well_formed pred_bb` by fs[wf_function_no_ids_def] >>
  `bb_well_formed subst_pred` by
    metis_tac[bb_well_formed_subst_label_terminator] >>
  `run_block_entry (SUC m) ctx subst_pred s =
    OK (v1 with vs_current_bb := sbn)`
    by (irule run_block_entry_eq_exec_block_OK >> simp[]) >>
  `EVERY (\inst. inst.inst_opcode <> PHI) split_bb.bb_instructions`
    by metis_tac[cfgNormSimTheory.build_split_block_no_phis, no_phis_def] >>
  `run_block_entry (SUC m) ctx split_bb
    (v1 with vs_current_bb := sbn) = OK v`
    by (simp[run_block_no_phis_eq_exec_block]) >>
  (* Get result_equiv from split_block_run_block_entry_equiv *)
  mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
    `var_repls`, `SUC m`, `ctx`, `v1`, `v`, `func`, `sbn`]
    split_block_run_block_entry_equiv) >>
  impl_tac >- simp[Abbr `sbn`, Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >> strip_tac >>
  (* Specialize fuel2 = m to get result_equiv for run_block_entry m *)
  first_x_assum (qspec_then `m` mp_tac) >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >> strip_tac >>
  (* Since run_block_entry m ctx target_bb v1 = Error e,
     updated_target also returns Error *)
  qpat_x_assum `result_equiv _ (Error _) _` (fn th =>
    strip_assume_tac (MATCH_MP result_equiv_Error_elim th)) >>
  (* Derive facts needed by run_function_3step *)
  `~v.vs_halted` by (
    imp_res_tac venomExecProofsTheory.exec_block_OK_not_halted >> fs[]) >>
  `v.vs_current_bb = target_bb.bb_label`
    by metis_tac[exec_block_split_bb_current_bb_from_idx0] >>
  (* Use 3step: pred(SUC m) -> split(SUC m) -> target(m) *)
  mp_tac (Q.SPECL [`func'`, `subst_pred`, `split_bb`, `updated_target`,
    `pred_bb.bb_label`, `sbn`, `target_bb.bb_label`,
    `m`, `SUC m`, `SUC m`, `ctx`, `s`,
    `v1 with vs_current_bb := sbn`, `v`]
    run_function_3step) >>
  simp[] >> strip_tac >>
  gvs[stateEquivTheory.result_equiv_def]
QED
(*
 * Helper: Error case for insert_split_target_from_pred.
 * When target_bb returns Error, the transformed function also returns Error.
 * Extracted to avoid nested >- in batch mode.
 *)
Theorem insert_split_target_error_case[local]:
  !func pred_bb target_bb id_base func' split_lbl split_bb var_repls
   subst_pred updated_target m ctx s v1 e.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_lbl /\
    subst_pred = subst_label_terminator target_bb.bb_label split_lbl pred_bb /\
    updated_target = update_phis_for_split pred_bb.bb_label split_lbl
                       var_repls target_bb /\
    lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target /\
    ~s.vs_halted /\ s.vs_current_bb = pred_bb.bb_label /\ s.vs_inst_idx = 0 /\
    run_block_entry (SUC m) ctx pred_bb s = OK v1 /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\ v1.vs_prev_bb = SOME pred_bb.bb_label /\
    run_block_entry m ctx target_bb v1 = Error e /\
    (!f. f >= SUC m ==>
       run_block_entry f ctx subst_pred s =
         OK (v1 with vs_current_bb := split_lbl)) /\
    (!v. MEM v (nub (phi_vars_needing_forward pred_bb.bb_label
           pred_bb target_bb.bb_instructions)) ==>
       !w. v <> STRCAT (STRCAT split_lbl "_fwd_") w) ==>
    ?fuel'. fuel' >= SUC (SUC m) /\
      result_equiv UNIV (Error e) (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `split_lbl = _` SUBST_ALL_TAC >>
  (* Specialize the fuel-monotone hypothesis *)
  first_x_assum (qspec_then `SUC m` assume_tac) >> fs[] >>
  (* run_block_entry for subst_pred is already in hypotheses *)
  `bb_well_formed pred_bb` by fs[wf_function_no_ids_def] >>
  `bb_well_formed subst_pred`
    by metis_tac[bb_well_formed_subst_label_terminator] >>
  (* split_bb has no PHIs *)
  `EVERY (\inst. inst.inst_opcode <> PHI) split_bb.bb_instructions`
    by metis_tac[cfgNormSimTheory.build_split_block_no_phis, no_phis_def] >>
  (* Use split_block_result_cases: exec_block on split_bb is OK or Error *)
  mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`, `var_repls`,
    `SUC m`, `ctx`,
    `v1 with vs_current_bb :=
       split_block_name pred_bb.bb_label target_bb.bb_label`]
    split_block_result_cases) >>
  impl_tac >- simp[] >>
  strip_tac >- (
    (* OK case *)
    qexists `SUC (SUC (SUC m))` >>
    conj_tac >- decide_tac >>
    `v.vs_inst_idx = 0`
      by metis_tac[venomExecPropsTheory.exec_block_OK_inst_idx_0] >>
    `~v.vs_halted`
      by metis_tac[venomExecProofsTheory.exec_block_OK_not_halted] >>
    `v.vs_current_bb = target_bb.bb_label`
      by metis_tac[exec_block_split_bb_current_bb_from_idx0] >>
    `run_block_entry (SUC m) ctx split_bb
      (v1 with vs_current_bb :=
         split_block_name pred_bb.bb_label target_bb.bb_label) = OK v`
      by simp[run_block_no_phis_eq_exec_block] >>
    mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
      `var_repls`, `SUC m`, `ctx`, `v1`, `v`, `func`,
      `split_block_name pred_bb.bb_label target_bb.bb_label`]
      split_block_run_block_entry_equiv) >>
    impl_tac >- simp[Excl "run_block_def"] >> strip_tac >>
    first_x_assum (qspec_then `m` mp_tac) >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >> strip_tac >>
    qpat_x_assum `result_equiv _ (Error _) _` (fn th =>
      strip_assume_tac (MATCH_MP result_equiv_Error_elim th)) >>
    `~v.vs_halted` by (
      imp_res_tac venomExecProofsTheory.exec_block_OK_not_halted >> fs[]) >>
    mp_tac (Q.SPECL [`func'`, `subst_pred`, `split_bb`, `updated_target`,
      `pred_bb.bb_label`,
      `split_block_name pred_bb.bb_label target_bb.bb_label`,
      `target_bb.bb_label`,
      `m`, `SUC m`, `SUC m`, `ctx`, `s`,
      `v1 with vs_current_bb :=
         split_block_name pred_bb.bb_label target_bb.bb_label`, `v`]
      run_function_3step) >>
    impl_tac >- simp[] >> strip_tac >>
    gvs[stateEquivTheory.result_equiv_def]
  ) >>
  (* Error case *)
  qexists `SUC (SUC (SUC m))` >>
  conj_tac >- decide_tac >>
  `run_block_entry (SUC m) ctx split_bb
    (v1 with vs_current_bb :=
       split_block_name pred_bb.bb_label target_bb.bb_label) = Error e'`
    by simp[run_block_no_phis_eq_exec_block] >>
  mp_tac (Q.SPECL [`func'`, `subst_pred`, `split_bb`,
    `pred_bb.bb_label`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `m`, `ctx`, `s`, `v1`, `e`, `e'`]
    error_case_split_bb_error) >>
  impl_tac >- simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >>
  simp[stateEquivTheory.result_equiv_def]
QED

(*
 * Helper: OK-not-halted case for insert_split_target_from_pred.
 * When target_bb returns OK with non-halted state, apply IH.
 * Extracted to avoid nested >- in batch mode.
 *)
Theorem insert_split_target_ok_case[local]:
  !func pred_bb target_bb id_base func' split_lbl split_bb var_repls
   subst_pred updated_target m ctx s v1 v_split v_after1.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_lbl /\
    subst_pred = subst_label_terminator target_bb.bb_label split_lbl pred_bb /\
    updated_target = update_phis_for_split pred_bb.bb_label split_lbl
                       var_repls target_bb /\
    lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target /\
    ~s.vs_halted /\ s.vs_current_bb = pred_bb.bb_label /\ s.vs_inst_idx = 0 /\
    s.vs_labels = FEMPTY /\
    run_block_entry (SUC m) ctx pred_bb s = OK v1 /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\ v1.vs_prev_bb = SOME pred_bb.bb_label /\
    run_block_entry m ctx target_bb v1 = OK v_after1 /\
    ~v_after1.vs_halted /\
    run_block_entry m ctx split_bb (v1 with vs_current_bb := split_lbl) =
      OK v_split /\
    (!f. result_equiv (COMPL (set (fn_all_vars func)))
       (run_block_entry f ctx target_bb v1)
       (run_block_entry f ctx updated_target v_split)) /\
    (!f. f >= SUC m ==>
       run_block_entry f ctx subst_pred s =
         OK (v1 with vs_current_bb := split_lbl)) /\
    (!f. f >= m ==>
       run_block_entry f ctx split_bb (v1 with vs_current_bb := split_lbl) =
         OK v_split) /\
    (!k ctx' s'.
       k <= m /\ ~s'.vs_halted /\
       s'.vs_current_bb <> split_lbl /\ s'.vs_inst_idx = 0 /\
       s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <> SOME split_lbl) ==>
      ?fuel'. fuel' >= k /\
        result_equiv UNIV (run_blocks k ctx' func s')
          (run_blocks fuel' ctx' func' s')) ==>
    ?fuel'. fuel' >= SUC (SUC m) /\
      result_equiv UNIV (run_blocks m ctx func v_after1)
        (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  (* Step 1: Extract v2 from result_equiv at fuel m *)
  qpat_x_assum `!f. result_equiv _ _ _` (qspec_then `m` mp_tac) >>
  simp[stateEquivPropsTheory.result_equiv_is_lift_result] >>
  disch_then (mp_tac o MATCH_MP lift_result_OK_elim) >>
  strip_tac >>
  (* Now: run_block_entry m ctx updated_target v_split = OK v2, state_equiv ... v_after1 v2 *)
  (* Step 2: Extract field equalities from state_equiv *)
  `v_after1.vs_current_bb = v2.vs_current_bb /\
   v_after1.vs_inst_idx = v2.vs_inst_idx /\
   v_after1.vs_halted = v2.vs_halted /\
   v_after1.vs_prev_bb = v2.vs_prev_bb` by
    fs[stateEquivTheory.state_equiv_def, stateEquivTheory.execution_equiv_def] >>
  (* Step 3: v_after1 has inst_idx = 0 *)
  `v_after1.vs_inst_idx = 0` by (
    mp_tac (Q.SPECL [`m`, `ctx`, `target_bb`, `v1`, `v_after1`]
      venomExecProofsTheory.run_block_OK_inst_idx_0) >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >>
  (* Step 4: derive bb_well_formed and inst_wf for target_bb *)
  `bb_well_formed target_bb` by
    (fs[wf_function_no_ids_def] >> metis_tac[]) >>
  `EVERY inst_wf target_bb.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >>
     fs[venomWfTheory.fn_inst_wf_def] >> metis_tac[]) >>
  `target_bb.bb_instructions <> []` by
    (qpat_x_assum `bb_well_formed target_bb` mp_tac >>
     simp[venomWfTheory.bb_well_formed_def]) >>
  `!i. i < LENGTH target_bb.bb_instructions - 1 ==>
     ~is_terminator (EL i target_bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `bb_well_formed target_bb` mp_tac >>
     PURE_REWRITE_TAC[venomWfTheory.bb_well_formed_def] >>
     strip_tac >> rpt strip_tac >> CCONTR_TAC >>
     qpat_x_assum `!j. j < LENGTH target_bb.bb_instructions /\ _ ==> _`
       (qspec_then `i` mp_tac) >>
     impl_tac >- simp[] >> simp[]) >>
  (* v_after1.vs_current_bb is in bb_succs (hence in fn_labels, hence <> split_lbl) *)
  `MEM v_after1.vs_current_bb (bb_succs target_bb)` by
    (mp_tac (Q.SPECL [`m`, `ctx`, `target_bb`, `v1`, `v_after1`]
       venomExecPropsTheory.run_block_current_bb_in_succs) >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >>
  `MEM v_after1.vs_current_bb (fn_labels func)` by
    (fs[wf_function_no_ids_def, venomWfTheory.fn_succs_closed_def] >>
     metis_tac[]) >>
  `v_after1.vs_current_bb <> split_lbl` by (CCONTR_TAC >> fs[] >> metis_tac[]) >>
  (* Step 5: v_after1.vs_prev_bb = SOME target_bb.bb_label *)
  `v_after1.vs_prev_bb = SOME target_bb.bb_label` by (
    mp_tac (Q.SPECL [`m`, `ctx`, `target_bb`, `v1`, `v_after1`]
       venomExecProofsTheory.run_block_ok_prev_bb_exact) >> simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >>
  (* Step 6: Apply IH with v2 *)
  `~v2.vs_halted` by metis_tac[] >>
  `v2.vs_current_bb <> split_lbl` by metis_tac[] >>
  `v2.vs_inst_idx = 0` by metis_tac[] >>
  `(v2.vs_current_bb = target_bb.bb_label ==>
    v2.vs_prev_bb <> SOME pred_bb.bb_label /\
    v2.vs_prev_bb <> SOME split_lbl)` by (
    strip_tac >> fs[] >> conj_tac
    >- (CCONTR_TAC >> fs[])
    >- (CCONTR_TAC >> fs[] >> metis_tac[])) >>
  (* Derive v2.vs_labels = FEMPTY through the chain *)
  `v1.vs_labels = FEMPTY` by (
    mp_tac (Q.SPECL [`SUC m`, `ctx`, `pred_bb`, `s`, `v1`]
      venomExecPropsTheory.run_block_preserves_labels) >> simp[Excl "run_block_def"]) >>
  `(v1 with vs_current_bb := split_lbl).vs_labels = FEMPTY` by simp[] >>
  `v_split.vs_labels = FEMPTY` by (
    mp_tac (Q.SPECL [`m`, `ctx`, `split_bb`,
      `v1 with vs_current_bb := split_lbl`, `v_split`]
      venomExecPropsTheory.run_block_preserves_labels) >> simp[Excl "run_block_def"]) >>
  `v2.vs_labels = FEMPTY` by (
    mp_tac (Q.SPECL [`m`, `ctx`, `updated_target`, `v_split`, `v2`]
      venomExecPropsTheory.run_block_preserves_labels) >> simp[Excl "run_block_def"]) >>
  qpat_assum `!k ctx' s'. _`
    (qspecl_then [`m`, `ctx`, `v2`] mp_tac) >>
  (impl_tac >- simp[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >> strip_tac >>
  (* Now have: fuel' >= m, result_equiv UNIV (run_blocks m ctx func v2)
                                                (run_blocks fuel' ctx func' v2) *)
  (* Step 7: Bridge via transitivity *)
  `result_equiv UNIV (run_blocks m ctx func v_after1)
                     (run_blocks m ctx func v2)` by (
    irule stateEquivPropsTheory.result_equiv_subset >>
    qexists_tac `COMPL (set (fn_all_vars func))` >>
    simp[pred_setTheory.SUBSET_UNIV,
         stateEquivPropsTheory.result_equiv_is_lift_result] >>
    irule run_function_same_fn_state_equiv >>
    simp[stateEquivTheory.state_equiv_def]) >>
  `result_equiv UNIV (run_blocks m ctx func v_after1)
                     (run_blocks fuel' ctx func' v2)` by (
    mp_tac (Q.SPECL [`run_blocks m ctx func v_after1`,
      `run_blocks m ctx func v2`,
      `run_blocks fuel' ctx func' v2`]
      cfgNormSimTheory.result_equiv_UNIV_trans) >>
    simp[]) >>
  (* Step 8: Use run_block_fuel_mono for updated_target *)
  `run_block_entry fuel' ctx updated_target v_split = OK v2` by (
    mp_tac venomExecProofsTheory.run_block_fuel_mono >>
    disch_then (qspecl_then [`m`, `fuel'`, `ctx`, `updated_target`,
        `v_split`, `OK v2`] mp_tac) >> simp[]) >>
  (* Step 9: Derive v_split properties needed for 3step_ok *)
  `~v_split.vs_halted` by
    (mp_tac venomExecProofsTheory.run_block_OK_not_halted >> metis_tac[]) >>
  `v_split.vs_current_bb = target_bb.bb_label` by (
    `EVERY (\inst. inst.inst_opcode <> PHI) split_bb.bb_instructions`
      by metis_tac[cfgNormSimTheory.build_split_block_no_phis, no_phis_def] >>
    `(v1 with vs_current_bb := split_lbl) with vs_inst_idx := 0 =
      v1 with vs_current_bb := split_lbl`
      by simp[venomStateTheory.venom_state_component_equality] >>
    `exec_block m ctx split_bb (v1 with vs_current_bb := split_lbl) = OK v_split`
      by metis_tac[run_block_no_phis_eq_exec_block] >>
    metis_tac[exec_block_split_bb_current_bb_from_idx0]) >>
  (* Step 10: Use run_function_3step_ok *)
  `run_block_entry (SUC m) ctx subst_pred s =
     OK (v1 with vs_current_bb := split_lbl)` by (
    first_x_assum (qspec_then `SUC m` mp_tac) >> simp[]) >>
  qexists_tac `fuel' + 3` >> simp[] >>
  `fuel' + 3 = SUC (SUC (SUC fuel'))` by simp[] >>
  pop_assum SUBST1_TAC >>
  mp_tac (Q.SPECL [`func'`, `subst_pred`, `split_bb`, `updated_target`,
    `pred_bb.bb_label`, `split_lbl`, `target_bb.bb_label`,
    `fuel'`, `SUC m`, `m`, `ctx`, `s`,
    `v1 with vs_current_bb := split_lbl`, `v_split`, `v2`]
    run_function_3step_ok) >>
  `v_split.vs_inst_idx = 0`
    by metis_tac[venomExecProofsTheory.run_block_OK_inst_idx_0] >>
  `s with vs_inst_idx := 0 = s` by simp[venomStateTheory.inst_idx_update_id] >>
  `v1 with <|vs_inst_idx := 0; vs_current_bb := split_lbl|> =
   v1 with vs_current_bb := split_lbl`
    by simp[venomStateTheory.venom_state_component_equality] >>
  `v_split with vs_inst_idx := 0 = v_split`
    by simp[venomStateTheory.inst_idx_update_id] >>
  (impl_tac >- gvs[]) >>
  strip_tac >>
  (* Goal has insert_split ..., assumption has func'. Unify via SUBST1_TAC *)
  qpat_x_assum `func' = _` (SUBST1_TAC o GSYM) >>
  gvs[stateEquivPropsTheory.result_equiv_is_lift_result]
QED

(* Boundary lemma: unfold run_blocks (SUC fuel) when lookup_block is known.
   Avoids once_rewrite_tac[run_blocks_unfold] >> simp[] in by blocks. *)

(* Boundary lemma: MAP of opcode-preserving function preserves phi_prefix_length *)
Theorem phi_prefix_length_subst_label_terminator[local]:
  !old_lbl new_lbl insts.
    phi_prefix_length (MAP (\inst. if is_terminator inst.inst_opcode
                                   then subst_label_inst old_lbl new_lbl inst
                                   else inst) insts) =
    phi_prefix_length insts
Proof
  Induct_on `insts` >> simp[phi_prefix_length_def] >>
  rpt gen_tac >>
  `(if is_terminator h.inst_opcode then subst_label_inst old_lbl new_lbl h
    else h).inst_opcode = h.inst_opcode` by
    simp[subst_label_terminator_inst_opcode] >>
  simp[]
QED

(* Boundary lemma: MAP of opcode-preserving function preserves eval_phis *)
Theorem eval_phis_subst_label_terminator[local]:
  !s old_lbl new_lbl insts.
    eval_phis s (MAP (\inst. if is_terminator inst.inst_opcode
                             then subst_label_inst old_lbl new_lbl inst
                             else inst) insts) =
    eval_phis s insts
Proof
  Induct_on `insts` >> simp[eval_phis_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
  >- ((* h is PHI: is_terminator PHI = F, so MAP leaves h unchanged *)
    simp[venomInstTheory.is_terminator_def] >>
    Cases_on `eval_one_phi s h` >> simp[] >>
    Cases_on `x` >> simp[] >>
    PairCases_on `r` >> simp[])
  >> (* h is not PHI: the conditional inst also has inst_opcode <> PHI,
        so eval_phis returns OK s on both sides *)
  `(if is_terminator h.inst_opcode
    then subst_label_inst old_lbl new_lbl h else h).inst_opcode <> PHI` by (
    simp[subst_label_terminator_inst_opcode]) >>
  simp[]
QED

(* Derived boundary lemmas at the subst_label_terminator level:
   The MAP-level lemmas above combine with subst_label_terminator_def
   to give properties about the actual block transform. *)
Theorem eval_phis_subst_label_terminator_bb[local]:
  !s old_lbl new_lbl bb.
    eval_phis s (subst_label_terminator old_lbl new_lbl bb).bb_instructions =
    eval_phis s bb.bb_instructions
Proof
  simp[cfgTransformTheory.subst_label_terminator_def,
       eval_phis_subst_label_terminator]
QED

Theorem phi_prefix_length_subst_label_terminator_bb[local]:
  !old_lbl new_lbl bb.
    phi_prefix_length (subst_label_terminator old_lbl new_lbl bb).bb_instructions =
    phi_prefix_length bb.bb_instructions
Proof
  simp[cfgTransformTheory.subst_label_terminator_def,
       phi_prefix_length_subst_label_terminator]
QED

(* run_block-level version of run_block_subst_label_general.
   subst_label_terminator doesn't change PHIs (only terminators),
   so eval_phis and phi_prefix_length are preserved, and the exec_block
   relationship from run_block_subst_label_general applies. *)
Theorem run_block_subst_label_run_block[local]:
  !fuel ctx bb s old_lbl new_lbl.
    ~s.vs_halted /\ s.vs_labels = FEMPTY /\ s.vs_inst_idx = 0 ==>
    run_block fuel ctx (subst_label_terminator old_lbl new_lbl bb) s =
    (case run_block fuel ctx bb s of
       OK v => OK (if v.vs_current_bb = old_lbl
                   then v with vs_current_bb := new_lbl
                   else v)
     | other => other)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  `eval_phis s (subst_label_terminator old_lbl new_lbl bb).bb_instructions =
    eval_phis s bb.bb_instructions` by (
    simp[cfgTransformTheory.subst_label_terminator_def,
         eval_phis_subst_label_terminator]) >>
  `phi_prefix_length (subst_label_terminator old_lbl new_lbl bb).bb_instructions =
    phi_prefix_length bb.bb_instructions` by (
    simp[cfgTransformTheory.subst_label_terminator_def,
         phi_prefix_length_subst_label_terminator]) >>
  gvs[] >>
  (* eval_phis can only return OK or Error — split directly using the disjunction *)
  DISJ_CASES_THEN STRIP_ASSUME_TAC
    (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- ((* OK case: eval_phis s bb.bb_instructions = OK s_phi' *)
    gvs[] >> rename1 `OK s_phi` >>
    `s_phi.vs_halted = s.vs_halted` by metis_tac[eval_phis_preserves_halted] >>
    `s_phi.vs_labels = s.vs_labels` by metis_tac[venomExecPropsTheory.eval_phis_preserves_labels] >>
    `s_phi.vs_inst_idx = s.vs_inst_idx` by metis_tac[eval_phis_preserves_inst_idx] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`,
      `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
      `old_lbl`, `new_lbl`] run_block_subst_label_general) >>
    impl_tac >- simp[venom_state_component_equality] >>
    Cases_on `exec_block fuel ctx bb (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> gvs[])
  (* Error case: both sides = Error e *)
  >> gvs[]
QED

Theorem run_blocks_SUC_lookup_SOME[local]:
  !fuel ctx fn s bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
    run_blocks (SUC fuel) ctx fn s =
      case run_block_entry fuel ctx bb s of
        OK s' => if s'.vs_halted then Halt s' else run_blocks fuel ctx fn s'
      | Halt v => Halt v | Abort a s' => Abort a s'
      | IntRet vals s' => IntRet vals s' | Error e => Error e
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_blocks_unfold] >>
  gvs[]
QED

Theorem run_blocks_SUC_target_lookup[local]:
  !fuel ctx fn s bb.
    s.vs_current_bb = bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb ==>
    run_blocks (SUC fuel) ctx fn s =
      case run_block_entry fuel ctx bb s of
        OK s' => if s'.vs_halted then Halt s' else run_blocks fuel ctx fn s'
      | Halt v => Halt v | Abort a s' => Abort a s'
      | IntRet vals s' => IntRet vals s' | Error e => Error e
Proof
  rpt strip_tac >>
  irule run_blocks_SUC_lookup_SOME >>
  simp[]
QED

Theorem run_block_entry_OK_not_halted[local]:
  !fuel ctx bb s v.
    run_block_entry fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  ACCEPT_TAC venomExecProofsTheory.run_block_OK_not_halted
QED

(* Boundary lemma: derive v_split.vs_current_bb from run_block_entry on split_bb.
   Bridge: run_block_entry -> exec_block (no PHIs) -> exec_block_split_bb_current_bb_from_idx0 *)
Theorem split_bb_run_block_entry_current_bb[local]:
  !pred_bb target_bb id_base split_bb var_repls fuel ctx v1 v_split split_lbl.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    v1.vs_inst_idx = 0 /\
    run_block_entry fuel ctx split_bb (v1 with vs_current_bb := split_lbl) = OK v_split ==>
    v_split.vs_current_bb = target_bb.bb_label
Proof
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) split_bb.bb_instructions`
    by metis_tac[cfgNormSimTheory.build_split_block_no_phis, no_phis_def] >>
  imp_res_tac run_block_no_phis_eq_exec_block >>
  gvs[venom_state_component_equality] >>
  metis_tac[exec_block_split_bb_current_bb_from_idx0]
QED
(* Standalone lemma: when run_block_entry on target_bb is not Error,
   the split block executes successfully and is result_equiv.
   Extracted to avoid by-block chaining failures. *)
Theorem split_bb_run_block_entry_facts[local]:
  !func pred_bb target_bb id_base split_lbl split_bb var_repls
   updated_target fuel ctx v1.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    ~v1.vs_halted /\ v1.vs_inst_idx = 0 /\
    v1.vs_prev_bb = SOME pred_bb.bb_label /\
    v1.vs_current_bb = target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_lbl /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    bb_well_formed target_bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) target_bb.bb_instructions) /\
    updated_target = update_phis_for_split pred_bb.bb_label split_lbl
                       var_repls target_bb /\
    (!e. run_block_entry fuel ctx target_bb v1 <> Error e) ==>
    ?v_split.
      run_block_entry fuel ctx split_bb (v1 with vs_current_bb := split_lbl) =
        OK v_split /\
      (!f. result_equiv (COMPL (set (fn_all_vars func)))
             (run_block_entry f ctx target_bb v1)
             (run_block_entry f ctx updated_target v_split)) /\
      (!f. f >= fuel ==>
           run_block_entry f ctx split_bb
             (v1 with vs_current_bb := split_lbl) = OK v_split)
Proof
  rpt gen_tac >> strip_tac >>
  (* Derive phi_fwd_vars in FDOM from non-Error condition *)
  `!var. MEM var (nub (phi_vars_needing_forward pred_bb.bb_label
           pred_bb target_bb.bb_instructions)) ==>
     var IN FDOM v1.vs_vars` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `target_bb`, `v1`, `func`,
      `pred_bb.bb_label`, `pred_bb`, `var`]
      run_block_entry_non_error_phi_fwd_vars_defined) >>
    simp[] >> metis_tac[listTheory.MEM_nub]) >>
  (* Derive _fwd_ freshness for run_split_block *)
  `!v. MEM v (nub (phi_vars_needing_forward pred_bb.bb_label
           pred_bb target_bb.bb_instructions)) ==>
     !w. v <> STRCAT (STRCAT
           (split_block_name pred_bb.bb_label target_bb.bb_label)
           "_fwd_") w` by (
    rpt strip_tac >>
    `MEM v (fn_all_vars func)` by (
      mp_tac (Q.SPECL [`func`, `target_bb`, `pred_bb.bb_label`,
        `pred_bb`, `v`] phi_fwd_var_in_fn_all_vars) >>
      simp[] >> metis_tac[listTheory.MEM_nub]) >>
    qpat_x_assum `split_lbl = _` SUBST_ALL_TAC >>
    CCONTR_TAC >> fs[] >> metis_tac[]) >>
  (* split_bb has no PHIs *)
  `EVERY (\inst. inst.inst_opcode <> PHI) split_bb.bb_instructions`
    by metis_tac[cfgNormSimTheory.build_split_block_no_phis, no_phis_def] >>
  `bb_well_formed split_bb`
    by metis_tac[bb_well_formed_split_bb] >>
  (* exec_block on split_bb gives OK via run_split_block *)
  `?v. exec_block fuel ctx split_bb
         (v1 with vs_current_bb := split_lbl) = OK v /\
       v.vs_current_bb = target_bb.bb_label /\
       v.vs_inst_idx = 0 /\ ~v.vs_halted`
    by (mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
        `var_repls`, `fuel`, `ctx`,
        `v1 with vs_current_bb := split_lbl`]
        run_split_block) >>
      simp[venom_state_component_equality] >>
      metis_tac[]) >>
  qexists_tac `v` >>
  conj_tac >- (
    (* run_block_entry fuel = OK v *)
    `(v1 with vs_current_bb := split_lbl) with vs_inst_idx := 0 =
     v1 with vs_current_bb := split_lbl`
      by simp[venom_state_component_equality] >>
    `run_block_entry fuel ctx split_bb
       (v1 with vs_current_bb := split_lbl) =
     exec_block fuel ctx split_bb
       (v1 with vs_current_bb := split_lbl)`
      by metis_tac[run_block_no_phis_eq_exec_block] >>
    simp[]) >>
  conj_tac >- (
    (* result_equiv via split_block_run_block_entry_equiv *)
    gen_tac >>
    mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`, `split_bb`,
      `var_repls`, `fuel`, `ctx`, `v1`, `v`, `func`, `split_lbl`]
      split_block_run_block_entry_equiv) >>
    impl_keep_tac >- (
      simp[venom_state_component_equality] >>
      metis_tac[]) >>
    simp[]) >>
  (* fuel monotonicity via run_block_entry_fuel_mono_no_phis *)
  rpt strip_tac >>
  `run_block_entry fuel ctx split_bb
     (v1 with vs_current_bb := split_lbl) = OK v` by (
    `run_block_entry fuel ctx split_bb
       (v1 with vs_current_bb := split_lbl) =
     exec_block fuel ctx split_bb
       ((v1 with vs_current_bb := split_lbl) with vs_inst_idx := 0)`
      by metis_tac[run_block_no_phis_eq_exec_block] >>
    `(v1 with vs_current_bb := split_lbl) with vs_inst_idx := 0 =
     v1 with vs_current_bb := split_lbl`
      by simp[venom_state_component_equality] >>
    metis_tac[]) >>
  irule run_block_entry_fuel_mono_no_phis >>
  simp[venom_state_component_equality] >>
  metis_tac[]
QED
(* For n=0 case: when exec_block 0 gives OK on original, the transformed
   function's first block also succeeds (same instructions, just label changed),
   then both run_blocks 0 = Error "out of fuel" *)
Theorem insert_split_target_fuel0[local]:
  !func pred_bb target_bb id_base func' ctx s v1.
    wf_function_no_ids func /\
    MEM pred_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    func' = insert_split func pred_bb target_bb id_base /\
    ~s.vs_halted /\
    s.vs_current_bb = pred_bb.bb_label /\
    s.vs_inst_idx = 0 /\
    s.vs_labels = FEMPTY /\
    run_block_entry 0 ctx pred_bb s = OK v1 /\
    ~v1.vs_halted /\
    v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\
    v1.vs_prev_bb = SOME pred_bb.bb_label ==>
    result_equiv UNIV (run_blocks 0 ctx func v1)
      (run_blocks 1 ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  (* Step 1: lookup_block for ORIGINAL func *)
  `lookup_block pred_bb.bb_label func.fn_blocks = SOME pred_bb`
    by metis_tac[MEM_lookup_block, wf_function_no_ids_def, fn_labels_def] >>
  (* Step 2: lookup_block for TRANSFORMED func *)
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
            lookup_insert_split_pred) >>
  simp[PULL_EXISTS] >> rpt strip_tac >>
  (* Step 3: Use run_block_subst_label_run_block directly *)
  `run_block 0 ctx (subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb) s =
    OK (v1 with vs_current_bb := split_bb.bb_label)` by (
    mp_tac (Q.SPECL [`0`, `ctx`, `pred_bb`, `s`,
      `target_bb.bb_label`, `split_bb.bb_label`]
      run_block_subst_label_run_block) >>
    impl_tac >- (rpt strip_tac >> asm_rewrite_tac[]) >>
    strip_tac >>
    pop_assum SUBST1_TAC >>
    gvs[Excl "run_block_def", AllCaseEqs()]) >>
  `~(v1 with vs_current_bb := split_bb.bb_label).vs_halted`
    by simp[venom_state_component_equality] >>
  (* Step 4: Both sides are Error "out of fuel" *)
  `run_blocks 0 ctx func v1 = Error "out of fuel"` by (
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_blocks_def] >> simp[Excl "run_block_def"]) >>
  `run_blocks 1 ctx func' s = Error "out of fuel"` by (
    mp_tac (Q.SPECL [`0`,`ctx`,`func'`,
      `subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb`,
      `s`,`v1 with vs_current_bb := split_bb.bb_label`]
      venomExecPropsTheory.run_blocks_step) >>
    impl_tac >- (
      conj_tac >- (asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      first_assum ACCEPT_TAC) >>
    disch_tac >>
    gvs[Excl "run_block_def"] >>
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_blocks_def] >>
    simp[Excl "run_block_def"]) >>
  gvs[stateEquivTheory.result_equiv_def]
QED

Theorem insert_split_target_ok_halted_case[local]:
  !func func' pred_bb target_bb id_base subst_pred split_bb updated_target
   split_lbl var_repls m ctx s v1 v_split v.
    lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target /\
    s.vs_current_bb = pred_bb.bb_label /\
    run_block_entry (SUC m) ctx subst_pred s =
      OK (v1 with vs_current_bb := split_lbl) /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    run_block_entry m ctx split_bb (v1 with vs_current_bb := split_lbl) =
      OK v_split /\
    result_equiv (COMPL (set (fn_all_vars func))) (OK v)
      (run_block_entry m ctx updated_target v_split) /\
    v.vs_halted ==>
    ?fuel'. fuel' >= SUC (SUC m) /\
      result_equiv UNIV (Halt v) (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `SUC (SUC (SUC m))` >>
  conj_tac >- decide_tac >>
  `~v_split.vs_halted` by
    metis_tac[run_block_entry_OK_not_halted] >>
  `v_split.vs_current_bb = target_bb.bb_label` by
    metis_tac[split_bb_run_block_entry_current_bb] >>
  mp_tac (Q.SPECL [`func`, `func'`, `subst_pred`, `split_bb`,
    `updated_target`, `pred_bb.bb_label`, `split_lbl`,
    `target_bb.bb_label`, `m`, `SUC m`, `m`, `ctx`, `s`,
    `v1 with vs_current_bb := split_lbl`, `v_split`,
    `COMPL (set (fn_all_vars func))`, `v`]
    insert_split_3step_ok_halted) >>
  impl_tac >- simp[venom_state_component_equality] >>
  simp[]
QED

Theorem insert_split_target_ok_dispatch[local]:
  !func pred_bb target_bb id_base func' split_lbl split_bb var_repls
   subst_pred updated_target m ctx s v1 v_split v.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_lbl /\
    subst_pred = subst_label_terminator target_bb.bb_label split_lbl pred_bb /\
    updated_target = update_phis_for_split pred_bb.bb_label split_lbl
                       var_repls target_bb /\
    lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target /\
    ~s.vs_halted /\ s.vs_current_bb = pred_bb.bb_label /\ s.vs_inst_idx = 0 /\
    s.vs_labels = FEMPTY /\
    run_block_entry (SUC m) ctx pred_bb s = OK v1 /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\ v1.vs_prev_bb = SOME pred_bb.bb_label /\
    run_block_entry m ctx target_bb v1 = OK v /\
    run_block_entry m ctx split_bb (v1 with vs_current_bb := split_lbl) =
      OK v_split /\
    (!f. result_equiv (COMPL (set (fn_all_vars func)))
       (run_block_entry f ctx target_bb v1)
       (run_block_entry f ctx updated_target v_split)) /\
    (!f. f >= SUC m ==>
       run_block_entry f ctx subst_pred s =
         OK (v1 with vs_current_bb := split_lbl)) /\
    (!f. f >= m ==>
       run_block_entry f ctx split_bb (v1 with vs_current_bb := split_lbl) =
         OK v_split) /\
    (!k ctx' s'.
       k <= m /\ ~s'.vs_halted /\
       s'.vs_current_bb <> split_lbl /\ s'.vs_inst_idx = 0 /\
       s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <> SOME split_lbl) ==>
      ?fuel'. fuel' >= k /\
        result_equiv UNIV (run_blocks k ctx' func s')
          (run_blocks fuel' ctx' func' s')) ==>
    ?fuel'. fuel' >= SUC (SUC m) /\
      result_equiv UNIV
        (if v.vs_halted then Halt v else run_blocks m ctx func v)
        (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v.vs_halted` >> gvs[]
  >- (
    mp_tac (Q.SPECL [`func`, `insert_split func pred_bb target_bb id_base`,
      `pred_bb`, `target_bb`, `id_base`,
      `subst_label_terminator target_bb.bb_label
         (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb`,
      `split_bb`,
      `update_phis_for_split pred_bb.bb_label
         (split_block_name pred_bb.bb_label target_bb.bb_label)
         var_repls target_bb`,
      `split_block_name pred_bb.bb_label target_bb.bb_label`,
      `var_repls`, `m`, `ctx`, `s`, `v1`, `v_split`, `v`]
      insert_split_target_ok_halted_case) >>
    impl_tac >- (
      simp[venom_state_component_equality] >>
      qpat_x_assum `!f. result_equiv _ _ _`
        (qspec_then `m` mp_tac) >>
      simp[]) >>
    metis_tac[]) >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
    `insert_split func pred_bb target_bb id_base`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `split_bb`, `var_repls`,
    `subst_label_terminator target_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb`,
    `update_phis_for_split pred_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label)
       var_repls target_bb`,
    `m`, `ctx`, `s`, `v1`, `v_split`, `v`]
    insert_split_target_ok_case) >>
  impl_tac >- (
    simp[venom_state_component_equality] >>
    rpt conj_tac >> simp[] >>
    FIRST [
      qpat_x_assum `!f. result_equiv _ _ _`
        (qspec_then `m` mp_tac) >> simp[],
      qpat_x_assum `!f. f >= m ==> run_block_entry f ctx split_bb _ = OK v_split`
        (qspec_then `m` mp_tac) >> simp[]]) >>
  metis_tac[]
QED

Theorem insert_split_target_ok_branch[local]:
  !func pred_bb target_bb id_base func' split_lbl split_bb var_repls
   subst_pred updated_target m ctx s v1 v.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    (∀bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_lbl /\
    subst_pred = subst_label_terminator target_bb.bb_label split_lbl pred_bb /\
    updated_target = update_phis_for_split pred_bb.bb_label split_lbl
                       var_repls target_bb /\
    lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target /\
    ~s.vs_halted /\ s.vs_current_bb = pred_bb.bb_label /\ s.vs_inst_idx = 0 /\
    s.vs_labels = FEMPTY /\
    run_block_entry (SUC m) ctx pred_bb s = OK v1 /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\ v1.vs_prev_bb = SOME pred_bb.bb_label /\
    run_block_entry m ctx target_bb v1 = OK v /\
    (!f. f >= SUC m ==>
       run_block_entry f ctx subst_pred s =
         OK (v1 with vs_current_bb := split_lbl)) /\
    (!k ctx' s'.
       k <= m /\ ~s'.vs_halted /\
       s'.vs_current_bb <> split_lbl /\ s'.vs_inst_idx = 0 /\
       s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <> SOME split_lbl) ==>
      ?fuel'. fuel' >= k /\
        result_equiv UNIV (run_blocks k ctx' func s')
          (run_blocks fuel' ctx' func' s')) ==>
    ?fuel'. fuel' >= SUC (SUC m) /\
      result_equiv UNIV
        (if v.vs_halted then Halt v else run_blocks m ctx func v)
        (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed target_bb` by fs[wf_function_no_ids_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) target_bb.bb_instructions)` by
    res_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
    `split_lbl`, `split_bb`, `var_repls`, `updated_target`,
    `m`, `ctx`, `v1`] split_bb_run_block_entry_facts) >>
  impl_tac >- simp[] >>
  strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `func'`,
    `split_lbl`, `split_bb`, `var_repls`, `subst_pred`, `updated_target`,
    `m`, `ctx`, `s`, `v1`, `v_split`, `v`]
    insert_split_target_ok_dispatch) >>
  impl_tac >- simp[venom_state_component_equality] >>
  metis_tac[]
QED

Theorem insert_split_target_ok_branch_expanded[local]:
  !func pred_bb target_bb id_base split_bb var_repls m ctx s v1 v.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    (!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
      (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT
                (split_block_name pred_bb.bb_label target_bb.bb_label)
                "_fwd_") var) (fn_all_vars func)) /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_block_name pred_bb.bb_label target_bb.bb_label /\
    lookup_block pred_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
      SOME (subst_label_terminator target_bb.bb_label
        (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) /\
    lookup_block (split_block_name pred_bb.bb_label target_bb.bb_label)
      (insert_split func pred_bb target_bb id_base).fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
      SOME (update_phis_for_split pred_bb.bb_label
        (split_block_name pred_bb.bb_label target_bb.bb_label)
        var_repls target_bb) /\
    ~s.vs_halted /\ s.vs_current_bb = pred_bb.bb_label /\
    s.vs_inst_idx = 0 /\ s.vs_labels = FEMPTY /\
    run_block_entry (SUC m) ctx pred_bb s = OK v1 /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\ v1.vs_prev_bb = SOME pred_bb.bb_label /\
    run_block_entry m ctx target_bb v1 = OK v /\
    (!f. f >= SUC m ==>
       run_block_entry f ctx
         (subst_label_terminator target_bb.bb_label
            (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) s =
         OK (v1 with vs_current_bb :=
           split_block_name pred_bb.bb_label target_bb.bb_label)) /\
    (!k ctx' s'.
       k <= m /\ ~s'.vs_halted /\
       s'.vs_current_bb <>
         split_block_name pred_bb.bb_label target_bb.bb_label /\
       s'.vs_inst_idx = 0 /\ s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <>
          SOME (split_block_name pred_bb.bb_label target_bb.bb_label)) ==>
      ?fuel'. fuel' >= k /\
        result_equiv UNIV (run_blocks k ctx' func s')
          (run_blocks fuel' ctx'
            (insert_split func pred_bb target_bb id_base) s')) ==>
    ?fuel'. fuel' >= SUC (SUC m) /\
      result_equiv UNIV
        (if v.vs_halted then Halt v else run_blocks m ctx func v)
        (run_blocks fuel' ctx (insert_split func pred_bb target_bb id_base) s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
    `insert_split func pred_bb target_bb id_base`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `split_bb`, `var_repls`,
    `subst_label_terminator target_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb`,
    `update_phis_for_split pred_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label)
       var_repls target_bb`,
    `m`, `ctx`, `s`, `v1`, `v`]
    insert_split_target_ok_branch) >>
  impl_tac >- simp[venom_state_component_equality] >>
  simp[]
QED

Theorem insert_split_target_terminal_branch[local]:
  !func pred_bb target_bb id_base func' split_lbl split_bb var_repls
   subst_pred updated_target m ctx s v1 r_target.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    (∀bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_lbl /\
    subst_pred = subst_label_terminator target_bb.bb_label split_lbl pred_bb /\
    updated_target = update_phis_for_split pred_bb.bb_label split_lbl
                       var_repls target_bb /\
    lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target /\
    ~s.vs_halted /\ s.vs_current_bb = pred_bb.bb_label /\ s.vs_inst_idx = 0 /\
    s.vs_labels = FEMPTY /\
    run_block_entry (SUC m) ctx subst_pred s =
      OK (v1 with vs_current_bb := split_lbl) /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\ v1.vs_prev_bb = SOME pred_bb.bb_label /\
    run_block_entry m ctx target_bb v1 = r_target /\
    (!e. r_target <> Error e) /\
    (!v'. r_target = OK v' ==> v'.vs_halted) ==>
    result_equiv UNIV
      (case r_target of
         OK s'' => if s''.vs_halted then Halt s''
                   else run_blocks m ctx func s''
       | Halt v => Halt v
       | Abort a s' => Abort a s'
       | IntRet vals s' => IntRet vals s'
       | Error e => Error e)
      (run_blocks (SUC (SUC (SUC m))) ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed target_bb` by fs[wf_function_no_ids_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) target_bb.bb_instructions)` by
    res_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
    `split_lbl`, `split_bb`, `var_repls`, `updated_target`,
    `m`, `ctx`, `v1`] split_bb_run_block_entry_facts) >>
  impl_tac >- simp[] >>
  strip_tac >>
  `~v_split.vs_halted` by
    metis_tac[run_block_entry_OK_not_halted] >>
  `v_split.vs_current_bb = target_bb.bb_label` by
    metis_tac[split_bb_run_block_entry_current_bb] >>
  qpat_x_assum `!f. result_equiv _ (run_block_entry f ctx target_bb v1) _`
    (qspec_then `m` mp_tac) >>
  simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`func`, `func'`, `subst_pred`, `split_bb`,
    `updated_target`, `pred_bb.bb_label`, `split_lbl`, `target_bb.bb_label`,
    `m`, `SUC m`, `m`, `ctx`, `s`,
    `v1 with vs_current_bb := split_lbl`, `v_split`,
    `COMPL (set (fn_all_vars func))`, `r_target`]
    insert_split_3step_terminal) >>
  impl_tac >- simp[venom_state_component_equality] >>
  simp[]
QED

Theorem insert_split_target_terminal_branch_expanded[local]:
  !func pred_bb target_bb id_base split_bb var_repls m ctx s v1 r_target.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    (!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
      (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT
                (split_block_name pred_bb.bb_label target_bb.bb_label)
                "_fwd_") var) (fn_all_vars func)) /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_block_name pred_bb.bb_label target_bb.bb_label /\
    lookup_block pred_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
      SOME (subst_label_terminator target_bb.bb_label
        (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) /\
    lookup_block (split_block_name pred_bb.bb_label target_bb.bb_label)
      (insert_split func pred_bb target_bb id_base).fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
      SOME (update_phis_for_split pred_bb.bb_label
        (split_block_name pred_bb.bb_label target_bb.bb_label)
        var_repls target_bb) /\
    ~s.vs_halted /\ s.vs_current_bb = pred_bb.bb_label /\
    s.vs_inst_idx = 0 /\ s.vs_labels = FEMPTY /\
    run_block_entry (SUC m) ctx pred_bb s = OK v1 /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\ v1.vs_prev_bb = SOME pred_bb.bb_label /\
    run_block_entry m ctx target_bb v1 = r_target /\
    (!f. f >= SUC m ==>
       run_block_entry f ctx
         (subst_label_terminator target_bb.bb_label
            (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) s =
         OK (v1 with vs_current_bb :=
           split_block_name pred_bb.bb_label target_bb.bb_label)) /\
    (!e. r_target <> Error e) /\
    (!v'. r_target = OK v' ==> v'.vs_halted) ==>
    result_equiv UNIV
      (case r_target of
         OK s'' => if s''.vs_halted then Halt s''
                   else run_blocks m ctx func s''
       | Halt v => Halt v
       | Abort a s' => Abort a s'
       | IntRet vals s' => IntRet vals s'
       | Error e => Error e)
      (run_blocks (SUC (SUC (SUC m))) ctx
        (insert_split func pred_bb target_bb id_base) s)
Proof
  rpt gen_tac >> strip_tac >>
  `run_block_entry (SUC m) ctx
     (subst_label_terminator target_bb.bb_label
        (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) s =
   OK (v1 with vs_current_bb :=
        split_block_name pred_bb.bb_label target_bb.bb_label)` by (
    qpat_x_assum `!f. f >= SUC m ==> _` (qspec_then `SUC m` mp_tac) >>
    simp[]) >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
    `insert_split func pred_bb target_bb id_base`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `split_bb`, `var_repls`,
    `subst_label_terminator target_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb`,
    `update_phis_for_split pred_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label)
       var_repls target_bb`,
    `m`, `ctx`, `s`, `v1`, `r_target`]
    insert_split_target_terminal_branch) >>
  impl_tac >- simp[venom_state_component_equality] >>
  simp[]
QED

Theorem insert_split_target_result_dispatch[local]:
  !func pred_bb target_bb id_base func' split_lbl split_bb var_repls
   subst_pred updated_target m ctx s v1 r_target.
    wf_function_no_ids func /\ fn_inst_wf func /\
    fn_phi_preds_closed func /\ fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\ ALL_DISTINCT (fn_labels func) /\
    (!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM pred_bb func.fn_blocks /\ MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_bb.bb_label = split_lbl /\
    subst_pred = subst_label_terminator target_bb.bb_label split_lbl pred_bb /\
    updated_target = update_phis_for_split pred_bb.bb_label split_lbl
                       var_repls target_bb /\
    lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred /\
    lookup_block split_lbl func'.fn_blocks = SOME split_bb /\
    lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target /\
    ~s.vs_halted /\ s.vs_current_bb = pred_bb.bb_label /\ s.vs_inst_idx = 0 /\
    s.vs_labels = FEMPTY /\
    run_block_entry (SUC m) ctx pred_bb s = OK v1 /\
    run_block_entry (SUC m) ctx subst_pred s =
      OK (v1 with vs_current_bb := split_lbl) /\
    ~v1.vs_halted /\ v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\ v1.vs_prev_bb = SOME pred_bb.bb_label /\
    run_block_entry m ctx target_bb v1 = r_target /\
    (!f. f >= SUC m ==>
       run_block_entry f ctx subst_pred s =
         OK (v1 with vs_current_bb := split_lbl)) /\
    (!k ctx' s'.
       k <= m /\ ~s'.vs_halted /\
       s'.vs_current_bb <> split_lbl /\ s'.vs_inst_idx = 0 /\
       s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <> SOME split_lbl) ==>
      ?fuel'. fuel' >= k /\
        result_equiv UNIV (run_blocks k ctx' func s')
          (run_blocks fuel' ctx' func' s')) /\
    (!e. r_target = Error e ==>
      ?fuel'. fuel' >= SUC (SUC m) /\
        result_equiv UNIV (Error e) (run_blocks fuel' ctx func' s)) ==>
    ?fuel'. fuel' >= SUC (SUC m) /\
      result_equiv UNIV
        (case r_target of
           OK s'' => if s''.vs_halted then Halt s''
                     else run_blocks m ctx func s''
         | Halt v => Halt v
         | Abort a s' => Abort a s'
         | IntRet vals s' => IntRet vals s'
         | Error e => Error e)
        (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r_target` >> gvs[] >>
  TRY (drule_all insert_split_target_ok_branch_expanded >> simp[]) >>
  TRY (
    qexists_tac `SUC (SUC (SUC m))` >>
    conj_tac >- decide_tac >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
      `split_bb`, `var_repls`, `m`, `ctx`, `s`, `v1`,
      `run_block_entry m ctx target_bb v1`]
      insert_split_target_terminal_branch_expanded) >>
    impl_tac >- gvs[venom_state_component_equality] >>
    simp[]) >>
  TRY (
    qpat_x_assum `!e. _ = Error e ==> ?fuel'. _` mp_tac >>
    simp[] >> strip_tac >>
    qexists_tac `fuel'` >> gvs[]) >>
  metis_tac[]
QED

Theorem subst_label_run_block_entry_target_ok[local]:
  !ctx subst_pred pred_bb s v target_lbl split_lbl k.
    (!j. run_block_entry j ctx subst_pred s =
      (case run_block_entry j ctx pred_bb s of
         OK v' => OK (if v'.vs_current_bb = target_lbl
                      then v' with vs_current_bb := split_lbl
                      else v')
       | other => other)) /\
    run_block_entry k ctx pred_bb s = OK v /\
    v.vs_current_bb = target_lbl ==>
    run_block_entry k ctx subst_pred s =
      OK (v with vs_current_bb := split_lbl)
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem insert_split_target_from_pred[local]:
  !func pred_bb target_bb id_base n ctx s v1.
    wf_function_no_ids func /\
    fn_inst_wf func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    ALL_DISTINCT (fn_labels func) /\
    (!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT (split_block_name pred_bb.bb_label
                  target_bb.bb_label) "_fwd_") var)
                (fn_all_vars func)) /\
    s.vs_labels = FEMPTY /\
    ~s.vs_halted /\
    s.vs_current_bb = pred_bb.bb_label /\
    s.vs_inst_idx = 0 /\
    run_block_entry n ctx pred_bb s = OK v1 /\
    ~v1.vs_halted /\
    v1.vs_current_bb = target_bb.bb_label /\
    v1.vs_inst_idx = 0 /\
    v1.vs_prev_bb = SOME pred_bb.bb_label /\
    (!k ctx' s'.
       k <= n /\
       ~s'.vs_halted /\
       s'.vs_current_bb <>
         split_block_name pred_bb.bb_label target_bb.bb_label /\
       s'.vs_inst_idx = 0 /\
       s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <>
          SOME (split_block_name pred_bb.bb_label target_bb.bb_label)) ==>
      ?fuel'. fuel' >= k /\
        result_equiv UNIV (run_blocks k ctx' func s')
          (run_blocks fuel' ctx'
            (insert_split func pred_bb target_bb id_base) s')) ==>
    ?fuel'. fuel' >= SUC n /\
      result_equiv UNIV (run_blocks n ctx func v1)
        (run_blocks fuel' ctx
          (insert_split func pred_bb target_bb id_base) s)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `func' = insert_split func pred_bb target_bb id_base` >>
  qabbrev_tac `split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label` >>
  (* === Setup === *)
  `?split_bb var_repls.
     build_split_block pred_bb target_bb id_base = (split_bb, var_repls)` by
    metis_tac[pairTheory.PAIR] >>
  `split_bb.bb_label = split_lbl` by (
    qunabbrev_tac `split_lbl` >>
    drule cfgNormSimTheory.build_split_block_label >> simp[]) >>
  `lookup_block pred_bb.bb_label func.fn_blocks = SOME pred_bb` by
    metis_tac[MEM_lookup_block, fn_labels_def] >>
  `lookup_block target_bb.bb_label func.fn_blocks = SOME target_bb` by
    metis_tac[MEM_lookup_block, fn_labels_def] >>
  qabbrev_tac `subst_pred =
    subst_label_terminator target_bb.bb_label split_lbl pred_bb` >>
  `lookup_block pred_bb.bb_label func'.fn_blocks = SOME subst_pred` by (
    qunabbrev_tac `func'` >> qunabbrev_tac `split_lbl` >>
    qunabbrev_tac `subst_pred` >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
              cfgNormSimTheory.lookup_block_insert_split_pred) >>
    simp[LET_THM] >> pairarg_tac >> gvs[]) >>
  `lookup_block split_lbl func'.fn_blocks = SOME split_bb` by (
    qunabbrev_tac `func'` >> qunabbrev_tac `split_lbl` >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
              cfgNormSimTheory.lookup_block_insert_split_new) >>
    simp[LET_THM] >> pairarg_tac >> fs[]) >>
  qabbrev_tac `updated_target =
    update_phis_for_split pred_bb.bb_label split_lbl var_repls target_bb` >>
  `lookup_block target_bb.bb_label func'.fn_blocks = SOME updated_target` by (
    qunabbrev_tac `func'` >> qunabbrev_tac `split_lbl` >>
    qunabbrev_tac `updated_target` >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
              cfgNormSimTheory.lookup_block_insert_split_target) >>
    simp[LET_THM] >> pairarg_tac >> fs[]) >>
  (* subst_label_general for pred — run_block_entry level *)
  `!k. run_block_entry k ctx subst_pred s =
   (case run_block_entry k ctx pred_bb s of
      OK v => OK (if v.vs_current_bb = target_bb.bb_label
                  then v with vs_current_bb := split_lbl
                  else v)
    | other => other)` by (
    qunabbrev_tac `subst_pred` >>
    simp[run_block_subst_label_run_block]) >>
  (* Split n = 0 vs n = SUC m *)
  Cases_on `n` >- (
    (* n = 0 *)
    qexists_tac `1` >> conj_tac >- decide_tac >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `func'`,
      `ctx`, `s`, `v1`] insert_split_target_fuel0) >>
    simp[]
  ) >>
  rename1 `SUC m` >>
  `lookup_block v1.vs_current_bb func.fn_blocks = SOME target_bb` by simp[] >>
  `bb_well_formed target_bb` by fs[wf_function_no_ids_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) target_bb.bb_instructions)` by
    res_tac >>
  (* phi_fwd_vars_defined when run_block_entry not Error *)
  `(!e. run_block_entry m ctx target_bb v1 <> Error e) ==>
   !var. MEM var (nub (phi_vars_needing_forward pred_bb.bb_label
           pred_bb target_bb.bb_instructions)) ==>
     var IN FDOM v1.vs_vars` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`m`, `ctx`, `target_bb`, `v1`, `func`,
      `pred_bb.bb_label`, `pred_bb`, `var`]
      run_block_entry_non_error_phi_fwd_vars_defined) >>
    simp[] >> metis_tac[listTheory.MEM_nub]) >>
  `!v. MEM v (nub (phi_vars_needing_forward pred_bb.bb_label
           pred_bb target_bb.bb_instructions)) ==>
     !w. v <> STRCAT (STRCAT split_lbl "_fwd_") w` by (
    rpt strip_tac >>
    `MEM v (fn_all_vars func)` by (
      mp_tac (Q.SPECL [`func`, `target_bb`, `pred_bb.bb_label`,
        `pred_bb`, `v`] phi_fwd_var_in_fn_all_vars) >>
      simp[] >> metis_tac[listTheory.MEM_nub]) >>
    qunabbrev_tac `split_lbl` >>
    CCONTR_TAC >> fs[] >> metis_tac[]) >>
  `run_block_entry (SUC m) ctx pred_bb s = OK v1` by (
    mp_tac (Q.SPECL [`m`, `SUC m`, `ctx`, `pred_bb`, `s`, `v1`]
      venomExecPropsTheory.run_block_fuel_mono_OK) >>
    impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> simp[]) >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  `run_block_entry (SUC m) ctx subst_pred s =
     OK (v1 with vs_current_bb := split_lbl)` by (
    qpat_x_assum `!k. run_block_entry k ctx subst_pred s = _`
      (qspec_then `SUC m` mp_tac) >>
    gvs[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"]) >>
  `bb_well_formed pred_bb` by fs[wf_function_no_ids_def] >>
  `bb_well_formed subst_pred`
    by metis_tac[bb_well_formed_subst_label_terminator] >>
  `!f. f >= SUC m ==>
     run_block_entry f ctx subst_pred s =
       OK (v1 with vs_current_bb := split_lbl)` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`SUC m`, `f`, `ctx`, `subst_pred`, `s`,
      `v1 with vs_current_bb := split_lbl`]
      venomExecPropsTheory.run_block_fuel_mono_OK) >>
    impl_tac >- (
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `f >= SUC m` mp_tac >> decide_tac) >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  `func' = insert_split func pred_bb target_bb id_base` by simp[Abbr `func'`] >>
  `split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label` by simp[Abbr `split_lbl`] >>
  `subst_pred = subst_label_terminator target_bb.bb_label split_lbl pred_bb` by simp[Abbr `subst_pred`] >>
  `updated_target = update_phis_for_split pred_bb.bb_label split_lbl var_repls target_bb` by simp[Abbr `updated_target`] >>
  Cases_on `m` >- (
    qexists_tac `1` >> conj_tac >- decide_tac >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
      `func'`, `ctx`, `s`, `v1`] insert_split_target_fuel0) >>
    impl_tac >- (
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  rename1 `run_blocks (SUC m) ctx func v1` >>
  `v1.vs_current_bb = target_bb.bb_label` by (
    mp_tac (Q.SPECL [`v1.vs_current_bb`, `func.fn_blocks`, `target_bb`]
      lookup_block_label) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    simp[]) >>
  `run_block_entry (SUC m) ctx subst_pred s =
     OK (v1 with vs_current_bb := split_lbl)` by (
    irule subst_label_run_block_entry_target_ok >>
    qexists_tac `pred_bb` >>
    qexists_tac `target_bb.bb_label` >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!f. f >= SUC m ==>
     run_block_entry f ctx subst_pred s =
       OK (v1 with vs_current_bb := split_lbl)` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`SUC m`, `f`, `ctx`, `subst_pred`, `s`,
      `v1 with vs_current_bb := split_lbl`]
      venomExecPropsTheory.run_block_fuel_mono_OK) >>
    impl_tac >- (
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `f >= SUC m` mp_tac >> decide_tac) >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  (* === Dispatch to helper theorems === *)
  (* Error case — already handled by run_block_fuel_mono_OK above *)
  `(!e. run_block_entry m ctx target_bb v1 = Error e ==>
   ?fuel'. fuel' >= SUC (SUC m) /\
     result_equiv UNIV (Error e) (run_blocks fuel' ctx func' s))` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `func'`,
      `split_lbl`, `split_bb`, `var_repls`, `subst_pred`, `updated_target`,
      `m`, `ctx`, `s`, `v1`, `e`]
      insert_split_target_error_case) >>
    impl_tac >- (
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  (* Unfold original run_blocks once, then dispatch on target block result. *)
  `run_blocks (SUC m) ctx func v1 =
    case run_block_entry m ctx target_bb v1 of
      OK s'' => if s''.vs_halted then Halt s'' else run_blocks m ctx func s''
    | Halt v => Halt v | Abort a s' => Abort a s'
    | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
    mp_tac (Q.SPECL [`m`, `ctx`, `func`, `v1`, `target_bb`]
      run_blocks_SUC_lookup_SOME) >>
    simp[]) >>
  pop_assum SUBST1_TAC >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `func'`,
    `split_lbl`, `split_bb`, `var_repls`, `subst_pred`, `updated_target`,
    `m`, `ctx`, `s`, `v1`, `run_block_entry m ctx target_bb v1`]
    insert_split_target_result_dispatch) >>
  impl_tac >- (
    rpt conj_tac >> TRY (asm_rewrite_tac[]) >> TRY (FIRST_X_ASSUM ACCEPT_TAC) >>
    rpt gen_tac >> strip_tac >>
    qunabbrev_tac `func'` >>
    qunabbrev_tac `split_lbl` >>
    qpat_x_assum `!k ctx' s'. k <= SUC m /\ _ ==> _`
      (qspecl_then [`k`, `ctx'`, `s'`] mp_tac) >>
    impl_tac >- (
      rpt conj_tac >> TRY (asm_rewrite_tac[]) >>
      qpat_x_assum `k <= m` mp_tac >> simp[]) >>
    simp[]) >>
  DISCH_THEN ACCEPT_TAC
QED
(* One step of insert_split simulation for pred_bb *)
Triviality bb_well_formed_non_term_prefix[local]:
  !bb i.
    bb_well_formed bb /\
    i < LENGTH bb.bb_instructions - 1 ==>
    ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  rw[bb_well_formed_def] >>
  spose_not_then strip_assume_tac >>
  `i < LENGTH bb.bb_instructions` by DECIDE_TAC >>
  `i = PRE (LENGTH bb.bb_instructions)` by (
    first_x_assum match_mp_tac >> simp[]) >>
  DECIDE_TAC
QED

Theorem insert_split_pred_step[local]:
  !func pred_bb target_bb id_base func' split_lbl n ctx s cur_bb.
    wf_function_no_ids func /\
    fn_inst_wf func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    ALL_DISTINCT (fn_labels func) /\
    (!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM split_lbl (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT split_lbl "_fwd_") var)
                (fn_all_vars func)) /\
    func' = insert_split func pred_bb target_bb id_base /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    ~s.vs_halted /\
    s.vs_current_bb = pred_bb.bb_label /\
    s.vs_inst_idx = 0 /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME cur_bb /\
    s.vs_labels = FEMPTY /\
    (!k ctx' s'.
       k <= n /\
       ~s'.vs_halted /\
       s'.vs_current_bb <> split_lbl /\
       s'.vs_inst_idx = 0 /\
       s'.vs_labels = FEMPTY /\
       (s'.vs_current_bb = target_bb.bb_label ==>
        s'.vs_prev_bb <> SOME pred_bb.bb_label /\
        s'.vs_prev_bb <> SOME split_lbl) ==>
      ?fuel'. fuel' >= k /\
        result_equiv UNIV (run_blocks k ctx' func s')
                          (run_blocks fuel' ctx' func' s')) ==>
    ?fuel'. fuel' >= SUC n /\
      result_equiv UNIV (run_blocks (SUC n) ctx func s)
                        (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `func' = _` SUBST_ALL_TAC >>
  qpat_x_assum `split_lbl = _` SUBST_ALL_TAC >>
  `lookup_block pred_bb.bb_label func.fn_blocks = SOME pred_bb` by
    metis_tac[MEM_lookup_block, fn_labels_def] >>
  `cur_bb = pred_bb` by
    (`SOME cur_bb = SOME pred_bb` by metis_tac[] >> fs[]) >>
  qpat_x_assum `cur_bb = pred_bb` SUBST_ALL_TAC >>
  `?split_bb var_repls.
     build_split_block pred_bb target_bb id_base = (split_bb, var_repls)` by
    metis_tac[pairTheory.PAIR] >>
  `split_bb.bb_label =
     split_block_name pred_bb.bb_label target_bb.bb_label` by (
    drule build_split_block_label >> simp[]) >>
  `lookup_block pred_bb.bb_label
     (insert_split func pred_bb target_bb id_base).fn_blocks =
   SOME (subst_label_terminator target_bb.bb_label
     (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb)` by (
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
              lookup_block_insert_split_pred) >>
    simp[LET_THM] >> pairarg_tac >> fs[]) >>
  (* Establish run_block relationship using ~s.vs_halted *)
  `run_block n ctx (subst_label_terminator target_bb.bb_label
     (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) s =
   (case run_block n ctx pred_bb s of
      OK v => OK (if v.vs_current_bb = target_bb.bb_label
                  then v with vs_current_bb :=
                    split_block_name pred_bb.bb_label target_bb.bb_label
                  else v)
    | other => other)` by
    simp[run_block_subst_label_run_block] >>
  (* Move IH to goal to prevent simp/metis from touching it *)
  Q.PAT_ASSUM `!k ctx' s'. _` mp_tac >>
  (* Unfold LHS run_blocks *)
  `run_blocks (SUC n) ctx func s =
     (case run_block n ctx pred_bb s of
        OK s' => if s'.vs_halted then Halt s'
                 else run_blocks n ctx func s'
      | Halt v => Halt v
      | Abort a v => Abort a v
      | IntRet vals v => IntRet vals v
      | Error e => Error e)` by
    metis_tac[run_blocks_SUC_lookup_SOME] >>
  strip_tac >>
  (* Case split on run_block result *)
  Cases_on `run_block n ctx pred_bb s` >> gvs[Excl "run_block_def"] >>
  (* non-OK cases: both sides give same result, result_equiv_UNIV_refl *)
  TRY (qexists_tac `SUC n` >> simp[] >>
       PURE_ONCE_REWRITE_TAC[run_blocks_unfold] >>
       simp[result_equiv_UNIV_refl] >> NO_TAC) >>
  (* OK case remains *)
  rename1 `run_block n ctx pred_bb s = OK v1` >>
  Cases_on `v1.vs_halted` >> gvs[Excl "run_block_def"] >>
  TRY (qexists_tac `SUC n` >> simp[] >>
       PURE_ONCE_REWRITE_TAC[run_blocks_unfold] >>
       simp[COND_RAND, COND_RATOR, result_equiv_UNIV_refl] >>
       simp[result_equiv_def, execution_equiv_def] >>
       Cases_on `v1.vs_current_bb = target_bb.bb_label` >>
       simp[lookup_var_def] >> NO_TAC) >>
  (* ~v1.vs_halted: common setup for both C3b subcases *)
  `v1.vs_inst_idx = 0` by metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `bb_well_formed pred_bb` by (fs[wf_function_no_ids_def] >> metis_tac[]) >>
  `EVERY inst_wf pred_bb.bb_instructions` by (
    simp[listTheory.EVERY_MEM] >>
    rpt strip_tac >>
    fs[fn_inst_wf_def] >> res_tac) >>
  `MEM v1.vs_current_bb (fn_labels func)` by (
    mp_tac (Q.SPECL [`n`, `ctx`, `pred_bb`, `s`, `v1`, `func`]
              run_block_ok_succ_in_labels) >> simp[Excl "run_block_def"]) >>
  `v1.vs_current_bb <> split_block_name pred_bb.bb_label target_bb.bb_label` by
    (strip_tac >> fs[]) >>
  `pred_bb.bb_instructions <> []` by
    metis_tac[venomExecPropsTheory.run_block_ok_nonempty] >>
  `!i. i < LENGTH pred_bb.bb_instructions - 1 ==>
       ~is_terminator (EL i pred_bb.bb_instructions).inst_opcode` by
    metis_tac[bb_well_formed_non_term_prefix] >>
  `v1.vs_prev_bb = SOME pred_bb.bb_label` by (
    mp_tac (Q.SPECL [`n`, `ctx`, `pred_bb`, `s`, `v1`]
      venomExecPropsTheory.run_block_ok_prev_bb_exact) >> simp[Excl "run_block_def"]) >>
  Cases_on `v1.vs_current_bb = target_bb.bb_label` >-
  ((* Case C3b-target: delegate to insert_split_target_from_pred *)
   mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
     `n`, `ctx`, `s`, `v1`] insert_split_target_from_pred) >>
   simp[Excl "run_block_def", Excl "run_blocks_def"]) >>
  (* Step 2: Simplify subst_label run_block assumption *)
  `run_block n ctx
     (subst_label_terminator target_bb.bb_label
        (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) s =
   OK v1` by fs[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def"] >>
  (* Derive vs_labels preservation for IH *)
  `v1.vs_labels = FEMPTY` by (
    mp_tac (Q.SPECL [`n`, `ctx`,
      `subst_label_terminator target_bb.bb_label
         (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb`,
      `s`, `v1`]
      venomExecPropsTheory.run_block_preserves_labels) >> simp[Excl "run_block_def"]) >>
  (* Step 3: Apply IH to v1 *)
  Q.PAT_ASSUM `!k ctx' s'. _` (qspecl_then [`n`, `ctx`, `v1`] mp_tac) >>
  (impl_tac >- simp[Excl "run_block_def", Excl "run_blocks_def"]) >>
  disch_then strip_assume_tac >>
  rename1 `fuel_ih >= n` >>
  (* Step 4: Bump fuel on run_block from n to fuel_ih *)
  `run_block fuel_ih ctx
     (subst_label_terminator target_bb.bb_label
        (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) s =
   OK v1` by (
    drule venomExecPropsTheory.run_block_fuel_mono_OK >>
    simp[Excl "run_block_def"]) >>
  (* Step 5: Unfold RHS one step: run_blocks (SUC fuel_ih) ctx func' s *)
  qexists_tac `SUC fuel_ih` >>
  conj_tac >- decide_tac >>
  PURE_ONCE_REWRITE_TAC[run_blocks_unfold] >>
  asm_rewrite_tac[] >>
  Cases_on `run_block fuel_ih ctx
    (subst_label_terminator target_bb.bb_label
       (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) s` >>
  gvs[Excl "run_block_def", Excl "run_block_entry_def", Excl "run_blocks_def",
       AllCaseEqs(), result_equiv_def]
QED

(* The main correctness theorem: fuel induction, same state *)
Theorem insert_split_correct:
  !func pred_bb target_bb id_base.
    wf_function_no_ids func /\
    fn_inst_wf func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    ALL_DISTINCT (fn_labels func) /\
    (!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    (!var. ~MEM (STRCAT (STRCAT (split_block_name pred_bb.bb_label
                  target_bb.bb_label) "_fwd_") var)
                (fn_all_vars func)) ==>
    let func' = insert_split func pred_bb target_bb id_base in
    let split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label in
    !fuel ctx s.
      ~s.vs_halted /\
      s.vs_current_bb <> split_lbl /\
      s.vs_inst_idx = 0 /\
      s.vs_labels = FEMPTY /\
      (s.vs_current_bb = target_bb.bb_label ==>
       s.vs_prev_bb <> SOME pred_bb.bb_label /\
       s.vs_prev_bb <> SOME split_lbl) ==>
      ?fuel'. fuel' >= fuel /\
        result_equiv UNIV
          (run_blocks fuel ctx func s)
          (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >>
  simp[LET_THM] >> BETA_TAC >>
  completeInduct_on `fuel` >>
  rpt strip_tac >>
  Cases_on `fuel` >-
  (* Base: fuel = 0 *)
  (once_rewrite_tac[run_blocks_def] >> simp[Excl "run_block_def"] >>
   qexists_tac `0` >> once_rewrite_tac[run_blocks_def] >>
   simp[result_equiv_UNIV_refl]) >>
  rename1 `SUC n` >>
  (* Step: fuel = SUC n, IH: !m. m < SUC n ==> P m *)
  Cases_on `s.vs_current_bb = pred_bb.bb_label` >-
  ((* At pred_bb: use insert_split_pred_step *)
   `lookup_block pred_bb.bb_label func.fn_blocks = SOME pred_bb` by
     metis_tac[MEM_lookup_block, fn_labels_def] >>
   `!k ctx' s'.
      k <= n /\
      ~s'.vs_halted /\
      s'.vs_current_bb <>
        split_block_name pred_bb.bb_label target_bb.bb_label /\
      s'.vs_inst_idx = 0 /\
      s'.vs_labels = FEMPTY /\
      (s'.vs_current_bb = target_bb.bb_label ==>
       s'.vs_prev_bb <> SOME pred_bb.bb_label /\
       s'.vs_prev_bb <> SOME
         (split_block_name pred_bb.bb_label target_bb.bb_label)) ==>
     ?fuel'. fuel' >= k /\
       result_equiv UNIV (run_blocks k ctx' func s')
         (run_blocks fuel' ctx'
           (insert_split func pred_bb target_bb id_base) s')` by (
     rpt strip_tac >>
     Q.PAT_ASSUM `!m. m < SUC n ==> _` (qspec_then `k` mp_tac) >>
     simp[] >>
     disch_then (qspecl_then [`ctx'`, `s'`] mp_tac) >> simp[]) >>
   mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
     `insert_split func pred_bb target_bb id_base`,
     `split_block_name pred_bb.bb_label target_bb.bb_label`,
     `n`, `ctx`, `s`, `pred_bb`] insert_split_pred_step) >>
   simp[]) >>
  (* Not pred_bb: case split on target_bb *)
  Cases_on `s.vs_current_bb = target_bb.bb_label` >-
  ((* At target_bb: use insert_split_target_step *)
   `lookup_block s.vs_current_bb func.fn_blocks = SOME target_bb` by
     metis_tac[MEM_lookup_block, fn_labels_def] >>
   mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
     `insert_split func pred_bb target_bb id_base`,
     `split_block_name pred_bb.bb_label target_bb.bb_label`,
     `n`, `ctx`, `s`, `target_bb`] insert_split_target_step) >>
   simp[] >>
   disch_then match_mp_tac >>
   rpt strip_tac >>
   Q.PAT_ASSUM `!m. m < SUC n ==> _` (qspec_then `n` mp_tac) >>
   simp[] >>
   disch_then (qspecl_then [`ctx'`, `s'`] mp_tac) >> simp[]) >>
  (* Other blocks: use insert_split_other_step *)
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >-
  ((* lookup fails: both sides return Error *)
   simp[Once run_blocks_def] >>
   qexists_tac `SUC n` >> simp[Once run_blocks_def] >>
   `lookup_block s.vs_current_bb
      (insert_split func pred_bb target_bb id_base).fn_blocks = NONE` by
     simp[lookup_insert_split_other] >>
   simp[result_equiv_UNIV_refl]) >>
  rename1 `SOME cur_bb` >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
    `insert_split func pred_bb target_bb id_base`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `n`, `ctx`, `s`, `cur_bb`] insert_split_other_step) >>
  simp[] >>
  disch_then match_mp_tac >>
  rpt strip_tac >>
  Q.PAT_ASSUM `!m. m < SUC n ==> _` (qspec_then `n` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`ctx'`, `s'`] mp_tac) >> simp[]
QED

val _ = export_theory();
