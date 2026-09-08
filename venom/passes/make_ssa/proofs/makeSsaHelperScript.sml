(*
 * Make SSA Pass — Helper Lemmas
 *
 * Infrastructure for the make_ssa_fn correctness proof:
 *   1. Label preservation through make_ssa_fn pipeline
 *   2. run_block_ssa_sim: per-block simulation
 *   3. Non-aliasing / colon_free / version_var injectivity
 *   4. PHI prefix simulation and phi_args_ok discharge
 *   5. Lockstep body simulation (concrete + abstract sigma)
 *   6. Well-formedness preservation (make_ssa_preserves_wf_function)
 *   7. Pipeline correspondence (rename_blocks_body_match, bbs_outputs_agree)
 *
 * Core simulation definitions: ssaSimDefs. Per-instruction sim: ssaRenamedSim.
 * Top-level theorem: makeSsaProofScript.
 *)

Theory makeSsaHelper
Ancestors
  ssaSimDefs ssaRenamedSim ssaPipeline makeSsaDefs stateEquiv
  venomExecSemantics venomExecProofs venomWf venomState venomInst
  cfgTransform cfgTransformProps passSimulationDefs passSimulationProps
  execEquivParamDefs execEquivParamProofs
  list rich_list alist finite_map pred_set string arithmetic

(* ALOOKUP CASE elimination helper *)
Theorem alookup_case_elim[local]:
  ALOOKUP l k = SOME v ==>
  (case ALOOKUP l k of NONE => d | SOME r => r) = v
Proof
  simp[]
QED

val elim_alookup_case = fn th =>
  PURE_REWRITE_TAC [MATCH_MP alookup_case_elim th];

(* ==========================================================================
   Part 1: Label preservation through make_ssa_fn pipeline
   ========================================================================== *)

Theorem replace_block_preserves_labels:
  !lbl bb' bbs.
    bb'.bb_label = lbl ==>
    MAP (\bb. bb.bb_label) (replace_block lbl bb' bbs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  Induct_on `bbs` >> rw[replace_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> rw[]
QED

(* process_frontiers only inserts PHI instructions, preserving labels *)
Theorem process_frontiers_preserves_labels[local]:
  !var pred_map live_in bbs rest has_phi fs.
    MAP (\bb. bb.bb_label)
      (FST (process_frontiers var pred_map live_in bbs rest has_phi fs)) =
    MAP (\bb. bb.bb_label) bbs
Proof
  Induct_on `fs` >>
  rw[process_frontiers_def, LET_THM] >>
  rw[MAP_MAP_o, combinTheory.o_DEF, insert_phi_at_block_def] >>
  irule MAP_CONG >> rw[]
QED

(* insert_phis_for_var preserves labels *)
Theorem insert_phis_for_var_preserves_labels[local]:
  !var df pred_map live_in bbs def_blocks wl.
    MAP (\bb. bb.bb_label)
      (insert_phis_for_var var df pred_map live_in bbs def_blocks wl) =
    MAP (\bb. bb.bb_label) bbs
Proof
  ho_match_mp_tac insert_phis_for_var_ind >>
  rw[insert_phis_for_var_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  first_x_assum (fn th =>
    `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs`
      suffices_by (strip_tac >> gvs[]) >>
    mp_tac (GSYM th) >> simp[pairTheory.PAIR_FST_SND_EQ] >>
    strip_tac >> gvs[process_frontiers_preserves_labels])
QED

(* add_phi_nodes preserves labels *)
Theorem add_phi_nodes_preserves_labels:
  !defs df pred_map live_in bbs.
    MAP (\bb. bb.bb_label)
      (add_phi_nodes df pred_map live_in bbs defs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  Induct >> rw[add_phi_nodes_def] >>
  PairCases_on `h` >> rw[] >>
  rw[GSYM add_phi_nodes_def] >>
  rw[insert_phis_for_var_preserves_labels]
QED

(* General FOLDL label preservation: each step preserves labels *)
Theorem foldl_preserves_labels[local]:
  !f xs bbs.
    (!x bbs'. MAP (\bb. bb.bb_label) (f bbs' x) = MAP (\bb. bb.bb_label) bbs') ==>
    MAP (\bb. bb.bb_label) (FOLDL f bbs xs) = MAP (\bb. bb.bb_label) bbs
Proof
  Induct_on `xs` >> rw[]
QED

(* lookup_block returns a block whose label matches *)
Theorem lookup_block_label:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >> gvs[] >>
  first_x_assum irule >> gvs[lookup_block_def]
QED

(* update_succ_phis preserves labels *)
Theorem update_succ_phis_preserves_labels:
  !rs lbl bbs succs.
    MAP (\bb. bb.bb_label) (update_succ_phis rs lbl bbs succs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  rw[update_succ_phis_def] >>
  irule foldl_preserves_labels >> rw[] >>
  CASE_TAC >> rw[] >>
  irule replace_block_preserves_labels >>
  imp_res_tac lookup_block_label >> rw[]
QED

(* rename_blocks and rename_children both preserve labels — mutual induction *)
Theorem rename_blocks_children_preserves_labels[local]:
  (!dtree rs bbs succ_map.
    MAP (\bb. bb.bb_label)
      (SND (rename_blocks rs bbs succ_map dtree)) =
    MAP (\bb. bb.bb_label) bbs) /\
  (!children ctrs stacks bbs succ_map.
    MAP (\bb. bb.bb_label)
      (SND (rename_children ctrs stacks bbs succ_map children)) =
    MAP (\bb. bb.bb_label) bbs)
Proof
  HO_MATCH_MP_TAC makeSsaDefsTheory.dom_tree_induction >>
  rpt conj_tac
  >- (
    rpt strip_tac >>
    simp[Once rename_blocks_def] >>
    Cases_on `lookup_block s bbs` >> simp[] >>
    pairarg_tac >> gvs[] >>
    simp[update_succ_phis_preserves_labels] >>
    irule replace_block_preserves_labels >>
    imp_res_tac lookup_block_label >> simp[]
  )
  >- simp[rename_blocks_def]
  >- (
    rpt strip_tac >>
    simp[Once rename_blocks_def, LET_THM] >>
    pairarg_tac >> gvs[] >>
    `SND (rename_blocks (ctrs,stacks) bbs succ_map dtree) = bbs'` by
      simp[] >>
    metis_tac[]
  )
QED

Theorem rename_blocks_preserves_labels:
  !rs bbs succ_map dtree.
    MAP (\bb. bb.bb_label)
      (SND (rename_blocks rs bbs succ_map dtree)) =
    MAP (\bb. bb.bb_label) bbs
Proof
  metis_tac[rename_blocks_children_preserves_labels]
QED

(* Full pipeline label preservation *)
Theorem make_ssa_fn_preserves_labels:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    MAP (\bb. bb.bb_label)
      (make_ssa_fn dom_frontiers dtree dom_post_order
        pred_map succ_map live_in func).fn_blocks =
    MAP (\bb. bb.bb_label) func.fn_blocks
Proof
  rw[make_ssa_fn_def, LET_THM] >>
  CASE_TAC >> simp[] >>
  pairarg_tac >> gvs[] >>
  `SND (rename_blocks (init_rename_state
    (compute_defs
      (MAP THE
        (FILTER IS_SOME
          (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))))
    (add_phi_nodes dom_frontiers pred_map live_in func.fn_blocks
      (compute_defs
        (MAP THE
          (FILTER IS_SOME
            (MAP (\lbl. lookup_block lbl func.fn_blocks) dom_post_order)))))
    succ_map dtree) = bbs2` by simp[] >>
  metis_tac[rename_blocks_preserves_labels, add_phi_nodes_preserves_labels]
QED

(* ==========================================================================
   Part 2: Lookup block agreement under label preservation
   ========================================================================== *)

(* Lookup agreement: if labels are preserved, lookup_block agrees *)
Theorem lookup_block_labels_agree:
  !bbs1 bbs2.
    MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) bbs2 ==>
    !lbl. IS_SOME (lookup_block lbl bbs1) <=> IS_SOME (lookup_block lbl bbs2)
Proof
  Induct >> Cases_on `bbs2` >> simp[lookup_block_def] >>
  simp[lookup_block_def, FIND_thm] >> rpt gen_tac >> strip_tac >>
  gen_tac >> Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def]
QED

(* Corollary: lookup_block NONE/SOME agreement — curried for drule *)
Theorem lookup_block_none_agree[local]:
  !bbs1 bbs2 lbl.
    MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) bbs2 ==>
    lookup_block lbl bbs1 = NONE ==>
    lookup_block lbl bbs2 = NONE
Proof
  rpt strip_tac >>
  imp_res_tac lookup_block_labels_agree >>
  Cases_on `lookup_block lbl bbs2` >> simp[] >>
  `IS_SOME (lookup_block lbl bbs2)` by simp[] >>
  metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem lookup_block_some_agree[local]:
  !bbs1 bbs2 lbl bb.
    MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) bbs2 ==>
    lookup_block lbl bbs1 = SOME bb ==>
    ?bb'. lookup_block lbl bbs2 = SOME bb'
Proof
  rpt strip_tac >>
  imp_res_tac lookup_block_labels_agree >>
  Cases_on `lookup_block lbl bbs2` >> simp[] >>
  `~IS_SOME (lookup_block lbl bbs2)` by simp[] >>
  metis_tac[optionTheory.IS_SOME_DEF]
QED

(* ==========================================================================
   Part 3: Pipeline-to-simulation correspondence
   
   Key abstraction: the pipeline's latest_version IS the simulation's sigma.
   rename_operands computes MAP (renamed_operand sigma) for sigma = latest_version.
   rename_inst produces inst_renamed-related instructions.
   ========================================================================== *)

(* rename_operands is MAP (renamed_operand (latest_version rs)) *)
Theorem rename_operands_eq_map[local]:
  !rs ops.
    rename_operands rs ops =
    MAP (renamed_operand (latest_version rs)) ops
Proof
  Induct_on `ops` >> rw[rename_operands_def, renamed_operand_def, MAP] >>
  Cases_on `h` >> rw[rename_operands_def, renamed_operand_def]
QED

(* rename_outputs preserves length *)
Theorem rename_outputs_length[local]:
  !outs rs. LENGTH (SND (rename_outputs rs outs)) = LENGTH outs
Proof
  Induct >> rw[rename_outputs_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND]
QED

(* rename_inst preserves opcode *)
Theorem rename_inst_opcode_preserved:
  !rs inst. (SND (rename_inst rs inst)).inst_opcode = inst.inst_opcode
Proof
  rw[rename_inst_def, LET_THM] >> pairarg_tac >> gvs[]
QED

(* rename_inst preserves inst_id *)
Theorem rename_inst_id_preserved[local]:
  !rs inst. (SND (rename_inst rs inst)).inst_id = inst.inst_id
Proof
  rw[rename_inst_def, LET_THM] >> pairarg_tac >> gvs[]
QED

(* rename_inst preserves output length *)
Theorem rename_inst_outputs_length[local]:
  !rs inst.
    LENGTH (SND (rename_inst rs inst)).inst_outputs = LENGTH inst.inst_outputs
Proof
  rw[rename_inst_def, LET_THM] >> pairarg_tac >> gvs[] >>
  `LENGTH outs' = LENGTH (SND (rename_outputs rs inst.inst_outputs))`
    by simp[] >>
  gvs[rename_outputs_length]
QED

(* For non-PHI instructions, rename_inst produces renamed operands *)
Theorem rename_inst_non_phi_operands[local]:
  !rs inst.
    inst.inst_opcode <> PHI ==>
    (SND (rename_inst rs inst)).inst_operands =
      MAP (renamed_operand (latest_version rs)) inst.inst_operands
Proof
  rw[rename_inst_def, LET_THM] >>
  pairarg_tac >> gvs[rename_operands_eq_map]
QED

(* rename_block_insts preserves length *)
Theorem rename_block_insts_length:
  !insts rs.
    LENGTH (SND (rename_block_insts rs insts)) = LENGTH insts
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[pairTheory.SND]
QED

(* rename_block_insts preserves opcodes *)
Theorem rename_block_insts_opcodes[local]:
  !insts rs j.
    j < LENGTH insts ==>
    (EL j (SND (rename_block_insts rs insts))).inst_opcode =
      (EL j insts).inst_opcode
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `j` >> gvs[]
  >- metis_tac[rename_inst_opcode_preserved, pairTheory.SND]
  >- metis_tac[pairTheory.SND]
QED

(* rename_block_insts preserves inst_ids *)
Theorem rename_block_insts_ids[local]:
  !insts rs j.
    j < LENGTH insts ==>
    (EL j (SND (rename_block_insts rs insts))).inst_id =
      (EL j insts).inst_id
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `j` >> gvs[]
  >- metis_tac[rename_inst_id_preserved, pairTheory.SND]
  >- metis_tac[pairTheory.SND]
QED

(* ==========================================================================
   Part 3b: Pipeline PHI properties

   Key lemma: update_phi_for_pred + resolve_phi correspondence.
   After update_phi_for_pred rs lbl ops, resolving for lbl gives the
   renamed_operand (latest_version rs) applied to the original resolve result.
   ========================================================================== *)

(* resolve_phi after update_phi_for_pred: renaming for the matching label *)
Theorem resolve_phi_update_phi_for_pred[local]:
  !rs lbl ops.
    resolve_phi lbl (update_phi_for_pred rs lbl ops) =
    OPTION_MAP (renamed_operand (latest_version rs)) (resolve_phi lbl ops)
Proof
  ho_match_mp_tac update_phi_for_pred_ind >>
  rw[resolve_phi_def, update_phi_for_pred_def, renamed_operand_def] >>
  Cases_on `x` >> rw[resolve_phi_def, renamed_operand_def]
QED

(* resolve_phi after update_phi_for_pred for a DIFFERENT label: unchanged *)
Theorem resolve_phi_update_phi_for_pred_other[local]:
  !rs lbl ops lbl'.
    lbl' <> lbl ==>
    resolve_phi lbl' (update_phi_for_pred rs lbl ops) =
    resolve_phi lbl' ops
Proof
  ho_match_mp_tac update_phi_for_pred_ind >>
  rw[resolve_phi_def, update_phi_for_pred_def] >>
  Cases_on `x` >> rw[resolve_phi_def]
QED

(* ==========================================================================
   Part 3c: Version variable injectivity under colon_free

   colon_free s: s contains no ':' character.
   Under this condition, version_var is injective in its base argument,
   which gives the non-aliasing property needed by ssa_sim_update_var.
   ========================================================================== *)

Definition colon_free_def:
  colon_free s <=> ~MEM #":" (EXPLODE s)
End

(* All variables defined in a state have colon-free names *)
Definition vars_colon_free_def:
  vars_colon_free s <=> !x. lookup_var x s <> NONE ==> colon_free x
End

(* vs_inst_idx is irrelevant to vars_colon_free *)
Theorem vars_colon_free_update_inst_idx[local]:
  !s n. vars_colon_free (s with vs_inst_idx := n) <=> vars_colon_free s
Proof
  rw[vars_colon_free_def, lookup_var_def]
QED

(* vars_colon_free is preserved by update_var with colon_free name *)
Theorem vars_colon_free_update[local]:
  !s name v. vars_colon_free s /\ colon_free name ==>
             vars_colon_free (update_var name v s)
Proof
  rw[vars_colon_free_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE] >>
  BasicProvers.every_case_tac >> metis_tac[]
QED

(* Small output-arity interface used to keep opcode branches local. *)
Theorem fdom_union_two_outputs_intro[local]:
  !d x a b.
    (x IN d \/ x = a \/ x = b) ==>
    x IN d UNION set [a; b]
Proof
  simp[IN_UNION]
QED

Theorem step_inst_base_DRET_not_OK_local[local]:
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

Theorem step_inst_base_RETFMP_not_OK_local[local]:
  !inst s r. inst.inst_opcode = RETFMP ==>
    step_inst_base inst s <> OK r
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  Cases_on `eval_operands inst.inst_operands s` >> gvs[] >>
  Cases_on `x` >> gvs[]
QED

val make_ssa_term_ok_jump_tac =
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, eval_operands_def, eval_operand_def,
       AllCaseEqs()] >>
  rpt CASE_TAC >> gvs[] >> rpt strip_tac >> pairarg_tac >> gvs[];

Theorem step_inst_base_ok_terminator_jump_local[local]:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
    inst.inst_opcode = DJMP
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  TRY (rename1 `inst.inst_opcode = DRET` >>
       metis_tac[step_inst_base_DRET_not_OK_local]) >>
  TRY (rename1 `inst.inst_opcode = RETFMP` >>
       metis_tac[step_inst_base_RETFMP_not_OK_local]) >>
  TRY (rename1 `inst.inst_opcode = RET` >> make_ssa_term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = RETURN` >> make_ssa_term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = REVERT` >> make_ssa_term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = STOP` >> make_ssa_term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = SINK` >> make_ssa_term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = SELFDESTRUCT` >> make_ssa_term_ok_jump_tac) >>
  TRY (rename1 `inst.inst_opcode = INVALID` >> make_ssa_term_ok_jump_tac)
QED

Theorem step_inst_base_as_step_inst_local[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    step_inst 0 ARB inst s = OK s'
Proof
  rw[Once step_inst_def] >>
  gvs[step_inst_base_def]
QED


(* step_inst_base only adds variables from inst_outputs.
   Key helper for vars_colon_free preservation.
   Strategy: ONCE_REWRITE to avoid full expansion, then per-opcode TRY. *)
Theorem step_inst_base_vars_subset[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    FDOM s'.vs_vars SUBSET FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  rw[SUBSET_DEF] >> rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all step_inst_base_ok_terminator_jump_local >>
      strip_tac >>
      gvs[step_inst_base_def, jump_to_def, AllCaseEqs()]) >>
  Cases_on `MEM x inst.inst_outputs`
  >- simp[IN_UNION] >>
  `lookup_var x s' = lookup_var x s` by
    metis_tac[step_inst_base_as_step_inst_local,
              venomInstProofsTheory.step_preserves_non_output_vars] >>
  gvs[lookup_var_def, FLOOKUP_DEF, IN_UNION]
QED

(* FOLDL update_var adds output names to vs_vars *)
Theorem foldl_update_var_vars_subset[local]:
  !pairs s.
    FDOM (FOLDL (\st (nm,vl). update_var nm vl st) s pairs).vs_vars
    SUBSET
    FDOM s.vs_vars UNION set (MAP FST pairs)
Proof
  Induct
  >- rw[SUBSET_DEF, IN_UNION] >>
  rpt gen_tac >>
  PairCases_on `h` >> simp[] >>
  first_x_assum (qspec_then `update_var h0 h1 s` mp_tac) >>
  rw[SUBSET_DEF, IN_UNION, update_var_def, FDOM_FUPDATE, IN_INSERT] >>
  metis_tac[]
QED

(* FOLDL update_var monotonically grows FDOM *)
Theorem foldl_update_var_vars_monotone[local]:
  !pairs s.
    FDOM s.vs_vars SUBSET
    FDOM (FOLDL (\st (nm,vl). update_var nm vl st) s pairs).vs_vars
Proof
  Induct
  >- rw[SUBSET_DEF] >>
  rpt gen_tac >>
  PairCases_on `h` >> simp[] >>
  first_x_assum (qspec_then `update_var h0 h1 s` mp_tac) >>
  rw[SUBSET_DEF, update_var_def, FDOM_FUPDATE, IN_INSERT] >>
  metis_tac[]
QED

(* FOLDL update_var includes all output names in FDOM *)
Theorem foldl_update_var_outputs_in_fdom[local]:
  !pairs s nm vl.
    MEM (nm, vl) pairs ==>
    nm IN FDOM (FOLDL (\st (nm,vl). update_var nm vl st) s pairs).vs_vars
Proof
  Induct
  >- rw[] >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >>
  strip_tac
  >- (
    `h0 IN FDOM (update_var h0 h1 s).vs_vars` by
      rw[update_var_def, FDOM_FUPDATE] >>
    mp_tac (Q.SPECL [`pairs`, `update_var h0 h1 s`]
      foldl_update_var_vars_monotone) >>
    rw[SUBSET_DEF]) >>
  metis_tac[]
QED

(* bind_outputs includes all output names in FDOM *)
Theorem bind_outputs_outputs_in_fdom[local]:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==>
    !out. MEM out outs ==> out IN FDOM s'.vs_vars
Proof
  rw[bind_outputs_def] >> gvs[] >>
  imp_res_tac MEM_ZIP_MEM_MAP >>
  `MEM out (MAP FST (ZIP (outs, vals)))` by
    (simp[MAP_ZIP] >> first_assum ACCEPT_TAC) >>
  gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  metis_tac[foldl_update_var_outputs_in_fdom]
QED

(* Non-terminator step_inst_base: outputs end up in FDOM.
   Requires well-formedness: opcodes without output have empty outputs list. *)
Theorem step_inst_base_outputs_in_fdom[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (~opcode_has_output inst.inst_opcode ==> inst.inst_outputs = []) ==>
    !out. MEM out inst.inst_outputs ==> out IN FDOM s'.vs_vars
Proof
  rpt gen_tac >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >>
  PURE_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  gvs[is_terminator_def] >>
  gvs[opcode_has_output_def] >>
  gvs[exec_pure1_def] >>
  gvs[exec_pure2_def] >>
  gvs[exec_pure3_def] >>
  gvs[exec_read0_def, exec_read1_def] >>
  gvs[exec_write2_def, exec_alloca_def] >>
  gvs[exec_ext_call_def] >>
  gvs[exec_delegatecall_def] >>
  gvs[exec_create_def] >>
  gvs[extract_venom_result_def] >>
  gvs[AllCaseEqs(), LET_THM] >>
  gvs[update_var_def, FDOM_FUPDATE] >>
  rpt strip_tac >> gvs[FDOM_FUPDATE]
QED

(* Non-terminator step_inst: outputs end up in FDOM (incl. INVOKE) *)
Theorem step_inst_outputs_in_fdom[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (~opcode_has_output inst.inst_opcode ==> inst.inst_outputs = []) ==>
    !out. MEM out inst.inst_outputs ==> out IN FDOM s'.vs_vars
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    rw[step_inst_def, is_terminator_def, opcode_has_output_def] >>
    gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
    imp_res_tac bind_outputs_outputs_in_fdom >>
    gvs[merge_callee_state_def, update_var_def, FDOM_FUPDATE])
  >>
  strip_tac >>
  `~is_terminator inst.inst_opcode` by gvs[] >>
  `step_inst fuel ctx inst s = step_inst_base inst s`
    by gvs[step_inst_non_invoke] >>
  gvs[] >>
  metis_tac[step_inst_base_outputs_in_fdom]
QED

(* step_inst_base monotonically grows FDOM vs_vars *)
Theorem step_inst_base_vars_monotone[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    FDOM s.vs_vars SUBSET FDOM s'.vs_vars
Proof
  rpt gen_tac >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >>
  PURE_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  gvs[exec_pure1_def] >>
  gvs[exec_pure2_def] >>
  gvs[exec_pure3_def] >>
  gvs[exec_read0_def, exec_read1_def] >>
  gvs[exec_write2_def, exec_alloca_def] >>
  gvs[exec_ext_call_def] >>
  gvs[exec_delegatecall_def] >>
  gvs[exec_create_def] >>
  gvs[extract_venom_result_def] >>
  gvs[AllCaseEqs(), LET_THM] >>
  gvs[update_var_def, FDOM_FUPDATE] >>
  gvs[jump_to_def, mcopy_def, mstore_def, istore_def, mstore8_def] >>
  gvs[sstore_def, tstore_def] >>
  gvs[halt_state_def, revert_state_def, set_returndata_def] >>
  rpt strip_tac >> gvs[SUBSET_DEF, IN_INSERT, IN_UNION] >>
  TRY (gvs[write_memory_with_expansion_def, LET_THM] >> NO_TAC) >>
  TRY (pairarg_tac >> gvs[update_var_def, FDOM_FUPDATE] >>
       gvs[SUBSET_DEF, IN_INSERT, IN_UNION] >> NO_TAC) >>
  TRY (Cases_on `result` >> gvs[AllCaseEqs()]) >>
  TRY (Cases_on `y` >> gvs[AllCaseEqs()]) >>
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* bind_outputs adds exactly the output variables *)
Theorem bind_outputs_vars_subset[local]:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==>
    FDOM s'.vs_vars SUBSET FDOM s.vs_vars UNION set outs
Proof
  rw[bind_outputs_def] >> gvs[] >>
  mp_tac (Q.SPECL [`ZIP (outs, vals)`, `s`] foldl_update_var_vars_subset) >>
  rw[SUBSET_DEF, IN_UNION] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  disj2_tac >>
  gvs[MEM_MAP, MEM_ZIP] >>
  metis_tac[MEM_EL]
QED

(* step_inst (including INVOKE) only adds variables from inst_outputs *)
Theorem step_inst_vars_subset[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==>
    FDOM s'.vs_vars SUBSET FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    rw[step_inst_def] >>
    gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
    imp_res_tac bind_outputs_vars_subset >>
    Cases_on `ret.iret_adopt_fmp` >>
    gvs[SUBSET_DEF, IN_UNION, merge_callee_state_def,
        adopt_return_fmp_def])
  >>
  rw[step_inst_non_invoke] >>
  imp_res_tac step_inst_base_vars_subset
QED

(* bind_outputs monotonically grows FDOM vs_vars *)
Theorem bind_outputs_vars_monotone[local]:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==>
    FDOM s.vs_vars SUBSET FDOM s'.vs_vars
Proof
  rw[bind_outputs_def] >> gvs[] >>
  mp_tac (Q.SPECL [`ZIP (outs, vals)`, `s`] foldl_update_var_vars_monotone) >>
  rw[]
QED

(* step_inst (including INVOKE) monotonically grows FDOM vs_vars *)
Theorem step_inst_vars_monotone[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==>
    FDOM s.vs_vars SUBSET FDOM s'.vs_vars
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    rw[step_inst_def] >>
    gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
    imp_res_tac bind_outputs_vars_monotone >>
    Cases_on `ret.iret_adopt_fmp` >>
    gvs[SUBSET_DEF, merge_callee_state_def, adopt_return_fmp_def])
  >>
  rw[step_inst_non_invoke] >>
  imp_res_tac step_inst_base_vars_monotone
QED

(* exec_block OK: FDOM vs_vars only grows *)
Triviality exec_block_vars_grow[local]:
  !fuel ctx bb s v.
    exec_block fuel ctx bb s = OK v ==>
    FDOM s.vs_vars SUBSET FDOM v.vs_vars
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst fuel ctx x s` >> simp[] >>
  Cases_on `is_terminator x.inst_opcode` >> simp[]
  >- (
    IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
    imp_res_tac step_inst_vars_monotone >> gvs[SUBSET_DEF])
  >>
  strip_tac >>
  imp_res_tac step_inst_vars_monotone >>
  first_x_assum (qspecl_then
    [`LENGTH bb.bb_instructions - SUC s.vs_inst_idx`] mp_tac) >>
  impl_tac >- (gvs[get_instruction_def] >> DECIDE_TAC) >>
  disch_then (qspecl_then [`bb`,
    `v'' with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[SUBSET_TRANS]
QED

Theorem run_block_vars_grow[local]:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v ==>
    FDOM s.vs_vars SUBSET FDOM v.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = OK _`
    (ASSUME_TAC o (ONCE_REWRITE_RULE[run_block_def])) >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> gvs[Excl "eval_phis_def", Excl "eval_one_phi_def"] >>
  imp_res_tac eval_phis_vars_grow >>
  imp_res_tac exec_block_vars_grow >>
  gvs[pred_setTheory.SUBSET_DEF]
QED

(* run_block OK: outputs of all executed instructions end up in vs_vars.
   Generalized to arbitrary starting inst_idx for clean induction. *)
(* Helper: run_block OK, outputs of instruction at idx are in final state.
   Generalized to arbitrary starting idx. *)
(* Per-index: instruction outputs end up in final state *)
(* Terminator at idx means idx = last, by bb_well_formed *)
Theorem bb_wf_terminator_is_last[local]:
  !bb idx.
    bb_well_formed bb /\
    idx < LENGTH bb.bb_instructions /\
    is_terminator (EL idx bb.bb_instructions).inst_opcode ==>
    idx = PRE (LENGTH bb.bb_instructions)
Proof
  rw[bb_well_formed_def]
QED

(* exec_block OK: non-terminator instruction outputs end up in FDOM.
   The terminator case is excluded because e.g. JMP doesn't bind outputs. *)
Triviality exec_block_non_term_out_fdom[local]:
  !n fuel ctx bb s v idx.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    exec_block fuel ctx bb s = OK v /\
    bb_well_formed bb /\
    s.vs_inst_idx <= idx /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    (!j. j < LENGTH bb.bb_instructions ==>
         ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
         (EL j bb.bb_instructions).inst_outputs = []) ==>
    !out. MEM out (EL idx bb.bb_instructions).inst_outputs ==>
          out IN FDOM v.vs_vars
Proof
  completeInduct_on `n` >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst fuel ctx x s` >> simp[] >>
  Cases_on `is_terminator x.inst_opcode` >> simp[]
  >- (
    (* is_terminator *)
    IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
    `s.vs_inst_idx < LENGTH bb.bb_instructions`
      by gvs[get_instruction_def] >>
    `x = EL s.vs_inst_idx bb.bb_instructions`
      by gvs[get_instruction_def] >>
    `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
      by metis_tac[] >>
    `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)`
      by metis_tac[bb_wf_terminator_is_last] >>
    `idx = s.vs_inst_idx` by DECIDE_TAC >>
    metis_tac[])
  >>
  (* non-terminator, step_inst = OK v'' *)
  strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions`
    by gvs[get_instruction_def] >>
  `x = EL s.vs_inst_idx bb.bb_instructions`
    by gvs[get_instruction_def] >>
  Cases_on `idx = s.vs_inst_idx`
  >- (
    (* idx = current *)
    rpt strip_tac >> gvs[] >>
    `~opcode_has_output (EL s.vs_inst_idx bb.bb_instructions).inst_opcode ==>
     (EL s.vs_inst_idx bb.bb_instructions).inst_outputs = []` by (
      first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
    drule_all step_inst_outputs_in_fdom >> strip_tac >>
    imp_res_tac exec_block_vars_grow >>
    gvs[SUBSET_DEF])
  >>
  (* idx > current: apply IH *)
  rpt strip_tac >>
  qpat_x_assum `!m. m < _ ==> !fuel ctx bb s v idx. _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- DECIDE_TAC >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`,
    `v' with vs_inst_idx := SUC s.vs_inst_idx`, `v`, `idx`] mp_tac) >>
  simp[]
QED

(* Wrapper: run_block version *)
Theorem run_block_non_term_outputs_fdom[local]:
  !fuel ctx bb s v idx.
    run_block fuel ctx bb s = OK v /\
    bb_well_formed bb /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    (!j. j < LENGTH bb.bb_instructions ==>
         ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
         (EL j bb.bb_instructions).inst_outputs = []) ==>
    !out. MEM out (EL idx bb.bb_instructions).inst_outputs ==>
          out IN FDOM v.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = OK _`
    (ASSUME_TAC o (ONCE_REWRITE_RULE[run_block_def])) >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> gvs[Excl "eval_phis_def", Excl "eval_one_phi_def"] >>
  Cases_on `phi_prefix_length bb.bb_instructions ≤ idx`
  >- (imp_res_tac exec_block_non_term_out_fdom >>
      fs[pred_setTheory.SUBSET_DEF])
  >- (`idx < phi_prefix_length bb.bb_instructions` by DECIDE_TAC >>
      imp_res_tac eval_phis_outputs_in_fdom_idx >>
      imp_res_tac exec_block_vars_grow >>
      fs[pred_setTheory.SUBSET_DEF])
QED

(* step_inst_base preserves lookup_var for non-output variables *)
Theorem step_inst_base_lookup_preserved[local]:
  !inst s s' x.
    step_inst_base inst s = OK s' /\ ~MEM x inst.inst_outputs ==>
    lookup_var x s' = lookup_var x s
Proof
  rpt gen_tac >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >>
  PURE_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  gvs[exec_pure1_def] >>
  gvs[exec_pure2_def] >>
  gvs[exec_pure3_def] >>
  gvs[exec_read0_def, exec_read1_def] >>
  gvs[exec_write2_def, exec_alloca_def] >>
  gvs[exec_ext_call_def] >>
  gvs[exec_delegatecall_def] >>
  gvs[exec_create_def] >>
  gvs[extract_venom_result_def] >>
  gvs[AllCaseEqs(), LET_THM] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[jump_to_def, mcopy_def, mstore_def, istore_def, mstore8_def] >>
  gvs[sstore_def, tstore_def] >>
  gvs[halt_state_def, revert_state_def, set_returndata_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE] >>
  TRY (gvs[write_memory_with_expansion_def, LET_THM] >> NO_TAC) >>
  TRY (pairarg_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> NO_TAC) >>
  TRY (Cases_on `result` >> gvs[AllCaseEqs()]) >>
  TRY (Cases_on `y` >> gvs[AllCaseEqs()]) >>
  gvs[lookup_var_def]
QED

(* vars_colon_free preservation through step_inst_base *)
Theorem vars_colon_free_step_inst_base[local]:
  !inst s s'.
    vars_colon_free s /\
    EVERY colon_free inst.inst_outputs /\
    step_inst_base inst s = OK s' ==>
    vars_colon_free s'
Proof
  rpt strip_tac >>
  rw[vars_colon_free_def, lookup_var_def] >> rpt strip_tac >>
  imp_res_tac step_inst_base_vars_subset >>
  gvs[SUBSET_DEF, lookup_var_def] >>
  `x IN FDOM s.vs_vars \/ MEM x inst.inst_outputs` by
    (first_x_assum irule >> gvs[FLOOKUP_DEF]) >>
  gvs[vars_colon_free_def, lookup_var_def, FLOOKUP_DEF, EVERY_MEM]
QED

(* merge_callee_state preserves vars_colon_free (doesn't touch vs_vars) *)
Theorem vars_colon_free_merge_callee[local]:
  !caller callee.
    vars_colon_free caller ==>
    vars_colon_free (merge_callee_state caller callee)
Proof
  rw[vars_colon_free_def, merge_callee_state_def, lookup_var_def]
QED

(* FOLDL update_var preserves vars_colon_free when all names are colon_free *)
Theorem vars_colon_free_foldl_update[local]:
  !pairs s.
    vars_colon_free s /\
    EVERY (\(nm,vl). colon_free nm) pairs ==>
    vars_colon_free (FOLDL (\st (nm,vl). update_var nm vl st) s pairs)
Proof
  Induct >> rw[] >>
  PairCases_on `h` >> gvs[] >>
  first_x_assum irule >> simp[vars_colon_free_update]
QED

(* MEM colon in STRCAT: if neither part has colon, the whole doesn't *)
Theorem colon_free_strcat[local]:
  !s1 s2. colon_free (STRCAT s1 s2) <=> colon_free s1 /\ colon_free s2
Proof
  rw[colon_free_def, IMPLODE_EXPLODE_I, MEM_APPEND]
QED

(* ":" has a colon (used for contradiction) *)
Theorem not_colon_free_colon[local]:
  ~colon_free ":"
Proof
  EVAL_TAC
QED

(* version_var x n with n > 0 is NOT colon_free *)
Theorem version_var_has_colon:
  !x n. n > 0 ==> ~colon_free (version_var x n)
Proof
  rw[version_var_def] >>
  simp[colon_free_strcat, not_colon_free_colon]
QED

(* version_var is injective in base under colon_free *)
Theorem colon_free_strcat_prefix[local]:
  !x x' y y'.
    colon_free x /\ colon_free y /\
    STRCAT x x' = STRCAT y y' /\
    x' <> "" /\ y' <> "" /\
    HD (EXPLODE x') = #":" /\ HD (EXPLODE y') = #":" ==>
    x = y
Proof
  Induct >> rw[STRCAT_def] >-
  (Cases_on `y` >> gvs[STRCAT_def, colon_free_def, IMPLODE_EXPLODE_I]) >>
  Cases_on `y` >> gvs[STRCAT_def, colon_free_def, IMPLODE_EXPLODE_I] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem version_var_base_inj[local]:
  !x y n m.
    colon_free x /\ colon_free y /\
    version_var x n = version_var y m ==>
    x = y
Proof
  rw[version_var_def] >> gvs[] >>
  (* n = 0, m > 0: x = y ++ ":" ++ toString m, but x is colon_free *)
  gvs[colon_free_strcat, not_colon_free_colon] >>
  (* n > 0, m = 0: x ++ ":" ++ toString n = y, but y is colon_free *)
  gvs[colon_free_strcat, not_colon_free_colon] >>
  (* n > 0, m > 0: x ++ ":" ++ toString n = y ++ ":" ++ toString m *)
  irule colon_free_strcat_prefix >>
  rw[] >>
  qexistsl_tac [`STRCAT ":" (toString n)`, `STRCAT ":" (toString m)`] >>
  simp[STRCAT_EQ_EMPTY, IMPLODE_EXPLODE_I, STRCAT_ASSOC]
QED

(* version_var is fully injective under colon_free *)
Theorem version_var_inj:
  !x y n m.
    colon_free x /\ colon_free y /\
    version_var x n = version_var y m ==>
    x = y /\ n = m
Proof
  rw[version_var_def] >> gvs[] >>
  gvs[colon_free_strcat, not_colon_free_colon] >>
  `x = y` by (
    irule colon_free_strcat_prefix >> rw[] >>
    qexistsl_tac [`STRCAT ":" (toString n)`, `STRCAT ":" (toString m)`] >>
    simp[STRCAT_EQ_EMPTY, IMPLODE_EXPLODE_I, STRCAT_ASSOC]) >>
  gvs[]
QED

(* version_var a h = b with colon_free on both sides forces a = b *)
Triviality version_var_eq_colon_free[local]:
  !a h b. colon_free a /\ colon_free b /\ version_var a h = b ==> a = b
Proof
  rpt strip_tac >>
  Cases_on `h = 0`
  >- gvs[version_var_def]
  >> `h > 0` by DECIDE_TAC >>
  `~colon_free (version_var a h)` by metis_tac[version_var_has_colon] >>
  gvs[]
QED

(* latest_version is injective on colon_free domains.
   Used by ssa_sim_state_patch to construct patched states. *)
Theorem latest_version_INJ:
  !rs dom.
    (!x. x IN dom ==> colon_free x) ==>
    INJ (latest_version rs) dom UNIV
Proof
  Cases_on `rs` >> rw[pred_setTheory.INJ_DEF] >> rpt strip_tac >>
  spose_not_then ASSUME_TAC >>
  `colon_free x /\ colon_free y` by metis_tac[] >>
  fs[latest_version_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  metis_tac[version_var_inj, version_var_eq_colon_free]
QED

(* push_version returns a version number that is >= the current counter *)
Theorem push_version_ver[local]:
  !rs v rs' ver.
    push_version rs v = (rs', ver) ==>
    !v'. v' <> v ==>
      (case ALOOKUP (FST rs') v' of NONE => 0 | SOME n => n) =
      (case ALOOKUP (FST rs) v' of NONE => 0 | SOME n => n)
Proof
  Cases >> rw[push_version_def, LET_THM] >>
  gvs[ALOOKUP_FILTER]
QED

(* push_version increments the counter for v *)
Theorem push_version_counter:
  !rs v rs' ver.
    push_version rs v = (rs', ver) ==>
    (case ALOOKUP (FST rs') v of NONE => 0 | SOME n => n) = ver + 1
Proof
  Cases >> rw[push_version_def, LET_THM] >> simp[]
QED

(* Helper: get_counter extracts the current version counter for a variable *)
Definition get_counter_def:
  get_counter rs v = case ALOOKUP (FST rs) v of NONE => 0n | SOME n => n
End

(* All version numbers in rename_outputs output are >= the counter in the input state.
   Proved together with ALL_DISTINCT as a strengthened induction. *)
Theorem rename_outputs_versions_ge:
  !outs rs rs' outs'.
    EVERY colon_free outs /\
    rename_outputs rs outs = (rs', outs') ==>
    ALL_DISTINCT outs' /\
    (!x v n. MEM x outs' /\ colon_free v /\
             x = version_var v n ==> n >= get_counter rs v) /\
    (!v. get_counter rs' v >= get_counter rs v)
Proof
  Induct
  >- (rw[rename_outputs_def] >> gvs[])
  >> rpt gen_tac >> strip_tac >>
  gvs[rename_outputs_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  (* Establish counter facts about rs'' *)
  `get_counter rs'' h = ver + 1` by (
    gvs[get_counter_def] >>
    metis_tac[push_version_counter]) >>
  `!v'. v' <> h ==> get_counter rs'' v' = get_counter rs v'` by (
    rpt strip_tac >> gvs[get_counter_def] >>
    metis_tac[push_version_ver]) >>
  `ver = get_counter rs h` by (
    gvs[get_counter_def] >>
    Cases_on `rs` >> gvs[push_version_def, LET_THM]) >>
  rpt conj_tac
  (* Goal 1: ¬MEM (version_var h ver) rest *)
  >- (CCONTR_TAC >> gvs[] >> res_tac >> gvs[])
  (* Goal 2: ALL_DISTINCT rest *)
  >- gvs[]
  (* Goal 3: MEM version bounds *)
  >- (rpt gen_tac >> strip_tac >> gvs[]
      >- (`v = h /\ n = get_counter rs h` by metis_tac[version_var_inj] >>
          ASM_REWRITE_TAC[] >> simp[])
      >> `n >= get_counter rs'' v` by res_tac >>
         `get_counter rs'' v >= get_counter rs v` by (
           Cases_on `v = h` >> gvs[]) >>
         simp[GREATER_EQ])
  (* Goal 4: Counter monotonicity *)
  >> rpt strip_tac >>
  `get_counter rs' v >= get_counter rs'' v` by gvs[] >>
  `get_counter rs'' v >= get_counter rs v` by (
    Cases_on `v = h` >> gvs[]) >>
  simp[GREATER_EQ]
QED

(* push_version never decreases any counter *)
Theorem push_version_mono[local]:
  !rs v rs' ver w.
    push_version rs v = (rs', ver) ==>
    get_counter rs' w >= get_counter rs w
Proof
  rpt strip_tac >> Cases_on `w = v`
  >- (imp_res_tac push_version_counter >>
      Cases_on `rs` >> gvs[push_version_def, LET_THM, get_counter_def])
  >> imp_res_tac push_version_ver >>
     gvs[get_counter_def]
QED

(* Counter monotonicity for rename_outputs — no colon_free needed *)
Theorem rename_outputs_counter_mono:
  !outs rs rs' outs'.
    rename_outputs rs outs = (rs', outs') ==>
    !v. get_counter rs' v >= get_counter rs v
Proof
  Induct >- (rw[rename_outputs_def] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[rename_outputs_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  imp_res_tac push_version_mono >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[]
QED

(* Convenient corollary *)
Theorem rename_outputs_all_distinct:
  !outs rs.
    EVERY colon_free outs ==>
    ALL_DISTINCT (SND (rename_outputs rs outs))
Proof
  rpt strip_tac >>
  Cases_on `rename_outputs rs outs` >>
  metis_tac[rename_outputs_versions_ge, pairTheory.SND]
QED

(* Each output of rename_outputs is version_var of the corresponding input *)
Theorem rename_outputs_el[local]:
  !outs rs rs' outs'.
    rename_outputs rs outs = (rs', outs') ==>
    LENGTH outs' = LENGTH outs /\
    !i. i < LENGTH outs ==> ?ver. EL i outs' = version_var (EL i outs) ver
Proof
  Induct >- rw[rename_outputs_def] >>
  rw[rename_outputs_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `i` >> gvs[] >> metis_tac[]
QED

(* Output properties of rename_inst for non-PHI instructions *)
Theorem rename_inst_output_props[local]:
  !rs inst.
    inst.inst_opcode <> PHI /\ EVERY colon_free inst.inst_outputs ==>
    ALL_DISTINCT (SND (rename_inst rs inst)).inst_outputs /\
    LENGTH (SND (rename_inst rs inst)).inst_outputs = LENGTH inst.inst_outputs /\
    !i. i < LENGTH inst.inst_outputs ==>
      ?ver. EL i (SND (rename_inst rs inst)).inst_outputs =
            version_var (EL i inst.inst_outputs) ver
Proof
  rw[rename_inst_def, LET_THM] >> pairarg_tac >> gvs[] >>
  Cases_on `rename_outputs rs inst.inst_outputs` >> gvs[] >>
  imp_res_tac rename_outputs_el >> gvs[] >>
  metis_tac[rename_outputs_all_distinct, rename_outputs_versions_ge,
            pairTheory.SND]
QED

(* latest_version always returns version_var x n for some n *)
Theorem latest_version_is_version_var:
  !rs x. ?n. latest_version rs x = version_var x n
Proof
  Cases >> rw[latest_version_def] >>
  Cases_on `ALOOKUP r x` >> rw[] >- (qexists_tac `0` >> rw[version_var_def]) >>
  Cases_on `x'` >> rw[] >- (qexists_tac `0` >> rw[version_var_def]) >>
  qexists_tac `h` >> rw[]
QED

(* The key non-aliasing lemma for ssa_sim_update_var:
   If sigma = latest_version rs and all original vars are colon_free,
   then sigma(x) <> version_var y ver for x <> y *)
Theorem latest_version_no_alias[local]:
  !rs x y ver.
    colon_free x /\ colon_free y /\ x <> y ==>
    latest_version rs x <> version_var y ver
Proof
  rpt strip_tac >>
  `?n. latest_version rs x = version_var x n`
    by metis_tac[latest_version_is_version_var] >>
  `x = y` by metis_tac[version_var_base_inj] >>
  gvs[]
QED

(* Abstract sigma no-alias: if sigma maps colon_free vars to their own versions,
   then sigma x cannot collide with version_var y ver for x <> y. *)
Theorem sigma_no_alias[local]:
  !sigma x y ver.
    colon_free x /\ colon_free y /\ x <> y /\
    (!v. colon_free v ==> ?n. sigma v = version_var v n) ==>
    sigma x <> version_var y ver
Proof
  rpt strip_tac >>
  `?n. sigma x = version_var x n` by metis_tac[] >>
  gvs[] >> metis_tac[version_var_base_inj]
QED

(* ==========================================================================
   Part 4: Per-block simulation

   Strategy:
   Phase 1 (PHI prefix): Execute PHI instructions on SSA side only,
     updating sigma. Uses exec_block_step_non_term to peel each PHI.
   Phase 2 (lockstep): Execute corresponding instructions on both sides.
     Uses step_inst_base_renamed_sim for per-step simulation.
   
   After removing cleanup phases (remove_degenerate_phis, ensure_well_formed)
   from make_ssa_fn, the SSA block has a clean structure:
     [renamed_PHI_1, ..., renamed_PHI_k, renamed_orig_1, ..., renamed_orig_n]
   ========================================================================== *)

(* rename_block_insts distributes over append *)
Theorem rename_block_insts_append:
  !xs ys rs.
    rename_block_insts rs (xs ++ ys) =
    let (rs', xs') = rename_block_insts rs xs in
    let (rs'', ys') = rename_block_insts rs' ys in
    (rs'', xs' ++ ys')
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  first_x_assum (qspecl_then [`ys`, `rs'`] mp_tac) >>
  Cases_on `rename_block_insts rs' xs` >>
  Cases_on `rename_block_insts q ys` >>
  Cases_on `rename_block_insts rs' (xs ++ ys)` >>
  gvs[]
QED

Theorem rename_block_insts_fst_append:
  !xs ys rs.
    FST (rename_block_insts rs (xs ++ ys)) =
    FST (rename_block_insts (FST (rename_block_insts rs xs)) ys)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`xs`, `ys`, `rs`]
    (SIMP_RULE std_ss [LET_THM] rename_block_insts_append)) >>
  Cases_on `rename_block_insts rs xs` >>
  Cases_on `rename_block_insts q ys` >>
  simp[]
QED

(* rename_block_insts stepping: TAKE (SUC j) decomposes into
   TAKE j processed followed by rename_inst on EL j *)
Theorem rename_block_insts_step[local]:
  !j insts rs. j < LENGTH insts ==>
    FST (rename_block_insts rs (TAKE (SUC j) insts)) =
    FST (rename_inst (FST (rename_block_insts rs (TAKE j insts))) (EL j insts))
Proof
  rpt strip_tac >>
  `TAKE (SUC j) insts = TAKE j insts ++ [EL j insts]` by
    simp[GSYM SNOC_APPEND, SNOC_EL_TAKE] >>
  gvs[] >>
  mp_tac (Q.SPECL [`TAKE j insts`, `[EL j insts]`, `rs`]
           (SIMP_RULE std_ss [LET_THM] rename_block_insts_append)) >>
  rw[LET_THM] >>
  Cases_on `rename_block_insts rs (TAKE j insts)` >> gvs[] >>
  Cases_on `rename_inst q (EL j insts)` >> gvs[] >>
  gvs[rename_block_insts_def, LET_THM]
QED

(* rename_block_insts element-wise: the j-th output instruction is
   SND(rename_inst (FST(rename_block_insts rs (TAKE j insts))) (EL j insts)) *)
Theorem rename_block_insts_el:
  !insts rs j.
    j < LENGTH insts ==>
    EL j (SND (rename_block_insts rs insts)) =
    SND (rename_inst (FST (rename_block_insts rs (TAKE j insts)))
                     (EL j insts))
Proof
  Induct
  >- simp[]
  >> rpt gen_tac >> strip_tac >>
  simp[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `j`
  >- gvs[rename_block_insts_def]
  >> gvs[] >>
  first_x_assum (qspecl_then [`rs'`, `n`] mp_tac) >> simp[] >>
  simp[rename_block_insts_def, LET_THM] >>
  Cases_on `rename_block_insts rs' (TAKE n insts)` >> simp[]
QED

(* ---------- Helper: Peel n non-terminator non-INVOKE instructions --------
   Starting from vs_inst_idx = m, executes instructions m through m+n-1
   on the SSA side, peeling each from run_block. Each step must succeed
   and the resulting state must maintain some property P (threaded through
   via step_ok). Returns the state after n steps with vs_inst_idx = m+n. *)
Theorem peel_prefix[local]:
  !n m bb fuel ctx s.
    m + n <= LENGTH bb.bb_instructions /\
    s.vs_inst_idx = m /\
    (!j sj. m <= j /\ j < m + n /\ sj.vs_inst_idx = j ==>
       ~is_terminator (EL j bb.bb_instructions).inst_opcode /\
       (EL j bb.bb_instructions).inst_opcode <> INVOKE /\
       ?sj'. step_inst_base (EL j bb.bb_instructions) sj = OK sj') ==>
    ?s'.
      exec_block fuel ctx bb s =
        exec_block fuel ctx bb (s' with vs_inst_idx := m + n)
Proof
  Induct_on `n` >- (
    rw[] >> qexists_tac `s` >>
    `s with vs_inst_idx := s.vs_inst_idx = s` by
      (Cases_on `s` >> simp[venom_state_component_equality]) >>
    simp[]
  ) >>
  rpt strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by DECIDE_TAC >>
  first_assum (qspecl_then [`m`, `s`] mp_tac) >>
  impl_tac >- DECIDE_TAC >> strip_tac >>
  (* Peel instruction at index m using exec_block_step_non_term *)
  mp_tac (Q.SPECL [`bb`, `fuel`, `ctx`, `s`,
    `EL s.vs_inst_idx bb.bb_instructions`, `sj'`]
    exec_block_step_non_term) >>
  impl_tac >- gvs[] >> strip_tac >>
  (* Apply IH at SUC m with n steps *)
  first_x_assum (qspecl_then [`SUC m`, `bb`, `fuel`, `ctx`,
    `sj' with vs_inst_idx := SUC m`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >- DECIDE_TAC >- simp[] >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`j`, `sj`] mp_tac) >>
    impl_tac >- DECIDE_TAC >> simp[]
  ) >>
  strip_tac >>
  qexists_tac `s'` >>
  `SUC s.vs_inst_idx = SUC m` by gvs[] >>
  `SUC m + n = m + SUC n` by DECIDE_TAC >>
  gvs[]
QED

(* Per-block simulation: the core obligation.
   
   sigma must be latest_version of some rename state rs — this ensures
   PHI operands (filled by update_succ_phis with the predecessor's rs)
   resolve to Var (sigma x) for the correct original variable x.
   
   The conclusion strengthens ssa_result_equiv: in the OK case, the output
   sigma' is also a latest_version (so the invariant chains across blocks). *)
(* ---------- Block simulation ---------- *)

(* pipeline_block_structure is now in ssaPipelineTheory *)

(* rename_inst for non-PHI instructions produces inst_renamed.
   Now that freshness is separated into output_fresh, inst_renamed
   only requires opcode+id+operands+output_length. *)
Theorem rename_inst_produces_inst_renamed[local]:
  !rs inst.
    inst.inst_opcode <> PHI ==>
    inst_renamed (latest_version rs) inst (SND (rename_inst rs inst))
Proof
  rw[inst_renamed_def, rename_inst_def, LET_THM] >>
  Cases_on `rename_outputs rs inst.inst_outputs` >> gvs[] >>
  rpt conj_tac
  >- (simp[rename_operands_eq_map])
  >> (`LENGTH r = LENGTH (SND (rename_outputs rs inst.inst_outputs))`
        by gvs[] >> gvs[rename_outputs_length])
QED

(* PHI simulation precondition (Option E): carries the POST-PHI state.
   Given states already related by ssa_sim at block entry, stepping all PHIs
   in bb' produces an intermediate state s2_mid where ssa_sim still holds
   (with possibly different sigma) and run_block factors through s2_mid.

   This pushes PHI value correspondence to the caller, avoiding the need to
   analyze update_succ_phis / resolve_phi at this level. *)
(* PHI simulation precondition.
   Given states related by ssa_sim at block entry, stepping all PHIs
   in bb' produces an intermediate state s2_mid where ssa_sim still holds.
   The runtime part requires:
   (1) original doesn't error
   (2) PHI base variables are defined in s1 (no use-before-def) *)
Definition phi_args_ok_def:
  phi_args_ok bb bb' sigma sigma_out s1 s2 rs_mid <=>
    ?n_phi.
      (* Structural: n_phi PHIs at start, then non-PHI body *)
      n_phi <= LENGTH bb'.bb_instructions /\
      (!j. j < n_phi ==>
        (EL j bb'.bb_instructions).inst_opcode = PHI) /\
      (!j. n_phi <= j /\ j < LENGTH bb'.bb_instructions ==>
        (EL j bb'.bb_instructions).inst_opcode <> PHI) /\
      LENGTH bb'.bb_instructions = n_phi + LENGTH bb.bb_instructions /\
      (* Body instructions are renamed versions of original instructions *)
      (!j. j < LENGTH bb.bb_instructions ==>
        EL (n_phi + j) bb'.bb_instructions =
          SND (rename_inst
            (FST (rename_block_insts rs_mid (TAKE j bb.bb_instructions)))
            (EL j bb.bb_instructions))) /\
      (* No PHIs in original block body *)
      (!j. j < LENGTH bb.bb_instructions ==>
        (EL j bb.bb_instructions).inst_opcode <> PHI) /\
      vars_colon_free s1 /\
      (!x. colon_free x ==> ?n. sigma_out x = version_var x n) /\
      (* Runtime: eval_phis on bb' produces the post-PHI state used by run_block. *)
      (!fuel ctx.
        (!e. run_block fuel ctx bb s1 <> Error e) ==>
        ?s2_mid.
          s2_mid.vs_inst_idx = n_phi /\
          ssa_sim sigma_out s1 s2_mid /\
          s2_mid.vs_halted = s2.vs_halted /\
          s2_mid.vs_current_bb = s2.vs_current_bb /\
          s2_mid.vs_prev_bb = s2.vs_prev_bb /\
          run_block fuel ctx bb' s2 =
          exec_block fuel ctx bb' s2_mid)
End

(* ssa_sim congruence: pointwise equal sigmas give same ssa_sim *)
Theorem ssa_sim_sigma_cong[local]:
  !f g s1 s2.
    ssa_sim f s1 s2 /\ (!x. g x = f x) ==> ssa_sim g s1 s2
Proof
  rw[ssa_sim_def] >> metis_tac[]
QED

(* ssa_sim preservation through update_var with fresh output *)
Theorem ssa_sim_update_fresh[local]:
  !sigma s1 s2 base out w.
    ssa_sim sigma s1 s2 /\
    lookup_var base s1 = SOME w /\
    (!x. x <> base ==> sigma x <> out) ==>
    ssa_sim ((base =+ out) sigma) s1 (update_var out w s2)
Proof
  rw[ssa_sim_def, update_var_def, lookup_var_def, combinTheory.UPDATE_def,
     FLOOKUP_UPDATE] >>
  metis_tac[optionTheory.SOME_11]
QED

(* Weaker version: freshness only for variables in s1's domain *)
Theorem ssa_sim_update_fresh_dom[local]:
  !sigma s1 s2 bvar out w.
    ssa_sim sigma s1 s2 /\
    lookup_var bvar s1 = SOME w /\
    (!x. x <> bvar /\ (?v. lookup_var x s1 = SOME v) ==> sigma x <> out) ==>
    ssa_sim ((bvar =+ out) sigma) s1 (update_var out w s2)
Proof
  rw[ssa_sim_def, update_var_def, lookup_var_def, combinTheory.UPDATE_def,
     FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  Cases_on `x = bvar` >> gvs[] >>
  `sigma x <> out` by metis_tac[] >>
  gvs[] >> metis_tac[]
QED

(* Single PHI step: execute one PHI instruction, updating ssa_sim.
   The PHI reads via resolve_phi, evaluates in s2, writes to fresh output.
   After: ssa_sim sigma' s1 s2' where sigma'(bv) = out, rest unchanged. *)
Theorem phi_step_sim[local]:
  !bb' fuel ctx s1 s2 sigma bv out w prev_bb.
    s2.vs_inst_idx < LENGTH bb'.bb_instructions /\
    s2.vs_prev_bb = SOME prev_bb /\
    ssa_sim sigma s1 s2 /\
    (EL s2.vs_inst_idx bb'.bb_instructions).inst_opcode = PHI /\
    (EL s2.vs_inst_idx bb'.bb_instructions).inst_outputs = [out] /\
    resolve_phi prev_bb
      (EL s2.vs_inst_idx bb'.bb_instructions).inst_operands =
      SOME (Var (sigma bv)) /\
    lookup_var bv s1 = SOME w /\
    lookup_var (sigma bv) s2 = SOME w /\
    (!x. x <> bv ==> sigma x <> out) ==>
    let s2' = update_var out w s2 in
    ssa_sim ((bv =+ out) sigma) s1 s2' /\
    (s2'.vs_halted <=> s2.vs_halted) /\
    s2'.vs_current_bb = s2.vs_current_bb /\
    s2'.vs_prev_bb = s2.vs_prev_bb /\
    exec_block fuel ctx bb' s2 = Error "phi outside prefix"
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  conj_tac >- (
    irule ssa_sim_update_fresh >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (conj_tac >- (simp[update_var_def])) >>
  (conj_tac >- (simp[update_var_def])) >>
  (conj_tac >- (simp[update_var_def])) >>
  qpat_x_assum `(EL s2.vs_inst_idx bb'.bb_instructions).inst_opcode = PHI`
    mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  gvs[get_instruction_def, step_inst_def, step_inst_base_def]
QED


(* PHI prefix execution: stepping through n_phi PHI instructions
   starting at index idx0 in bb' produces s2_mid with specific
   lookup_var properties. This is a pure execution lemma — it does
   NOT mention ssa_sim or sigma. The caller builds ssa_sim from
   the lookup_var facts.

   Each PHI j reads operand var v_j from s2, gets value w_j,
   writes it to output out_j. The no-shadow condition ensures
   v_j is not clobbered by earlier writes (v_j ∉ {out_0..out_{j-1}}).
   Distinct outputs ensures no write clobbers a later write target. *)
(* OBSOLETE after parallel-PHI semantics: PHIs are no longer executable via
   exec_block/step_inst_base. Original sequential-PHI proof preserved below.
Theorem phi_prefix_exec_old[local]:
  !n_phi bb' s2 prev_bb idx0 outs vals vars.
    idx0 + n_phi <= LENGTH bb'.bb_instructions /\
    s2.vs_inst_idx = idx0 /\
    s2.vs_prev_bb = SOME prev_bb /\
    LENGTH outs = n_phi /\ LENGTH vals = n_phi /\ LENGTH vars = n_phi /\
    (* Per-PHI instruction properties *)
    (!j. j < n_phi ==>
      (EL (idx0 + j) bb'.bb_instructions).inst_opcode = PHI /\
      (EL (idx0 + j) bb'.bb_instructions).inst_outputs = [EL j outs] /\
      resolve_phi prev_bb
        (EL (idx0 + j) bb'.bb_instructions).inst_operands =
        SOME (Var (EL j vars)) /\
      lookup_var (EL j vars) s2 = SOME (EL j vals)) /\
    (* No shadow: each PHI's operand var is not an earlier output *)
    (!j k. j < n_phi /\ k < j ==> EL j vars <> EL k outs) /\
    (* Distinct outputs *)
    ALL_DISTINCT outs ==>
    !fuel ctx.
      ?s2_mid.
        s2_mid.vs_inst_idx = idx0 + n_phi /\
        (s2_mid.vs_halted <=> s2.vs_halted) /\
        s2_mid.vs_current_bb = s2.vs_current_bb /\
        s2_mid.vs_prev_bb = s2.vs_prev_bb /\
        exec_block fuel ctx bb' s2 = exec_block fuel ctx bb' s2_mid /\
        (* PHI outputs written *)
        (!j. j < n_phi ==>
          lookup_var (EL j outs) s2_mid = SOME (EL j vals)) /\
        (* Non-output vars preserved *)
        (!x. ~MEM x outs ==>
          lookup_var x s2_mid = lookup_var x s2)
Proof
  Induct_on `n_phi` >>
  rpt gen_tac >> strip_tac
  (* Base case: n_phi = 0 *)
  >- (
    rpt gen_tac >>
    qexists_tac `s2` >> gvs[] >>
    Cases_on `outs` >> gvs[]) >>
  (* Step case: n_phi = SUC n_phi' *)
  (* Decompose lists into head::tail *)
  Cases_on `outs` >> gvs[] >>
  Cases_on `vals` >> gvs[] >>
  Cases_on `vars` >> gvs[] >>
  rename1 `lookup_var (h_var::t_var)❲_❳ s2 = SOME (h_val::t_val)❲_❳` >>
  (* Extract j=0 facts — match the per-PHI assumption specifically *)
  qpat_x_assum `!j. j < SUC _ ==> _.inst_opcode = _ /\ _`
    (fn th => assume_tac th >>
     mp_tac (SIMP_RULE (srw_ss()) [] (Q.SPEC `0` th))) >>
  strip_tac >>
  (* step_inst_base for PHI0 *)
  qabbrev_tac `phi0 = EL s2.vs_inst_idx bb'.bb_instructions` >>
  `step_inst_base phi0 s2 = OK (update_var h h_val s2)` by (
    simp[Abbr `phi0`, step_inst_base_def, eval_operand_def] >>
    Cases_on `FLOOKUP s2.vs_vars h_var` >> gvs[lookup_var_def]) >>
  (* Peel one step *)
  `s2.vs_inst_idx < LENGTH bb'.bb_instructions` by DECIDE_TAC >>
  mp_tac exec_block_step_non_term >>
  disch_then (qspecl_then [`bb'`, `fuel`, `ctx`, `s2`, `phi0`,
    `update_var h h_val s2`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    simp[Abbr `phi0`, is_terminator_def]) >>
  strip_tac >>
  qabbrev_tac `s2_1 = update_var h h_val s2 with
    vs_inst_idx := SUC s2.vs_inst_idx` >>
  (* Apply IH — establish shifted per-PHI and no-shadow as Trivialities *)
  first_x_assum (qspecl_then [`bb'`, `s2_1`, `prev_bb`,
    `t`, `t_val`, `t_var`] mp_tac) >>
  `s2_1.vs_inst_idx = SUC s2.vs_inst_idx` by simp[Abbr `s2_1`] >>
  `s2_1.vs_prev_bb = SOME prev_bb` by simp[Abbr `s2_1`, update_var_def] >>
  impl_tac >- (suspend "ih_pre") >>
  suspend "compose"
QED

Resume phi_prefix_exec[ih_pre]:
  simp[Abbr `s2_1`] >>
  conj_tac
  (* Per-PHI for tail *)
  >- (
    rpt gen_tac >> strip_tac >>
    `bb'.bb_instructions❲SUC (j + s2.vs_inst_idx)❳.inst_opcode = PHI /\
     bb'.bb_instructions❲SUC (j + s2.vs_inst_idx)❳.inst_outputs = [t❲j❳] /\
     resolve_phi prev_bb
       bb'.bb_instructions❲SUC (j + s2.vs_inst_idx)❳.inst_operands =
       SOME (Var t_var❲j❳) /\
     lookup_var t_var❲j❳ s2 = SOME t_val❲j❳`
      by (first_x_assum (mp_tac o Q.SPEC `SUC j`) >>
          simp[ADD_CLAUSES, rich_listTheory.EL_CONS]) >>
    `t_var❲j❳ <> h`
      by (first_x_assum (mp_tac o Q.SPECL [`SUC j`, `0`]) >>
          simp[rich_listTheory.EL_CONS]) >>
    gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE, ADD_CLAUSES])
  (* No-shadow for tail *)
  >> (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`SUC j`, `SUC k`] mp_tac) >>
    simp[rich_listTheory.EL_CONS])
QED

Resume phi_prefix_exec[compose]:
  strip_tac >>
  rpt gen_tac >>
  pop_assum (strip_assume_tac o Q.SPECL [`fuel'`, `ctx'`]) >>
  qexists_tac `s2_mid` >>
  simp[] >>
  (* Re-derive peel equation for fuel'/ctx' *)
  `exec_block fuel' ctx' bb' s2 = exec_block fuel' ctx' bb' s2_1` by (
    mp_tac exec_block_step_non_term >>
    disch_then (qspecl_then [`bb'`, `fuel'`, `ctx'`, `s2`, `phi0`,
      `update_var h h_val s2`] mp_tac) >>
    impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[Abbr `phi0`, is_terminator_def]) >>
    simp[Abbr `s2_1`]) >>
  rpt conj_tac
  >- (gvs[Abbr `s2_1`, update_var_def])
  >- (gvs[Abbr `s2_1`, update_var_def])
  >- (gvs[])
  >- (
    rpt strip_tac >>
    Cases_on `j` >> gvs[]
    >- (
      `~MEM h t` by (gvs[]) >>
      `lookup_var h s2_mid = lookup_var h s2_1` by (
        first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
      gvs[Abbr `s2_1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]))
  >> (
    gvs[Abbr `s2_1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE])
QED

Finalise phi_prefix_exec_old;
*)

(* Key bridge: push_version evolves latest_version as a pointwise update *)
Theorem latest_version_push[local]:
  !rs v.
    let (rs', ver) = push_version rs v in
    !x. latest_version rs' x =
        if x = v then version_var v ver else latest_version rs x
Proof
  Cases >> rw[push_version_def, latest_version_def, LET_THM] >>
  Cases_on `x = v` >> gvs[]
  >- (Cases_on `ALOOKUP r v` >> simp[ALOOKUP_def]) >>
  Cases_on `ALOOKUP r v` >> simp[ALOOKUP_def, ALOOKUP_FILTER]
QED

(* rename_outputs with single output: latest_version evolves by one update *)
Theorem rename_outputs_single_latest[local]:
  !rs v.
    let (rs', outs') = rename_outputs rs [v] in
    outs' = [version_var v (SND (push_version rs v))] /\
    !x. latest_version rs' x =
        if x = v then HD outs' else latest_version rs x
Proof
  rw[rename_outputs_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.SPECL [`rs`, `v`] latest_version_push) >>
  rw[LET_THM] >>
  pairarg_tac >> gvs[]
QED

(* PHI prefix simulation: execute the PHI prefix and build ssa_sim.
   Generalized for arbitrary starting idx (needed for IH in step case).
   Threads ssa_sim through induction via sigma updates at each step.

   Key hypotheses:
   - ALL_DISTINCT phi bases (for freshness at each step)
   - coverage (non-PHI vars agree with sigma → latest_version rs_b_entry)
   - per-PHI resolve_phi result (for read values)
   - vars_colon_free (for freshness via latest_version_no_alias) *)
Triviality all_distinct_head_tail_disjoint[local]:
  !h t j a b.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (h::t))) /\
    h.inst_outputs = [a] /\ j < LENGTH t /\
    (EL j t).inst_outputs = [b] ==> a <> b
Proof
  rpt strip_tac >> spose_not_then strip_assume_tac >> gvs[] >>
  fs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  first_x_assum (qspec_then `[a]` mp_tac) >> simp[] >>
  qexists_tac `EL j t` >> simp[MEM_EL] >> metis_tac[]
QED
(* rename_outputs doesn't change latest_version for non-output variables *)
Triviality rename_outputs_non_output_stable[local]:
  !outs rs x. ~MEM x outs ==>
    latest_version (FST (rename_outputs rs outs)) x = latest_version rs x
Proof
  Induct >> rw[rename_outputs_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.SPECL [`rs`, `h`] latest_version_push) >>
  rw[LET_THM] >>
  first_x_assum (qspecl_then [`rs'`, `x`] mp_tac) >> gvs[]
QED

(* FST of rename_inst depends only on rename_outputs (opcode-independent) *)
Triviality rename_inst_fst_early[local]:
  !rs inst. FST (rename_inst rs inst) = FST (rename_outputs rs inst.inst_outputs)
Proof
  rw[rename_inst_def] >> Cases_on `inst.inst_opcode = PHI` >> simp[LET_THM] >>
  pairarg_tac >> simp[]
QED

Triviality rename_inst_single_output_latest[local]:
  !rs inst bvar rs' inst'.
    inst.inst_outputs = [bvar] /\
    rename_inst rs inst = (rs', inst') ==>
    inst'.inst_outputs = [version_var bvar (SND (push_version rs bvar))] /\
    (!x. latest_version rs' x =
      if x = bvar then version_var bvar (SND (push_version rs bvar))
      else latest_version rs x)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`rs`, `bvar`] rename_outputs_single_latest) >>
  Cases_on `rename_outputs rs [bvar]` >>
  Cases_on `inst.inst_opcode = PHI` >>
  gvs[rename_inst_def, LET_THM]
QED

(* rename_block_insts doesn't change latest_version for non-output variables.
   Works for ALL instructions including PHI (unlike latest_version_stable). *)
Theorem rename_block_insts_non_output_stable_any:
  !insts rs x.
    (!i. MEM i insts ==> ~MEM x i.inst_outputs) ==>
    latest_version (FST (rename_block_insts rs insts)) x = latest_version rs x
Proof
  Induct >> rw[rename_block_insts_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `latest_version (FST (rename_inst rs h)) x = latest_version rs x` by (
    simp[rename_inst_fst_early] >>
    irule rename_outputs_non_output_stable >> metis_tac[]) >>
  first_x_assum (qspecl_then [`rs'`, `x`] mp_tac) >>
  impl_tac >- metis_tac[] >> gvs[]
QED

Triviality rename_block_cons_single_output_latest[local]:
  !rs inst rest bvar.
    inst.inst_outputs = [bvar] ==>
    ?rs' inst'.
      rename_inst rs inst = (rs', inst') /\
      inst'.inst_outputs = [version_var bvar (SND (push_version rs bvar))] /\
      (!x. latest_version rs' x =
        if x = bvar then version_var bvar (SND (push_version rs bvar))
        else latest_version rs x) /\
      SND (rename_block_insts rs (inst::rest)) =
        inst' :: SND (rename_block_insts rs' rest) /\
      FST (rename_block_insts rs (inst::rest)) =
        FST (rename_block_insts rs' rest)
Proof
  rpt strip_tac >>
  Cases_on `rename_inst rs inst` >>
  rename1 `rename_inst rs inst = (rs1, inst1)` >>
  qexists_tac `rs1` >> qexists_tac `inst1` >>
  `inst1.inst_outputs = [version_var bvar (SND (push_version rs bvar))] /\
   (!x. latest_version rs1 x =
      if x = bvar then version_var bvar (SND (push_version rs bvar))
      else latest_version rs x)` by (
    mp_tac (Q.SPECL [`rs`, `inst`, `bvar`, `rs1`, `inst1`]
      rename_inst_single_output_latest) >> simp[]) >>
  rpt conj_tac >> simp[] >>
  simp[rename_block_insts_def] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Triviality rename_block_cons_head_output_latest[local]:
  !rs inst rest bvar head_inst out.
    inst.inst_outputs = [bvar] /\
    head_inst.inst_outputs =
      (EL 0 (SND (rename_block_insts rs (inst::rest)))).inst_outputs /\
    out = version_var bvar (SND (push_version rs bvar)) ==>
    ?rs' inst'.
      rename_inst rs inst = (rs', inst') /\
      inst'.inst_outputs = [out] /\
      head_inst.inst_outputs = [out] /\
      (!x. latest_version rs' x =
        if x = bvar then out else latest_version rs x) /\
      SND (rename_block_insts rs (inst::rest)) =
        inst' :: SND (rename_block_insts rs' rest) /\
      FST (rename_block_insts rs (inst::rest)) =
        FST (rename_block_insts rs' rest)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`rs`, `inst`, `rest`, `bvar`]
    rename_block_cons_single_output_latest) >>
  impl_tac >- simp[] >>
  strip_tac >>
  rename1 `rename_inst rs inst = (rs1, inst1)` >>
  qexists_tac `rs1` >> qexists_tac `inst1` >>
  gvs[rich_listTheory.EL_CONS]
QED

Triviality rename_block_insts_cons_snd[local]:
  !rs inst rest rs1 inst1.
    rename_inst rs inst = (rs1, inst1) ==>
    SND (rename_block_insts rs (inst::rest)) =
      inst1 :: SND (rename_block_insts rs1 rest)
Proof
  rw[rename_block_insts_def, LET_THM] >>
  Cases_on `rename_block_insts rs1 rest` >> gvs[]
QED

Triviality rename_block_insts_cons_fst[local]:
  !rs inst rest rs1 inst1.
    rename_inst rs inst = (rs1, inst1) ==>
    FST (rename_block_insts rs (inst::rest)) =
      FST (rename_block_insts rs1 rest)
Proof
  rw[rename_block_insts_def, LET_THM] >>
  Cases_on `rename_block_insts rs1 rest` >> gvs[]
QED

Triviality phi_prefix_sim_tail_bundled[local]:
  !phi0 phis_rest inst0 insts_rest rs_b_entry rs_1 inst_0 sigma prev_lbl s1.
    rename_inst rs_b_entry phi0 = (rs_1, inst_0) /\
    (!j. j < LENGTH (phi0::phis_rest) ==>
      (EL j (phi0::phis_rest)).inst_opcode = PHI /\
      (?bv. (EL j (phi0::phis_rest)).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j (phi0::phis_rest)).inst_outputs)) s1 = SOME w) /\
      (EL j (inst0::insts_rest)).inst_opcode = PHI /\
      (EL j (inst0::insts_rest)).inst_outputs =
        (EL j (SND (rename_block_insts rs_b_entry (phi0::phis_rest)))).inst_outputs /\
      resolve_phi prev_lbl (EL j (inst0::insts_rest)).inst_operands =
        SOME (Var (sigma (HD ((EL j (phi0::phis_rest)).inst_outputs))))) ==>
    !j. j < LENGTH phis_rest ==>
      (EL j phis_rest).inst_opcode = PHI /\
      (?bv. (EL j phis_rest).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j phis_rest).inst_outputs)) s1 = SOME w) /\
      (EL j insts_rest).inst_opcode = PHI /\
      (EL j insts_rest).inst_outputs =
        (EL j (SND (rename_block_insts rs_1 phis_rest))).inst_outputs /\
      resolve_phi prev_lbl (EL j insts_rest).inst_operands =
        SOME (Var (sigma (HD ((EL j phis_rest).inst_outputs))))
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `SUC j` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `rename_block_insts rs_1 phis_rest` >>
  gvs[rich_listTheory.EL_CONS, rename_block_insts_def, LET_THM]
QED

Triviality phi_prefix_sim_tail_bundled_by_snd[local]:
  !phi0 phis_rest inst0 insts_rest rs_b_entry rs_1 inst_0 sigma prev_lbl s1.
    SND (rename_block_insts rs_b_entry (phi0::phis_rest)) =
      inst_0 :: SND (rename_block_insts rs_1 phis_rest) /\
    (!j. j < LENGTH (phi0::phis_rest) ==>
      (EL j (phi0::phis_rest)).inst_opcode = PHI /\
      (?bv. (EL j (phi0::phis_rest)).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j (phi0::phis_rest)).inst_outputs)) s1 = SOME w) /\
      (EL j (inst0::insts_rest)).inst_opcode = PHI /\
      (EL j (inst0::insts_rest)).inst_outputs =
        (EL j (SND (rename_block_insts rs_b_entry (phi0::phis_rest)))).inst_outputs /\
      resolve_phi prev_lbl (EL j (inst0::insts_rest)).inst_operands =
        SOME (Var (sigma (HD ((EL j (phi0::phis_rest)).inst_outputs))))) ==>
    !j. j < LENGTH phis_rest ==>
      (EL j phis_rest).inst_opcode = PHI /\
      (?bv. (EL j phis_rest).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j phis_rest).inst_outputs)) s1 = SOME w) /\
      (EL j insts_rest).inst_opcode = PHI /\
      (EL j insts_rest).inst_outputs =
        (EL j (SND (rename_block_insts rs_1 phis_rest))).inst_outputs /\
      resolve_phi prev_lbl (EL j insts_rest).inst_operands =
        SOME (Var (sigma (HD ((EL j phis_rest).inst_outputs))))
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `SUC j` mp_tac) >> simp[] >> strip_tac >>
  gvs[rich_listTheory.EL_CONS]
QED

Triviality phi_prefix_sim_head_output[local]:
  !phi0 phis_rest inst0 insts_rest rs_b_entry rs_1 inst_0 out0 sigma prev_lbl s1.
    SND (rename_block_insts rs_b_entry (phi0::phis_rest)) =
      inst_0 :: SND (rename_block_insts rs_1 phis_rest) /\
    inst_0.inst_outputs = [out0] /\
    (!j. j < LENGTH (phi0::phis_rest) ==>
      (EL j (phi0::phis_rest)).inst_opcode = PHI /\
      (?bv. (EL j (phi0::phis_rest)).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j (phi0::phis_rest)).inst_outputs)) s1 = SOME w) /\
      (EL j (inst0::insts_rest)).inst_opcode = PHI /\
      (EL j (inst0::insts_rest)).inst_outputs =
        (EL j (SND (rename_block_insts rs_b_entry (phi0::phis_rest)))).inst_outputs /\
      resolve_phi prev_lbl (EL j (inst0::insts_rest)).inst_operands =
        SOME (Var (sigma (HD ((EL j (phi0::phis_rest)).inst_outputs))))) ==>
    inst0.inst_outputs = [out0]
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[rich_listTheory.EL_CONS] >>
  metis_tac[rich_listTheory.EL_CONS]
QED

Triviality phi_prefix_sim_head_output_from_el[local]:
  !phi0 phis_rest inst0 rs_b_entry rs_1 inst_0 out0.
    inst0.inst_outputs =
      (EL 0 (SND (rename_block_insts rs_b_entry (phi0::phis_rest)))).inst_outputs /\
    SND (rename_block_insts rs_b_entry (phi0::phis_rest)) =
      inst_0 :: SND (rename_block_insts rs_1 phis_rest) /\
    inst_0.inst_outputs = [out0] ==>
    inst0.inst_outputs = [out0]
Proof
  simp[rich_listTheory.EL_CONS]
QED

Triviality all_distinct_outputs_tail[local]:
  !phi phis.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (phi::phis))) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis))
Proof
  simp[ALL_DISTINCT_APPEND]
QED

Triviality not_mem_flat_outputs[local]:
  !x phis.
    ~MEM x (FLAT (MAP (\i. i.inst_outputs) phis)) ==>
    !i. MEM i phis ==> ~MEM x i.inst_outputs
Proof
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Triviality all_distinct_cons_output_not_tail[local]:
  !phi phis x.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (phi::phis))) /\
    MEM x phi.inst_outputs ==>
    !i. MEM i phis ==> ~MEM x i.inst_outputs
Proof
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Triviality all_distinct_cons_tail_output_ne[local]:
  !phi phis base x i.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (phi::phis))) /\
    phi.inst_outputs = [base] /\ MEM i phis /\ MEM x i.inst_outputs ==>
    x <> base
Proof
  rpt strip_tac >> spose_not_then assume_tac >> gvs[] >>
  qpat_x_assum `~MEM base' (FLAT (MAP (\i. i.inst_outputs) phis))` mp_tac >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Triviality sigma_update_preserves_versioned[local]:
  !sigma bvar out rs.
    (!x. colon_free x ==> ?n. sigma x = version_var x n) /\
    out = version_var bvar (SND (push_version rs bvar)) ==>
    !x. colon_free x ==> ?n. ((bvar =+ out) sigma) x = version_var x n
Proof
  rpt strip_tac >>
  Cases_on `x = bvar` >> simp[combinTheory.APPLY_UPDATE_THM]
  >- (qexists_tac `SND (push_version rs bvar)` >> simp[]) >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Triviality sigma_update_preserves_cons_non_output[local]:
  !sigma sigma_tail phi phis bvar out x.
    phi.inst_outputs = [bvar] /\
    (!x. (!i. MEM i phis ==> ~MEM x i.inst_outputs) ==> sigma_tail x = sigma x) /\
    (!i. MEM i (phi::phis) ==> ~MEM x i.inst_outputs) ==>
    ((bvar =+ out) sigma_tail) x = sigma x
Proof
  rpt strip_tac >>
  `x <> bvar` by (
    strip_tac >> gvs[] >>
    qpat_x_assum `!i. i = phi \/ MEM i phis ==> ~MEM bvar i.inst_outputs`
      (qspec_then `phi` mp_tac) >> simp[]) >>
  simp[combinTheory.UPDATE_def] >>
  first_x_assum irule >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i (phi::phis) ==> ~MEM x i.inst_outputs`
    (qspec_then `i` mp_tac) >> simp[]
QED

Triviality sigma_update_preserves_output_latest_cons[local]:
  !sigma_tail sigma rs rs1 phi phis bvar out x i.
    phi.inst_outputs = [bvar] /\
    (!x i. MEM i phis /\ MEM x i.inst_outputs ==>
      sigma_tail x = latest_version (FST (rename_block_insts rs1 phis)) x) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (phi::phis))) /\
    (!x. latest_version rs1 x =
      if x = bvar then out else latest_version rs x) /\
    FST (rename_block_insts rs (phi::phis)) =
      FST (rename_block_insts rs1 phis) /\
    MEM i (phi::phis) /\ MEM x i.inst_outputs ==>
    ((bvar =+ out) sigma_tail) x =
      latest_version (FST (rename_block_insts rs (phi::phis))) x
Proof
  rpt strip_tac >>
  Cases_on `i = phi`
  >- (
    gvs[] >>
    `!i'. MEM i' phis ==> ~MEM bvar i'.inst_outputs` by (
      qpat_x_assum `~MEM bvar (FLAT (MAP _ phis))` mp_tac >>
      simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
    `latest_version (FST (rename_block_insts rs1 phis)) bvar =
     latest_version rs1 bvar` by (
      irule rename_block_insts_non_output_stable_any >> simp[]) >>
    gvs[combinTheory.APPLY_UPDATE_THM]) >>
  `MEM i phis` by gvs[] >>
  `x <> bvar` by (
    mp_tac (Q.SPECL [`phi`, `phis`, `bvar`, `x`, `i`]
      all_distinct_cons_tail_output_ne) >>
    simp[]) >>
  `sigma_tail x = latest_version (FST (rename_block_insts rs1 phis)) x` by (
    qpat_x_assum `!x i. MEM i phis /\ MEM x i.inst_outputs ==> _`
      (qspecl_then [`x`, `i`] mp_tac) >> simp[]) >>
  gvs[combinTheory.APPLY_UPDATE_THM]
QED

Triviality ssa_sim_update_versioned_fresh_dom[local]:
  !sigma s1 s2 bvar out w rs.
    ssa_sim sigma s1 s2 /\
    lookup_var bvar s1 = SOME w /\
    vars_colon_free s1 /\
    colon_free bvar /\
    (!x. colon_free x ==> ?n. sigma x = version_var x n) /\
    out = version_var bvar (SND (push_version rs bvar)) ==>
    ssa_sim ((bvar =+ out) sigma) s1 (update_var out w s2)
Proof
  rpt strip_tac >>
  irule ssa_sim_update_fresh_dom >>
  rpt strip_tac >>
  spose_not_then assume_tac >>
  `colon_free x` by (
    qpat_x_assum `vars_colon_free s1` mp_tac >>
    simp[vars_colon_free_def] >> metis_tac[]) >>
  `?n. sigma x = version_var x n` by (
    qpat_x_assum `!x. colon_free x ==> ?n. sigma x = version_var x n`
      (qspec_then `x` mp_tac) >> simp[]) >>
  rename1 `sigma x = version_var x nx` >>
  `version_var x nx = version_var bvar (SND (push_version rs bvar))` by gvs[] >>
  `x = bvar` by metis_tac[version_var_base_inj] >>
  gvs[]
QED

Triviality eval_one_phi_head_from_rename[local]:
  !rs phi rest bvar inst out s prev_lbl sigma w.
    phi.inst_outputs = [bvar] /\
    inst.inst_outputs =
      (EL 0 (SND (rename_block_insts rs (phi::rest)))).inst_outputs /\
    out = version_var bvar (SND (push_version rs bvar)) /\
    s.vs_prev_bb = SOME prev_lbl /\
    resolve_phi prev_lbl inst.inst_operands = SOME (Var (sigma bvar)) /\
    eval_operand (Var (sigma bvar)) s = SOME w ==>
    eval_one_phi s inst = SOME (out,w)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`rs`, `phi`, `rest`, `bvar`, `inst`, `out`]
    rename_block_cons_head_output_latest) >>
  impl_tac >- simp[] >>
  strip_tac >>
  gvs[eval_one_phi_def]
QED

Triviality phi_prefix_sim_head_step[local]:
  !rs phi rest bvar inst out s prev_lbl sigma w.
    phi.inst_outputs = [bvar] /\
    inst.inst_outputs =
      (EL 0 (SND (rename_block_insts rs (phi::rest)))).inst_outputs /\
    out = version_var bvar (SND (push_version rs bvar)) /\
    s.vs_prev_bb = SOME prev_lbl /\
    resolve_phi prev_lbl inst.inst_operands = SOME (Var (sigma bvar)) /\
    eval_operand (Var (sigma bvar)) s = SOME w ==>
    ?rs' inst'.
      rename_inst rs phi = (rs', inst') /\
      inst'.inst_outputs = [out] /\
      inst.inst_outputs = [out] /\
      (!x. latest_version rs' x =
        if x = bvar then out else latest_version rs x) /\
      SND (rename_block_insts rs (phi::rest)) =
        inst' :: SND (rename_block_insts rs' rest) /\
      FST (rename_block_insts rs (phi::rest)) =
        FST (rename_block_insts rs' rest) /\
      eval_one_phi s inst = SOME (out,w)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`rs`, `phi`, `rest`, `bvar`, `inst`, `out`]
    rename_block_cons_head_output_latest) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `rs'` (qx_choose_then `inst'` strip_assume_tac)) >>
  qexists_tac `rs'` >> qexists_tac `inst'` >>
  rpt conj_tac >> gvs[eval_one_phi_def]
QED

Triviality eval_one_phi_from_lookup[local]:
  !s inst out prev_lbl v w.
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev_lbl /\
    resolve_phi prev_lbl inst.inst_operands = SOME (Var v) /\
    lookup_var v s = SOME w ==>
    eval_one_phi s inst = SOME (out,w)
Proof
  rw[eval_one_phi_def, eval_operand_def]
QED

Triviality eval_one_phi_from_eval_operand[local]:
  !s inst out prev_lbl op w.
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev_lbl /\
    resolve_phi prev_lbl inst.inst_operands = SOME op /\
    eval_operand op s = SOME w ==>
    eval_one_phi s inst = SOME (out,w)
Proof
  rw[eval_one_phi_def]
QED

Triviality eval_one_phi_direct[local]:
  !s2 inst0 out0 w0 prev_lbl sigma base0.
    inst0.inst_outputs = [out0] /\
    s2.vs_prev_bb = SOME prev_lbl /\
    resolve_phi prev_lbl inst0.inst_operands = SOME (Var (sigma base0)) /\
    eval_operand (Var (sigma base0)) s2 = SOME w0 ==>
    eval_one_phi s2 inst0 = SOME (out0,w0)
Proof
  rw[eval_one_phi_def]
QED

Triviality eval_one_phi_from_eval_operand_var[local]:
  !s inst out prev_lbl v w.
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev_lbl /\
    resolve_phi prev_lbl inst.inst_operands = SOME (Var v) /\
    eval_operand (Var v) s = SOME w ==>
    eval_one_phi s inst = SOME (out,w)
Proof
  rw[eval_one_phi_def]
QED

Triviality eval_operand_from_ssa_lookup[local]:
  !sigma s1 s2 x w.
    ssa_sim sigma s1 s2 /\
    lookup_var x s1 = SOME w ==>
    eval_operand (Var (sigma x)) s2 = SOME w
Proof
  rw[eval_operand_def] >> gvs[ssa_sim_def]
QED

Triviality eval_one_phi_from_ssa_head[local]:
  !s2 inst out prev_lbl sigma bvar s1 w.
    inst.inst_outputs = [out] /\
    s2.vs_prev_bb = SOME prev_lbl /\
    resolve_phi prev_lbl inst.inst_operands = SOME (Var (sigma bvar)) /\
    ssa_sim sigma s1 s2 /\
    lookup_var bvar s1 = SOME w ==>
    eval_one_phi s2 inst = SOME (out,w)
Proof
  rpt strip_tac >>
  `lookup_var (sigma bvar) s2 = SOME w` by (gvs[ssa_sim_def] >> metis_tac[]) >>
  gvs[eval_one_phi_def, eval_operand_def, lookup_var_def]
QED

Triviality phi_prefix_sim_cons_finish[local]:
  !sigma sigma_tail rs rs1 phi phis bvar out inst insts s2 s2_tail s1 w.
    phi.inst_outputs = [bvar] /\
    inst.inst_opcode = PHI /\
    eval_one_phi s2 inst = SOME (out,w) /\
    eval_phis s2 insts = OK s2_tail /\
    out = version_var bvar (SND (push_version rs bvar)) /\
    (!x. latest_version rs1 x = if x = bvar then out else latest_version rs x) /\
    FST (rename_block_insts rs (phi::phis)) = FST (rename_block_insts rs1 phis) /\
    (!x. colon_free x ==> ?n. sigma_tail x = version_var x n) /\
    (!x. (!i. MEM i phis ==> ~MEM x i.inst_outputs) ==> sigma_tail x = sigma x) /\
    (!x i. MEM i phis /\ MEM x i.inst_outputs ==>
      sigma_tail x = latest_version (FST (rename_block_insts rs1 phis)) x) /\
    s2_tail.vs_inst_idx = s2.vs_inst_idx /\
    ssa_sim sigma_tail s1 s2_tail /\
    (s2_tail.vs_halted <=> s2.vs_halted) /\
    s2_tail.vs_current_bb = s2.vs_current_bb /\
    s2_tail.vs_prev_bb = s2.vs_prev_bb /\
    lookup_var bvar s1 = SOME w /\
    vars_colon_free s1 /\
    colon_free bvar /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (phi::phis))) ==>
    ?sigma_out s2_phi.
      (!x. colon_free x ==> ?n. sigma_out x = version_var x n) /\
      (!x. (!i. MEM i (phi::phis) ==> ~MEM x i.inst_outputs) ==>
           sigma_out x = sigma x) /\
      (!x i. MEM i (phi::phis) /\ MEM x i.inst_outputs ==>
           sigma_out x = latest_version (FST (rename_block_insts rs (phi::phis))) x) /\
      eval_phis s2 (inst::insts) = OK s2_phi /\
      s2_phi.vs_inst_idx = s2.vs_inst_idx /\
      ssa_sim sigma_out s1 s2_phi /\
      (s2_phi.vs_halted <=> s2.vs_halted) /\
      s2_phi.vs_current_bb = s2.vs_current_bb /\
      s2_phi.vs_prev_bb = s2.vs_prev_bb
Proof
  rpt strip_tac >>
  qexists_tac `(bvar =+ out) sigma_tail` >>
  qexists_tac `update_var out w s2_tail` >>
  sg `!x. colon_free x ==> ?n. ((bvar =+ out) sigma_tail) x = version_var x n` >- (
    match_mp_tac (Q.SPECL [`sigma_tail`, `bvar`, `out`, `rs`]
      sigma_update_preserves_versioned) >>
    simp[]) >>
  conj_tac >- last_x_assum ACCEPT_TAC >>
  conj_tac >- (
    gen_tac >> strip_tac >>
    `x <> bvar` by (
      qpat_x_assum `!i. MEM i (phi::phis) ==> ~MEM x i.inst_outputs`
        (qspec_then `phi` mp_tac) >> simp[]) >>
    simp[combinTheory.APPLY_UPDATE_THM] >>
    first_x_assum irule >>
    rpt strip_tac >>
    qpat_x_assum `!i. MEM i (phi::phis) ==> ~MEM x i.inst_outputs`
      (qspec_then `i` mp_tac) >> simp[]) >>
  conj_tac >- (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`sigma_tail`, `sigma`, `rs`, `rs1`,
      `phi`, `phis`, `bvar`, `out`, `x`, `i`]
      sigma_update_preserves_output_latest_cons) >>
    impl_tac >- (
      rpt conj_tac
      >- qpat_x_assum `phi.inst_outputs = [bvar]` ACCEPT_TAC
      >- qpat_x_assum `!x i. MEM i phis /\ MEM x i.inst_outputs ==> _` ACCEPT_TAC
      >- qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ (phi::phis)))` ACCEPT_TAC
      >- qpat_x_assum `!x. latest_version rs1 x = _` ACCEPT_TAC
      >- qpat_x_assum `FST (rename_block_insts rs (phi::phis)) = _` ACCEPT_TAC
      >- qpat_x_assum `MEM i (phi::phis)` ACCEPT_TAC
      >- qpat_x_assum `MEM x i.inst_outputs` ACCEPT_TAC) >>
    simp[]) >>
  rpt conj_tac >| [
    gvs[eval_phis_def],
    gvs[update_var_def],
    mp_tac (Q.SPECL [`sigma_tail`, `s1`, `s2_tail`, `bvar`, `out`, `w`, `rs`]
      ssa_sim_update_versioned_fresh_dom) >>
    impl_tac >- simp[] >>
    simp[],
    gvs[update_var_def],
    gvs[update_var_def],
    gvs[update_var_def]
  ]
QED

Triviality phi_prefix_sim_head_facts[local]:
  !rs_b_entry phi0 phis_rest inst0 insts_rest s2 prev_lbl sigma s1.
    s2.vs_prev_bb = SOME prev_lbl /\
    ssa_sim sigma s1 s2 /\
    (!j. j < LENGTH (phi0::phis_rest) ==>
      (EL j (phi0::phis_rest)).inst_opcode = PHI /\
      (?bv. (EL j (phi0::phis_rest)).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j (phi0::phis_rest)).inst_outputs)) s1 = SOME w) /\
      (EL j (inst0::insts_rest)).inst_opcode = PHI /\
      (EL j (inst0::insts_rest)).inst_outputs =
        (EL j (SND (rename_block_insts rs_b_entry (phi0::phis_rest)))).inst_outputs /\
      resolve_phi prev_lbl (EL j (inst0::insts_rest)).inst_operands =
        SOME (Var (sigma (HD ((EL j (phi0::phis_rest)).inst_outputs))))) ==>
    ?base0 w0 rs_1 inst_0.
      phi0.inst_outputs = [base0] /\
      lookup_var base0 s1 = SOME w0 /\
      colon_free base0 /\
      rename_inst rs_b_entry phi0 = (rs_1, inst_0) /\
      inst_0.inst_outputs =
        [version_var base0 (SND (push_version rs_b_entry base0))] /\
      inst0.inst_outputs =
        [version_var base0 (SND (push_version rs_b_entry base0))] /\
      (!x. latest_version rs_1 x =
        if x = base0 then version_var base0 (SND (push_version rs_b_entry base0))
        else latest_version rs_b_entry x) /\
      SND (rename_block_insts rs_b_entry (phi0::phis_rest)) =
        inst_0 :: SND (rename_block_insts rs_1 phis_rest) /\
      FST (rename_block_insts rs_b_entry (phi0::phis_rest)) =
        FST (rename_block_insts rs_1 phis_rest) /\
      eval_one_phi s2 inst0 =
        SOME (version_var base0 (SND (push_version rs_b_entry base0)), w0)
Proof
  rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH (phi0::phis_rest) ==> _`
    (fn th => assume_tac th >> qspec_then `0` mp_tac th) >>
  impl_tac >- simp[] >>
  strip_tac >>
  gvs[rich_listTheory.EL_CONS] >>
  rename1 `phi0.inst_outputs = [base0]` >>
  rename1 `lookup_var base0 s1 = SOME w0` >>
  `phi0.inst_outputs = [base0]` by gvs[] >>
  `lookup_var base0 s1 = SOME w0` by gvs[] >>
  `colon_free base0` by gvs[] >>
  `inst0.inst_outputs =
      (EL 0 (SND (rename_block_insts rs_b_entry (phi0::phis_rest)))).inst_outputs` by (
    qpat_x_assum `!j. j < SUC (LENGTH phis_rest) ==> _`
      (qspec_then `0` mp_tac) >>
    simp[rich_listTheory.EL_CONS]) >>
  `resolve_phi prev_lbl inst0.inst_operands = SOME (Var (sigma base0))` by (
    qpat_x_assum `!j. j < SUC (LENGTH phis_rest) ==> _`
      (qspec_then `0` mp_tac) >>
    simp[rich_listTheory.EL_CONS]) >>
  `eval_operand (Var (sigma base0)) s2 = SOME w0` by (
    irule eval_operand_from_ssa_lookup >>
    qexists_tac `s1` >> simp[]) >>
  mp_tac (Q.SPECL [`rs_b_entry`, `phi0`, `phis_rest`, `base0`,
    `inst0`, `version_var base0 (SND (push_version rs_b_entry base0))`,
    `s2`, `prev_lbl`, `sigma`, `w0`] phi_prefix_sim_head_step) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `rs_1` (qx_choose_then `inst_0` strip_assume_tac)) >>
  qexists_tac `rs_1` >> qexists_tac `inst_0` >>
  gvs[]
QED

Theorem phi_prefix_sim[local]:
  !phis rs_b_entry insts s2 prev_lbl sigma s1.
    s2.vs_prev_bb = SOME prev_lbl /\
    ssa_sim sigma s1 s2 /\
    (!x. colon_free x ==> ?n. sigma x = version_var x n) /\
    vars_colon_free s1 /\
    LENGTH phis <= LENGTH insts /\
    (!j. j < LENGTH phis ==>
      (EL j phis).inst_opcode = PHI /\
      (?bv. (EL j phis).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j phis).inst_outputs)) s1 = SOME w) /\
      (EL j insts).inst_opcode = PHI /\
      (EL j insts).inst_outputs =
        (EL j (SND (rename_block_insts rs_b_entry phis))).inst_outputs /\
      resolve_phi prev_lbl (EL j insts).inst_operands =
        SOME (Var (sigma (HD ((EL j phis).inst_outputs))))) /\
    (!j. LENGTH phis <= j /\ j < LENGTH insts ==>
      (EL j insts).inst_opcode <> PHI) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis)) ==>
    ?sigma_out s2_phi.
      (!x. colon_free x ==> ?n. sigma_out x = version_var x n) /\
      (!x. (!i. MEM i phis ==> ~MEM x i.inst_outputs) ==>
           sigma_out x = sigma x) /\
      (!x i. MEM i phis /\ MEM x i.inst_outputs ==>
           sigma_out x =
             latest_version (FST (rename_block_insts rs_b_entry phis)) x) /\
      eval_phis s2 insts = OK s2_phi /\
      s2_phi.vs_inst_idx = s2.vs_inst_idx /\
      ssa_sim sigma_out s1 s2_phi /\
      (s2_phi.vs_halted <=> s2.vs_halted) /\
      s2_phi.vs_current_bb = s2.vs_current_bb /\
      s2_phi.vs_prev_bb = s2.vs_prev_bb
Proof
  rpt gen_tac >>
  MAP_EVERY qid_spec_tac [`s1`, `sigma`, `prev_lbl`, `s2`, `insts`, `rs_b_entry`] >>
  Induct_on `phis`
  >- (
    rpt gen_tac >> strip_tac >>
    qexists_tac `sigma` >> qexists_tac `s2` >>
    Cases_on `insts`
    >- simp[eval_phis_def, rename_block_insts_def] >>
    rename1 `inst0::insts_rest` >>
    `inst0.inst_opcode <> PHI` by (
      qpat_x_assum `!j. LENGTH [] <= j /\ j < LENGTH (inst0::insts_rest) ==> _`
        (qspec_then `0` mp_tac) >> simp[]) >>
    simp[eval_phis_def, rename_block_insts_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `phi0::phis_rest` >>
  `ssa_sim sigma s1 s2` by
    qpat_x_assum `ssa_sim sigma s1 s2` ACCEPT_TAC >>
  `s2.vs_prev_bb = SOME prev_lbl` by
    qpat_x_assum `s2.vs_prev_bb = SOME prev_lbl` ACCEPT_TAC >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis_rest))` by (
    qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ (phi0::phis_rest)))` mp_tac >>
    simp[ALL_DISTINCT_APPEND]) >>
  Cases_on `insts`
  >- gvs[] >>
  rename1 `LENGTH (phi0::phis_rest) <= LENGTH (inst0::insts_rest)` >>
  `!j. LENGTH phis_rest <= j /\ j < LENGTH insts_rest ==>
      (EL j insts_rest).inst_opcode <> PHI` by (
    rpt strip_tac >>
    qpat_x_assum `!j. LENGTH (phi0::phis_rest) <= j /\
        j < LENGTH (inst0::insts_rest) ==> _`
      (qspec_then `SUC j` mp_tac) >>
    impl_tac >- (simp[] >> DECIDE_TAC) >>
    simp[rich_listTheory.EL_CONS]) >>
  `!j. j < LENGTH phis_rest ==>
      (EL j phis_rest).inst_opcode = PHI /\
      (?bv. (EL j phis_rest).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j phis_rest).inst_outputs)) s1 = SOME w) /\
      (EL j insts_rest).inst_opcode = PHI /\
      (EL j insts_rest).inst_outputs =
        (EL (SUC j) (SND (rename_block_insts rs_b_entry (phi0::phis_rest)))).inst_outputs /\
      resolve_phi prev_lbl (EL j insts_rest).inst_operands =
        SOME (Var (sigma (HD ((EL j phis_rest).inst_outputs))))` by (
    rpt strip_tac >>
    qpat_x_assum `!j. j < LENGTH (phi0::phis_rest) ==> _`
      (qspec_then `SUC j` mp_tac) >>
    impl_tac >- simp[] >>
    simp[rich_listTheory.EL_CONS]) >>
  mp_tac (Q.SPECL [`rs_b_entry`, `phi0`, `phis_rest`, `inst0`,
    `insts_rest`, `s2`, `prev_lbl`, `sigma`, `s1`]
    phi_prefix_sim_head_facts) >>
  impl_tac >- (
    rpt conj_tac
    >- qpat_x_assum `s2.vs_prev_bb = SOME prev_lbl` ACCEPT_TAC
    >- qpat_x_assum `ssa_sim sigma s1 s2` ACCEPT_TAC
    >- qpat_x_assum `!j. j < LENGTH (phi0::phis_rest) ==> _` ACCEPT_TAC) >>
  disch_then (qx_choose_then `base0` (qx_choose_then `w0`
    (qx_choose_then `rs_1` (qx_choose_then `inst_0` strip_assume_tac)))) >>
  `inst0.inst_opcode = PHI` by (
    qpat_x_assum `!j. j < LENGTH (phi0::phis_rest) ==> _`
      (qspec_then `0` mp_tac) >>
    simp[rich_listTheory.EL_CONS]) >>
  `LENGTH phis_rest <= LENGTH insts_rest` by gvs[] >>
  mp_tac (Q.SPECL [`phi0`, `phis_rest`, `inst0`, `insts_rest`,
    `rs_b_entry`, `rs_1`, `inst_0`, `sigma`, `prev_lbl`, `s1`]
    phi_prefix_sim_tail_bundled_by_snd) >>
  impl_tac >- (
    rpt conj_tac
    >- qpat_x_assum `SND (rename_block_insts rs_b_entry (phi0::phis_rest)) = _` ACCEPT_TAC
    >- qpat_x_assum `!j. j < LENGTH (phi0::phis_rest) ==> _` ACCEPT_TAC) >>
  disch_then (fn tail_th =>
    FIRST_X_ASSUM
      (qspecl_then [`rs_1`, `insts_rest`, `s2`, `prev_lbl`, `sigma`, `s1`] mp_tac) >>
    impl_tac >- (
      conj_tac >- qpat_x_assum `s2.vs_prev_bb = SOME prev_lbl` ACCEPT_TAC >>
      conj_tac >- qpat_x_assum `ssa_sim sigma s1 s2` ACCEPT_TAC >>
      conj_tac >- qpat_x_assum `!x. colon_free x ==> ?n. sigma x = version_var x n` ACCEPT_TAC >>
      conj_tac >- qpat_x_assum `vars_colon_free s1` ACCEPT_TAC >>
      conj_tac >- qpat_x_assum `LENGTH phis_rest <= LENGTH insts_rest` ACCEPT_TAC >>
      conj_tac >- ACCEPT_TAC tail_th >>
      conj_tac >- qpat_x_assum `!j. LENGTH phis_rest <= j /\ j < LENGTH insts_rest ==> _` ACCEPT_TAC >>
      qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ phis_rest))` ACCEPT_TAC)) >>
  strip_tac >>
  rename1 `eval_phis s2 insts_rest = OK s2_tail` >>
  mp_tac (Q.SPECL [`sigma`, `sigma_out`, `rs_b_entry`, `rs_1`,
    `phi0`, `phis_rest`, `base0`,
    `version_var base0 (SND (push_version rs_b_entry base0))`,
    `inst0`, `insts_rest`, `s2`, `s2_tail`, `s1`, `w0`]
    phi_prefix_sim_cons_finish) >>
  impl_tac >- (
    rpt conj_tac
    >- qpat_x_assum `phi0.inst_outputs = [base0]` ACCEPT_TAC
    >- qpat_x_assum `inst0.inst_opcode = PHI` ACCEPT_TAC
    >- qpat_x_assum `eval_one_phi s2 inst0 = SOME _` ACCEPT_TAC
    >- qpat_x_assum `eval_phis s2 insts_rest = OK s2_tail` ACCEPT_TAC
    >- simp[]
    >- qpat_x_assum `!x. latest_version rs_1 x = _` ACCEPT_TAC
    >- qpat_x_assum `FST (rename_block_insts rs_b_entry (phi0::phis_rest)) = _` ACCEPT_TAC
    >- qpat_x_assum `!x. colon_free x ==> ?n. sigma_out x = version_var x n` ACCEPT_TAC
    >- qpat_x_assum `!x. (!i. MEM i phis_rest ==> ~MEM x i.inst_outputs) ==> _` ACCEPT_TAC
    >- qpat_x_assum `!x i. MEM i phis_rest /\ MEM x i.inst_outputs ==> _` ACCEPT_TAC
    >- qpat_x_assum `s2_tail.vs_inst_idx = s2.vs_inst_idx` ACCEPT_TAC
    >- qpat_x_assum `ssa_sim sigma_out s1 s2_tail` ACCEPT_TAC
    >- qpat_x_assum `s2_tail.vs_halted <=> s2.vs_halted` ACCEPT_TAC
    >- qpat_x_assum `s2_tail.vs_current_bb = s2.vs_current_bb` ACCEPT_TAC
    >- qpat_x_assum `s2_tail.vs_prev_bb = s2.vs_prev_bb` ACCEPT_TAC
    >- qpat_x_assum `lookup_var base0 s1 = SOME w0` ACCEPT_TAC
    >- qpat_x_assum `vars_colon_free s1` ACCEPT_TAC
    >- qpat_x_assum `colon_free base0` ACCEPT_TAC
    >- qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ (phi0::phis_rest)))` ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

(* OBSOLETE sequential-PHI proof preserved for reference. *)
(*
Theorem phi_prefix_sim_old[local]:
  !phis rs_b_entry bb' s2 prev_lbl sigma s1 idx.
    s2.vs_inst_idx = idx /\
    s2.vs_prev_bb = SOME prev_lbl /\
    ssa_sim sigma s1 s2 /\
    (!x. colon_free x ==> ?n. sigma x = version_var x n) /\
    vars_colon_free s1 /\
    idx + LENGTH phis <= LENGTH bb'.bb_instructions /\
    (* Bundled per-element properties *)
    (!j. j < LENGTH phis ==>
      (EL j phis).inst_opcode = PHI /\
      (?bv. (EL j phis).inst_outputs = [bv] /\ colon_free bv) /\
      (?w. lookup_var (HD ((EL j phis).inst_outputs)) s1 = SOME w) /\
      (EL (idx + j) bb'.bb_instructions).inst_opcode = PHI /\
      (EL (idx + j) bb'.bb_instructions).inst_outputs =
        (EL j (SND (rename_block_insts rs_b_entry phis))).inst_outputs /\
      resolve_phi prev_lbl
        (EL (idx + j) bb'.bb_instructions).inst_operands =
        SOME (Var (sigma (HD ((EL j phis).inst_outputs))))) /\
    (* Distinct pre-rename bases *)
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis)) ==>
    ?sigma_out.
      (!x. colon_free x ==> ?n. sigma_out x = version_var x n) /\
      (!x. (!i. MEM i phis ==> ~MEM x i.inst_outputs) ==>
           sigma_out x = sigma x) /\
      (!x i. MEM i phis /\ MEM x i.inst_outputs ==>
           sigma_out x =
             latest_version (FST (rename_block_insts rs_b_entry phis)) x) /\
      !fuel ctx.
        ?s2_mid.
          s2_mid.vs_inst_idx = idx + LENGTH phis /\
          ssa_sim sigma_out s1 s2_mid /\
          (s2_mid.vs_halted <=> s2.vs_halted) /\
          s2_mid.vs_current_bb = s2.vs_current_bb /\
          s2_mid.vs_prev_bb = s2.vs_prev_bb /\
          exec_block fuel ctx bb' s2 = exec_block fuel ctx bb' s2_mid
Proof
  Induct
  >- (
    (* Base: phis = [] — sigma_out = sigma, no conversion needed *)
    rpt gen_tac >> strip_tac >>
    qexists_tac `sigma` >> simp[rename_block_insts_def] >>
    rpt gen_tac >> qexists_tac `s2` >> simp[]) >>
  (* Step: phis = phi0 :: phis_rest *)
  rpt gen_tac >> strip_tac >>
  rename1 `phi0 :: phis_rest` >>
  rpt gen_tac >>
  (* Stash IH in ref cell — it poisons all search tactics *)
  stash_ih ih_ref >>
  (* Extract j=0 facts; stash bundled hyp in ref cell to avoid poisoning *)
  FIRST_X_ASSUM (fn th =>
    if is_forall (concl th) andalso
       type_of (fst (dest_forall (concl th))) = ``:num`` andalso
       is_imp (snd (dest_forall (concl th)))
    then (bundled_ref := th;
          mp_tac (SIMP_RULE (srw_ss()) [] (Q.SPEC `0` th)) >> strip_tac)
    else FAIL_TAC "not bundled") >>
  `?base0. phi0.inst_outputs = [base0] /\ colon_free base0` by metis_tac[] >>
  `?w0. lookup_var base0 s1 = SOME w0` by (gvs[] >> metis_tac[]) >>
  (* Derive renamed output for phi0 *)
  `?rs_1 inst_0.
    rename_inst rs_b_entry phi0 = (rs_1, inst_0) /\
    inst_0.inst_outputs = [version_var base0 (SND (push_version rs_b_entry base0))] /\
    (!x. latest_version rs_1 x =
      if x = base0 then version_var base0 (SND (push_version rs_b_entry base0))
      else latest_version rs_b_entry x)` by (
    simp[rename_inst_def, LET_THM] >>
    mp_tac (Q.SPECL [`rs_b_entry`, `base0`] rename_outputs_single_latest) >>
    simp[LET_THM] >>
    pairarg_tac >> simp[]) >>
  qabbrev_tac `out0 = version_var base0 (SND (push_version rs_b_entry base0))` >>
  `EL 0 (SND (rename_block_insts rs_b_entry (phi0::phis_rest))) =
   inst_0` by (
    simp[rename_block_insts_def, LET_THM] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  `(EL idx bb'.bb_instructions).inst_outputs = [out0]` by gvs[] >>
  (* Domain-restricted freshness: for vars in s1, sigma x <> out0 when x <> base0 *)
  `!x. x <> base0 /\ (?v. lookup_var x s1 = SOME v) ==> sigma x <> out0` by (
    rpt strip_tac >> gvs[Abbr `out0`] >>
    `colon_free x` by (
      gvs[vars_colon_free_def] >>
      first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
    `?n. sigma x = version_var x n` by metis_tac[] >>
    metis_tac[version_var_base_inj]) >>
  (* Execute one PHI step *)
  `~is_terminator PHI` by simp[is_terminator_def] >>
  `idx < LENGTH bb'.bb_instructions` by (
    qpat_x_assum `idx + LENGTH _ <= _` mp_tac >> simp[]) >>
  (* step_inst_base for PHI: reads sigma(base0) from s2, writes to out0 *)
  `step_inst_base (EL idx bb'.bb_instructions) s2 =
   OK (update_var out0 w0 s2)` by (
    simp[step_inst_base_def] >>
    `eval_operand (Var (sigma base0)) s2 = SOME w0` by (
      simp[eval_operand_def] >>
      `lookup_var (sigma base0) s2 = SOME w0` by (
        gvs[ssa_sim_def] >> metis_tac[]) >>
      gvs[lookup_var_def]) >>
    gvs[]) >>
  (* Apply exec_block_step_non_term to peel this step *)
  `!fuel ctx. exec_block fuel ctx bb' s2 =
   exec_block fuel ctx bb'
     ((update_var out0 w0 s2) with vs_inst_idx := SUC idx)` by (
    rpt gen_tac >>
    mp_tac (Q.SPECL [`bb'`, `fuel`, `ctx`, `s2`,
      `EL idx bb'.bb_instructions`, `update_var out0 w0 s2`]
      exec_block_step_non_term) >>
    (impl_tac >- gvs[]) >>
    gvs[]) >>
  qabbrev_tac `s2_1 = (update_var out0 w0 s2) with vs_inst_idx := SUC idx` >>
  qabbrev_tac `sigma_1 = (base0 =+ out0) sigma` >>
  `ssa_sim ((base0 =+ out0) sigma) s1 (update_var out0 w0 s2)` by (
    irule ssa_sim_update_fresh_dom >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ssa_sim sigma_1 s1 s2_1` by (
    qpat_x_assum `ssa_sim _ s1 (update_var _ _ _)` mp_tac >>
    simp[Abbr `s2_1`, Abbr `sigma_1`,
         ssa_sim_def, update_var_def, lookup_var_def]) >>
  `s2_1.vs_inst_idx = SUC idx` by simp[Abbr `s2_1`, update_var_def] >>
  `s2_1.vs_prev_bb = SOME prev_lbl` by (
    simp[Abbr `s2_1`, update_var_def]) >>
  `s2_1.vs_halted = s2.vs_halted` by (
    simp[Abbr `s2_1`, update_var_def]) >>
  `s2_1.vs_current_bb = s2.vs_current_bb` by (
    simp[Abbr `s2_1`, update_var_def]) >>
  (* Stash ALL poisonous universals before IH application *)
  stash_cond cond_ref >>
  stash_fresh fresh_ref >>
  (* Apply IH from ref cell — must defer !ref to tactic application time *)
  (fn g => mp_tac (Q.SPECL [`rs_1`, `bb'`, `s2_1`, `prev_lbl`,
    `sigma_1`, `s1`, `SUC idx`] (!ih_ref)) g) >>
  (impl_tac >- (
    rpt conj_tac
    >- first_assum ACCEPT_TAC  (* IH1: vs_inst_idx *)
    >- first_assum ACCEPT_TAC  (* IH2: vs_prev_bb *)
    >- first_assum ACCEPT_TAC  (* IH3: ssa_sim *)
    >- (  (* IH4: fresh *)
      rpt strip_tac >>
      simp[Abbr `sigma_1`, combinTheory.UPDATE_def] >>
      Cases_on `x = base0` >> simp[]
      >- (simp[Abbr `out0`] >>
          qexists_tac `SND (push_version rs_b_entry base0)` >> simp[])
      >> ((fn g => mp_tac (Q.SPEC `x` (!fresh_ref)) g) >> simp[]))
    >- first_assum ACCEPT_TAC  (* IH5: vars_colon_free *)
    >- (  (* IH6: arithmetic *)
      qpat_x_assum `idx + LENGTH _ <= _` mp_tac >> simp[])
    >- (  (* IH7: bundled per-element *)
      rpt gen_tac >> strip_tac >>
      `SUC j < LENGTH (phi0::phis_rest)` by (simp[]) >>
      (fn g => mp_tac (SIMP_RULE (srw_ss()) [] (Q.SPEC `SUC j` (!bundled_ref))) g) >>
      `SUC idx + j = idx + SUC j` by (DECIDE_TAC) >>
      strip_tac >>
      `?bv_j. (EL j phis_rest).inst_outputs = [bv_j] /\ colon_free bv_j` by (
        metis_tac[]) >>
      `bv_j <> base0` by (
        mp_tac (Q.SPECL [`phi0`, `phis_rest`, `j`, `base0`, `bv_j`]
          all_distinct_head_tail_disjoint) >>
        simp[]) >>
      `(EL (idx + SUC j) bb'.bb_instructions).inst_outputs =
        (EL j (SND (rename_block_insts rs_1 phis_rest))).inst_outputs` by (
        simp[] >> simp[rename_block_insts_def, LET_THM] >>
        pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
      simp[Abbr `sigma_1`, combinTheory.UPDATE_def] >>
      metis_tac[])
    >> (  (* IH8: ALL_DISTINCT *)
      qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ (phi0::phis_rest)))` mp_tac >>
      simp[ALL_DISTINCT_APPEND]))) >>
  strip_tac >>
  qexists_tac `sigma_out` >>
  `FST (rename_block_insts rs_b_entry (phi0::phis_rest)) =
   FST (rename_block_insts rs_1 phis_rest)` by (
    simp[rename_block_insts_def, LET_THM] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC  (* freshness *)
  >- (  (* non-PHI preservation: sigma_out x = sigma x for x not in phi0::rest *)
    gen_tac >> strip_tac >>
    (* x not in phis_rest outputs *)
    `!i. MEM i phis_rest ==> ~MEM x i.inst_outputs` by (
      rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
    `sigma_out x = sigma_1 x` by metis_tac[] >>
    (* x not in phi0.inst_outputs so x <> base0 *)
    `x <> base0` by (
      spose_not_then strip_assume_tac >> gvs[] >>
      first_x_assum (qspec_then `phi0` mp_tac) >> simp[]) >>
    gvs[Abbr `sigma_1`, combinTheory.UPDATE_def])
  >- (  (* PHI characterization: sigma_out x = latest_version rs_final x for PHI outputs *)
    rpt strip_tac >>
    Cases_on `i = phi0`
    >- (
      (* phi0 case: x = base0, sigma_out = out0 = latest_version rs_final base0 *)
      `x = base0` by (
        `phi0.inst_outputs = [base0]` by first_assum ACCEPT_TAC >>
        gvs[]) >>
      `!i'. MEM i' phis_rest ==> ~MEM base0 i'.inst_outputs` by (
        rpt strip_tac >>
        qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ (phi0::phis_rest)))` mp_tac >>
        simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
        metis_tac[]) >>
      `sigma_out base0 = sigma_1 base0` by metis_tac[] >>
      (* Prove stability BEFORE gvs destroys the !i'. form *)
      `latest_version (FST (rename_block_insts rs_1 phis_rest)) base0 =
       latest_version rs_1 base0` by (
        irule rename_block_insts_non_output_stable_any >>
        first_assum ACCEPT_TAC) >>
      (* Bring back stashed cond to resolve latest_version rs_1 base0 *)
      (fn g => mp_tac (Q.SPEC `base0` (!cond_ref)) g) >>
      gvs[Abbr `sigma_1`, combinTheory.UPDATE_def, Abbr `out0`])
    >> (
      (* phis_rest case: use IH PHI characterization *)
      `MEM i phis_rest` by (Cases_on `i = phi0` >> gvs[]) >>
      `sigma_out x = latest_version (FST (rename_block_insts rs_1 phis_rest)) x`
        by metis_tac[] >>
      gvs[]))
  >> (
    rpt gen_tac >>
    first_x_assum (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
    qexists_tac `s2_mid` >> simp[LENGTH] >> metis_tac[])
QED
*)
(* rename_outputs multi-output: latest_version evolves as FOLDL of updates *)
Theorem rename_outputs_multi_latest[local]:
  !outs rs rs' outs'.
    rename_outputs rs outs = (rs', outs') ==>
    !x. latest_version rs' x =
      FOLDL (\s (o1,o2). (o1 =+ o2) s) (latest_version rs)
            (ZIP (outs, outs')) x
Proof
  Induct >> rw[rename_outputs_def, ZIP_def, FOLDL] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.SPECL [`rs`, `h`] latest_version_push) >>
  rw[LET_THM] >>
  Cases_on `push_version rs h` >> gvs[] >>
  `latest_version q = (h =+ version_var h r) (latest_version rs)` by
    (rw[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> metis_tac[]) >>
  gvs[ZIP_def, FOLDL] >>
  first_x_assum drule >> simp[]
QED

(* rename_inst sigma evolution for SINGLE output:
   latest_version evolves as a pointwise update at the output variable.
   Uses rename_outputs_single_latest. *)
Theorem rename_inst_single_output_evolution[local]:
  !rs inst.
    inst.inst_opcode <> PHI /\ LENGTH inst.inst_outputs = 1 ==>
    let (rs', inst') = rename_inst rs inst in
    latest_version rs' (HD inst.inst_outputs) = HD inst'.inst_outputs /\
    (!x. x <> HD inst.inst_outputs ==>
         latest_version rs' x = latest_version rs x)
Proof
  rw[rename_inst_def, LET_THM] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.SPECL [`rs`, `h`] rename_outputs_single_latest) >>
  rw[LET_THM] >> pairarg_tac >> gvs[]
QED

(* rename_inst with empty outputs: rename state unchanged *)
Theorem rename_inst_empty_outputs_id[local]:
  !rs inst.
    inst.inst_opcode <> PHI /\ inst.inst_outputs = [] ==>
    FST (rename_inst rs inst) = rs
Proof
  rw[rename_inst_def, LET_THM, rename_outputs_def]
QED

(* Corollary: latest_version unchanged *)
Theorem rename_inst_zero_output_evolution[local]:
  !rs inst.
    inst.inst_opcode <> PHI /\ inst.inst_outputs = [] ==>
    !x. latest_version (FST (rename_inst rs inst)) x = latest_version rs x
Proof
  metis_tac[rename_inst_empty_outputs_id]
QED

(* inst_wf + is_terminator ==> inst_outputs = [] *)
Theorem inst_wf_terminator_no_outputs[local]:
  !inst. inst_wf inst /\ is_terminator inst.inst_opcode ==>
         inst.inst_outputs = []
Proof
  rw[inst_wf_def] >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
QED

(* For a well-formed terminated block, rename state at terminator = rename state
   at end of block (terminator doesn't change rs) *)
Theorem rename_block_insts_terminator_end[local]:
  !rs0 insts.
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode /\
    (LAST insts).inst_opcode <> PHI /\
    (LAST insts).inst_outputs = [] ==>
    FST (rename_block_insts rs0 insts) =
    FST (rename_block_insts rs0 (TAKE (PRE (LENGTH insts)) insts))
Proof
  rpt strip_tac >>
  qabbrev_tac `j = PRE (LENGTH insts)` >>
  `j < LENGTH insts /\ LENGTH insts = SUC j` by
    (unabbrev_all_tac >> Cases_on `insts` >> fs[]) >>
  `TAKE (SUC j) insts = insts` by metis_tac[TAKE_LENGTH_ID_rwt] >>
  `FST (rename_block_insts rs0 (TAKE (SUC j) insts)) =
   FST (rename_inst (FST (rename_block_insts rs0 (TAKE j insts)))
     (EL j insts))` by metis_tac[rename_block_insts_step] >>
  `EL j insts = LAST insts` by simp[LAST_EL, Abbr `j`] >>
  metis_tac[rename_inst_empty_outputs_id]
QED

(* output_fresh from the pipeline: colon_free outputs + vars_colon_free state
   ensures version_var names don't collide with latest_version for defined vars *)
Theorem rename_inst_output_fresh[local]:
  !rs inst s1.
    inst.inst_opcode <> PHI /\
    EVERY colon_free inst.inst_outputs /\
    bound_output_count inst.inst_opcode <= LENGTH inst.inst_outputs /\
    vars_colon_free s1 ==>
    output_fresh (latest_version rs) inst (SND (rename_inst rs inst)) s1
Proof
  rpt strip_tac >> rw[output_fresh_def, LET_THM] >>
  `ALL_DISTINCT (SND (rename_inst rs inst)).inst_outputs /\
   LENGTH (SND (rename_inst rs inst)).inst_outputs = LENGTH inst.inst_outputs /\
   !i. i < LENGTH inst.inst_outputs ==>
     ?ver. EL i (SND (rename_inst rs inst)).inst_outputs =
           version_var (EL i inst.inst_outputs) ver`
    by metis_tac[rename_inst_output_props] >>
  rpt conj_tac
  >- simp[]
  >- metis_tac[ALL_DISTINCT_TAKE]
  >> rpt strip_tac >>
     `colon_free (EL i inst.inst_outputs)` by gvs[EVERY_EL] >>
     `colon_free x` by metis_tac[vars_colon_free_def] >>
     `?ver. EL i (SND (rename_inst rs inst)).inst_outputs =
             version_var (EL i inst.inst_outputs) ver` by
       (`i < LENGTH inst.inst_outputs` by decide_tac >>
        qpat_x_assum `!j. j < LENGTH inst.inst_outputs ==> _`
          (qspec_then `i` mp_tac) >> simp[]) >>
     metis_tac[latest_version_no_alias]
QED

(* inst_renamed sigma follows from inst_renamed (latest_version rs) when
   sigma agrees with latest_version rs on all operand var-bases. *)
Theorem inst_renamed_from_agreement[local]:
  !sigma rs inst1.
    inst1.inst_opcode <> PHI /\
    (!x. MEM (Var x) inst1.inst_operands ==> sigma x = latest_version rs x) ==>
    inst_renamed sigma inst1 (SND (rename_inst rs inst1))
Proof
  rpt strip_tac >>
  `inst_renamed (latest_version rs) inst1 (SND (rename_inst rs inst1))`
    by (irule rename_inst_produces_inst_renamed >> simp[]) >>
  gvs[inst_renamed_def] >>
  simp[MAP_EQ_f] >> rpt strip_tac >>
  Cases_on `e` >> simp[renamed_operand_def]
QED

(* output_fresh sigma follows from freshness (sigma maps colon_free to version_var)
   when inst1.inst_outputs are colon_free and vars_colon_free s1. *)
Theorem output_fresh_from_freshness[local]:
  !sigma rs inst1 s1.
    inst1.inst_opcode <> PHI /\
    EVERY colon_free inst1.inst_outputs /\
    bound_output_count inst1.inst_opcode <= LENGTH inst1.inst_outputs /\
    vars_colon_free s1 /\
    (!v. colon_free v ==> ?n. sigma v = version_var v n) ==>
    output_fresh sigma inst1 (SND (rename_inst rs inst1)) s1
Proof
  rpt strip_tac >> rw[output_fresh_def, LET_THM] >>
  `ALL_DISTINCT (SND (rename_inst rs inst1)).inst_outputs /\
   LENGTH (SND (rename_inst rs inst1)).inst_outputs = LENGTH inst1.inst_outputs /\
   !i. i < LENGTH inst1.inst_outputs ==>
     ?ver. EL i (SND (rename_inst rs inst1)).inst_outputs =
           version_var (EL i inst1.inst_outputs) ver`
    by metis_tac[rename_inst_output_props] >>
  rpt conj_tac
  >- simp[]
  >- metis_tac[ALL_DISTINCT_TAKE]
  >> rpt strip_tac >>
     `colon_free (EL i inst1.inst_outputs)` by gvs[EVERY_EL] >>
     `colon_free x` by metis_tac[vars_colon_free_def] >>
     `?ver. EL i (SND (rename_inst rs inst1)).inst_outputs =
             version_var (EL i inst1.inst_outputs) ver` by
       (`i < LENGTH inst1.inst_outputs` by decide_tac >>
        qpat_x_assum `!j. j < LENGTH inst1.inst_outputs ==> _`
          (qspec_then `i` mp_tac) >> simp[]) >>
     metis_tac[sigma_no_alias]
QED

(* When an opcode binds all of its syntactic outputs, output_sigma is exactly
   the latest_version map produced by rename_inst. *)
Theorem output_sigma_latest_rename_inst[local]:
  !rs inst.
    inst.inst_opcode <> PHI /\
    bound_output_count inst.inst_opcode = LENGTH inst.inst_outputs ==>
    output_sigma inst.inst_opcode inst.inst_outputs
      (SND (rename_inst rs inst)).inst_outputs (latest_version rs) =
    latest_version (FST (rename_inst rs inst))
Proof
  rpt strip_tac >> rw[FUN_EQ_THM, output_sigma_def] >>
  `TAKE (bound_output_count inst.inst_opcode) inst.inst_outputs =
   inst.inst_outputs` by simp[] >>
  `LENGTH (SND (rename_inst rs inst)).inst_outputs =
   LENGTH inst.inst_outputs` by metis_tac[rename_inst_outputs_length] >>
  `TAKE (bound_output_count inst.inst_opcode)
      (SND (rename_inst rs inst)).inst_outputs =
   (SND (rename_inst rs inst)).inst_outputs` by simp[] >>
  simp[] >>
  gvs[rename_inst_def, LET_THM] >> pairarg_tac >> gvs[] >>
  drule rename_outputs_multi_latest >> simp[TAKE_LENGTH_ID_rwt]
QED

(* ASSIGN follows the same all-output sigma interface as every other
   non-INVOKE instruction. *)
Theorem assign_renamed_sim[local]:
  !sigma inst1 inst2 s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    output_fresh sigma inst1 inst2 s1 /\
    inst1.inst_opcode = ASSIGN /\
    step_inst_base inst1 s1 = OK s1' ==>
    ?s2'. step_inst_base inst2 s2 = OK s2' /\
          ssa_sim (output_sigma inst1.inst_opcode
                     inst1.inst_outputs inst2.inst_outputs sigma) s1' s2'
Proof
  rpt strip_tac >> gvs[inst_renamed_def, output_fresh_def] >>
  gvs[step_inst_base_def, AllCaseEqs()] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  Cases_on `inst2.inst_outputs` >> gvs[] >>
  simp[output_sigma_def, bound_output_count_def, opcode_has_output_def] >>
  irule ssa_sim_update_var >>
  gvs[lookup_var_def, bound_output_count_def, opcode_has_output_def]
QED

(* setup_callee produces identical states under ssa_sim *)
Theorem setup_callee_ssa_sim[local]:
  !sigma s1 s2 fn args.
    ssa_sim sigma s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[setup_callee_def, ssa_sim_def, venom_state_component_equality]
QED

(* merge_callee_state preserves ssa_sim (callee state is shared) *)
Theorem merge_callee_ssa_sim[local]:
  !sigma s1 s2 cs.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (merge_callee_state s1 cs) (merge_callee_state s2 cs)
Proof
  rw[ssa_sim_def, merge_callee_state_def, lookup_var_def]
QED

(* bind_outputs: LENGTH, expansion, and synthesis *)
Theorem bind_outputs_LENGTH[local]:
  !outs vals s s'. bind_outputs outs vals s = SOME s' ==>
    LENGTH outs = LENGTH vals
Proof
  rw[bind_outputs_def]
QED

Theorem bind_outputs_FOLDL[local]:
  !outs vals s s'. bind_outputs outs vals s = SOME s' ==>
    s' = FOLDL (\st (nm,vl). update_var nm vl st) s (ZIP (outs, vals))
Proof
  rw[bind_outputs_def]
QED

Theorem bind_outputs_LENGTH_SOME[local]:
  !outs vals s. LENGTH outs = LENGTH vals ==>
    bind_outputs outs vals s =
      SOME (FOLDL (\st (nm,vl). update_var nm vl st) s (ZIP (outs, vals)))
Proof
  rw[bind_outputs_def]
QED

(* Unified step simulation for ALL non-terminator, non-PHI instructions.
   Combines step_inst_base_renamed_sim (most opcodes) +
   assign_renamed_sim + invoke case (callee reflexive).
   For INVOKE with multiple outputs, needs ALL_DISTINCT + per-element
   non-aliasing (satisfied by pipeline via colon_free + latest_version).
 *)

(* Precompute constructor-specific clauses so the generic theorem never
   expands step_inst_base into one monolithic opcode case expression. *)
local
  val nt_ni_ops = List.filter (fn op_tm =>
    let val nt = EVAL ``~is_terminator ^op_tm``
        val ni = EVAL ``^op_tm <> INVOKE``
    in aconv (rhs (concl nt)) T andalso aconv (rhs (concl ni)) T end
  ) (TypeBase.constructors_of ``:opcode``);

  val nt_ni_clauses = map (fn op_tm =>
    SIMP_CONV (srw_ss()) [step_inst_base_def]
      (mk_comb(mk_comb(``step_inst_base``,
        ``inst with inst_opcode := ^op_tm``), ``st:venom_state``))
  ) nt_ni_ops;

  val exec_helper_defs = [
    exec_pure1_def, exec_pure2_def, exec_pure3_def,
    exec_read0_def, exec_read1_def, exec_write2_def,
    exec_alloca_def, exec_ext_call_def, exec_create_def,
    exec_delegatecall_def, LET_THM, AllCaseEqs()];

  val per_op_not_halt_intret = map (fn (op_tm, clause) =>
    prove(
      ``inst.inst_opcode = ^op_tm ==>
        (!v. step_inst_base inst st <> Halt v) /\
        (!vals v. step_inst_base inst st <> IntRet vals v)``,
      strip_tac >>
      `inst with inst_opcode := ^op_tm = inst`
        by simp[instruction_component_equality] >>
      pop_assum (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
      ONCE_REWRITE_TAC [clause] >> simp exec_helper_defs)
  ) (ListPair.zip(nt_ni_ops, nt_ni_clauses));
in
  val step_inst_base_not_halt_intret_combined =
    LIST_CONJ per_op_not_halt_intret;
end

Triviality step_inst_base_not_halt_intret:
  !inst s.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    (!v. step_inst_base inst s <> Halt v) /\
    (!vals v. step_inst_base inst s <> IntRet vals v)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def, step_inst_base_not_halt_intret_combined]
QED

(* Non-terminator, non-INVOKE step_inst_base only returns OK, Error, or Abort. *)
Theorem step_inst_base_non_term_result[local]:
  !inst s.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    (?s'. step_inst_base inst s = OK s') \/
    (?e. step_inst_base inst s = Error e) \/
    (?a s'. step_inst_base inst s = Abort a s')
Proof
  rpt strip_tac >>
  drule_all step_inst_base_not_halt_intret >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[]
QED

(* Well-formed non-PHI/non-INVOKE instructions bind exactly the number of
   outputs described by the semantic output_sigma interface. *)
Theorem inst_wf_bound_output_count[local]:
  !inst.
    inst_wf inst /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode ==>
    bound_output_count inst.inst_opcode = LENGTH inst.inst_outputs
Proof
  rw[inst_wf_def] >> Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, bound_output_count_def, opcode_has_output_def]
QED

(* Bridge lemma: one well-formed non-terminator step evolves every bound
   output and therefore reaches the latest_version map from rename_inst. *)
Theorem step_base_sigma_bridge[local]:
  !rs inst1 s1 s2 s1'.
    ssa_sim (latest_version rs) s1 s2 /\
    vars_colon_free s1 /\
    EVERY colon_free inst1.inst_outputs /\
    inst_wf inst1 /\
    inst1.inst_opcode <> PHI /\
    inst1.inst_opcode <> INVOKE /\
    ~is_terminator inst1.inst_opcode /\
    step_inst_base inst1 s1 = OK s1' ==>
    let inst2 = SND (rename_inst rs inst1) in
    let rs' = FST (rename_inst rs inst1) in
    ?s2'. step_inst_base inst2 s2 = OK s2' /\
          ssa_sim (latest_version rs') s1' s2' /\
          vars_colon_free s1'
Proof
  rpt strip_tac >> simp[LET_THM] >>
  `bound_output_count inst1.inst_opcode = LENGTH inst1.inst_outputs` by
    metis_tac[inst_wf_bound_output_count] >>
  `inst_renamed (latest_version rs) inst1 (SND (rename_inst rs inst1))` by
    metis_tac[rename_inst_produces_inst_renamed] >>
  `output_fresh (latest_version rs) inst1 (SND (rename_inst rs inst1)) s1` by
    (irule rename_inst_output_fresh >> simp[]) >>
  `vars_colon_free s1'` by metis_tac[vars_colon_free_step_inst_base] >>
  `?s2'. step_inst_base (SND (rename_inst rs inst1)) s2 = OK s2' /\
     ssa_sim (output_sigma inst1.inst_opcode inst1.inst_outputs
                (SND (rename_inst rs inst1)).inst_outputs
                (latest_version rs)) s1' s2'` by (
    Cases_on `inst1.inst_opcode = ASSIGN`
    >- metis_tac[assign_renamed_sim]
    >- metis_tac[step_inst_base_renamed_sim]
  ) >>
  qexists_tac `s2'` >> simp[] >>
  qpat_x_assum `ssa_sim (output_sigma _ _ _ _) _ _` mp_tac >>
  simp[output_sigma_latest_rename_inst]
QED

(* ===== Generalized bridge lemmas (abstract sigma) ===== *)

(* Generalized step_base bridge: preserve the all-output sigma boundary. *)
Theorem step_base_sigma_bridge_gen[local]:
  !sigma inst1 inst2 s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    vars_colon_free s1 /\
    EVERY colon_free inst1.inst_outputs /\
    inst_renamed sigma inst1 inst2 /\
    output_fresh sigma inst1 inst2 s1 /\
    inst1.inst_opcode <> PHI /\
    inst1.inst_opcode <> INVOKE /\
    ~is_terminator inst1.inst_opcode /\
    step_inst_base inst1 s1 = OK s1' ==>
    ?s2'. step_inst_base inst2 s2 = OK s2' /\
          ssa_sim (output_sigma inst1.inst_opcode
                     inst1.inst_outputs inst2.inst_outputs sigma) s1' s2' /\
          vars_colon_free s1'
Proof
  rpt strip_tac >>
  `vars_colon_free s1'` by metis_tac[vars_colon_free_step_inst_base] >>
  Cases_on `inst1.inst_opcode = ASSIGN`
  >- (
    drule_all assign_renamed_sim >> strip_tac >>
    qexists_tac `s2'` >> gvs[]
  )
  >- (
    drule_all step_inst_base_renamed_sim >> strip_tac >>
    qexists_tac `s2'` >> gvs[]
  )
QED

(* decode_invoke correspondence under inst_renamed *)
Theorem decode_invoke_renamed[local]:
  !sigma inst1 inst2 callee_name arg_ops.
    inst_renamed sigma inst1 inst2 /\
    decode_invoke inst1 = SOME (callee_name, arg_ops) ==>
    decode_invoke inst2 = SOME (callee_name, MAP (renamed_operand sigma) arg_ops)
Proof
  rpt strip_tac >> gvs[inst_renamed_def, decode_invoke_def] >>
  Cases_on `inst1.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[renamed_operand_def]
QED

(* INVOKE sigma bridge: clean-context proof for INVOKE simulation.
   INVOKE branch exposing specific sigma
   and includes vars_colon_free. *)
Theorem invoke_sigma_bridge[local]:
  !rs inst1 s1 s2 fuel ctx s1'.
    ssa_sim (latest_version rs) s1 s2 /\
    vars_colon_free s1 /\
    EVERY colon_free inst1.inst_outputs /\
    ALL_DISTINCT inst1.inst_outputs /\
    inst1.inst_opcode = INVOKE /\
    step_inst fuel ctx inst1 s1 = OK s1' ==>
    let inst2 = SND (rename_inst rs inst1) in
    let rs' = FST (rename_inst rs inst1) in
    ?s2'. step_inst fuel ctx inst2 s2 = OK s2' /\
          ssa_sim (latest_version rs') s1' s2' /\
          vars_colon_free s1'
Proof
  rpt strip_tac >> simp[LET_THM] >>
  (* Step 1: inst_renamed and basic properties *)
  `inst1.inst_opcode <> PHI` by gvs[] >>
  `inst_renamed (latest_version rs) inst1 (SND (rename_inst rs inst1))`
    by metis_tac[rename_inst_produces_inst_renamed] >>
  gvs[inst_renamed_def] >>
  `(SND (rename_inst rs inst1)).inst_opcode = INVOKE` by gvs[] >>
  (* Step 2: Decompose INVOKE on side 1 — CLEAN context, no Abbrevs *)
  gvs[Once step_inst_def, AllCaseEqs()] >>
  (* Step 3: decode_invoke for inst2 *)
  `decode_invoke (SND (rename_inst rs inst1)) =
     SOME (callee_name, MAP (renamed_operand (latest_version rs)) arg_ops)`
    by (gvs[decode_invoke_def] >>
        Cases_on `inst1.inst_operands` >> gvs[] >>
        Cases_on `h` >> gvs[renamed_operand_def]) >>
  imp_res_tac eval_operands_renamed >>
  `setup_callee callee_fn args s2 = setup_callee callee_fn args s1`
    by metis_tac[setup_callee_ssa_sim] >>
  `ssa_sim (latest_version rs)
     (merge_callee_state s1 callee_s')
     (merge_callee_state s2 callee_s')`
    by metis_tac[merge_callee_ssa_sim] >>
  `ssa_sim (latest_version rs)
     (adopt_return_fmp ret (merge_callee_state s1 callee_s'))
     (adopt_return_fmp ret (merge_callee_state s2 callee_s'))` by
    (Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def] >>
     irule ssa_sim_fmp_update >> gvs[]) >>
  imp_res_tac bind_outputs_LENGTH >>
  imp_res_tac bind_outputs_FOLDL >> gvs[] >>
  `LENGTH (SND (rename_inst rs inst1)).inst_outputs =
   LENGTH ret.iret_values` by gvs[] >>
  imp_res_tac bind_outputs_LENGTH_SOME >>
  (* Step 4: Build side 2 *)
  simp[Once step_inst_def] >>
  (* Step 5: Output properties from rename_inst *)
  qabbrev_tac `inst2 = SND (rename_inst rs inst1)` >>
  `inst1.inst_opcode <> PHI` by gvs[] >>
  `ALL_DISTINCT inst2.inst_outputs /\
   LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
   !i. i < LENGTH inst1.inst_outputs ==>
     ?ver. EL i inst2.inst_outputs =
           version_var (EL i inst1.inst_outputs) ver` by
    (simp[Abbr `inst2`] >> metis_tac[rename_inst_output_props]) >>
  (* Non-aliasing: colon_free vars can't equal version_var outputs *)
  `vars_colon_free
     (adopt_return_fmp ret (merge_callee_state s1 callee_s'))` by
    (Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, vars_colon_free_def, lookup_var_def,
         merge_callee_state_def]) >>
  `!i. i < LENGTH inst1.inst_outputs ==>
    !x. lookup_var x
          (adopt_return_fmp ret (merge_callee_state s1 callee_s')) <> NONE ==>
        x <> EL i inst1.inst_outputs ==>
        latest_version rs x <> EL i inst2.inst_outputs` by (
    rpt strip_tac >>
    `colon_free x` by gvs[vars_colon_free_def] >>
    `colon_free (EL i inst1.inst_outputs)` by gvs[EVERY_EL] >>
    `?ver. EL i inst2.inst_outputs =
           version_var (EL i inst1.inst_outputs) ver` by gvs[] >>
    metis_tac[latest_version_no_alias]) >>
  (* Step 6: ssa_sim with specific sigma via foldl_update_var_ssa_sim *)
  `ssa_sim
     (FOLDL (\s (o1,o2). (o1 =+ o2) s)
        (latest_version rs) (ZIP (inst1.inst_outputs, inst2.inst_outputs)))
     (FOLDL (\st (nm,vl). update_var nm vl st)
        (adopt_return_fmp ret (merge_callee_state s1 callee_s'))
        (ZIP (inst1.inst_outputs, ret.iret_values)))
     (FOLDL (\st (nm,vl). update_var nm vl st)
        (adopt_return_fmp ret (merge_callee_state s2 callee_s'))
        (ZIP (inst2.inst_outputs, ret.iret_values)))` by (
    irule foldl_update_var_ssa_sim >> gvs[]) >>
  (* Step 7: Bridge FOLDL sigma to latest_version rs' *)
  Cases_on `rename_outputs rs inst1.inst_outputs` >>
  qspecl_then [`inst1.inst_outputs`, `rs`, `q`, `r`] mp_tac
    rename_outputs_multi_latest >> simp[] >> strip_tac >>
  `inst2.inst_outputs = r` by (
    gvs[Abbr `inst2`, rename_inst_def, LET_THM] >>
    Cases_on `inst1.inst_opcode` >> gvs[]) >>
  `FST (rename_inst rs inst1) = q` by (
    gvs[Abbr `inst2`, rename_inst_def, LET_THM] >>
    Cases_on `inst1.inst_opcode` >> gvs[]) >>
  conj_tac
  >- (irule ssa_sim_sigma_replace >>
      qexists_tac `FOLDL (\s (o1,o2). (o1 =+ o2) s) (latest_version rs)
                     (ZIP (inst1.inst_outputs, inst2.inst_outputs))` >>
      gvs[])
  >- (irule vars_colon_free_foldl_update >>
      conj_tac >- gvs[] >>
      gvs[EVERY_EL, EL_ZIP])
QED

(* Generalized INVOKE bridge: takes abstract sigma with freshness property.
   Produces FOLDL sigma update instead of latest_version rs'. *)
Theorem invoke_sigma_bridge_gen[local]:
  !sigma inst1 inst2 s1 s2 fuel ctx s1'.
    ssa_sim sigma s1 s2 /\
    vars_colon_free s1 /\
    inst_renamed sigma inst1 inst2 /\
    EVERY colon_free inst1.inst_outputs /\
    ALL_DISTINCT inst1.inst_outputs /\
    ALL_DISTINCT inst2.inst_outputs /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!i. i < LENGTH inst1.inst_outputs ==>
         ?ver. EL i inst2.inst_outputs =
               version_var (EL i inst1.inst_outputs) ver) /\
    (!v. colon_free v ==> ?n. sigma v = version_var v n) /\
    inst1.inst_opcode = INVOKE /\
    step_inst fuel ctx inst1 s1 = OK s1' ==>
    ?s2'. step_inst fuel ctx inst2 s2 = OK s2' /\
          ssa_sim (FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma
                    (ZIP (inst1.inst_outputs, inst2.inst_outputs)))
                  s1' s2' /\
          vars_colon_free s1'
Proof
  rpt strip_tac >>
  `inst1.inst_opcode <> PHI` by gvs[] >>
  gvs[inst_renamed_def] >>
  `inst2.inst_opcode = INVOKE` by gvs[] >>
  (* Decompose INVOKE on side 1 *)
  gvs[Once step_inst_def, AllCaseEqs()] >>
  `decode_invoke inst2 =
     SOME (callee_name, MAP (renamed_operand sigma) arg_ops)`
    by (gvs[decode_invoke_def] >>
        Cases_on `inst1.inst_operands` >> gvs[] >>
        Cases_on `h` >> gvs[renamed_operand_def]) >>
  imp_res_tac eval_operands_renamed >>
  `setup_callee callee_fn args s2 = setup_callee callee_fn args s1`
    by metis_tac[setup_callee_ssa_sim] >>
  `ssa_sim sigma
     (merge_callee_state s1 callee_s')
     (merge_callee_state s2 callee_s')`
    by metis_tac[merge_callee_ssa_sim] >>
  `ssa_sim sigma
     (adopt_return_fmp ret (merge_callee_state s1 callee_s'))
     (adopt_return_fmp ret (merge_callee_state s2 callee_s'))` by
    (Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def] >>
     irule ssa_sim_fmp_update >> gvs[]) >>
  imp_res_tac bind_outputs_LENGTH >>
  imp_res_tac bind_outputs_FOLDL >> gvs[] >>
  `LENGTH inst2.inst_outputs = LENGTH ret.iret_values` by gvs[] >>
  imp_res_tac bind_outputs_LENGTH_SOME >>
  (* Build side 2 *)
  simp[Once step_inst_def] >>
  (* Non-aliasing via sigma freshness *)
  `vars_colon_free
     (adopt_return_fmp ret (merge_callee_state s1 callee_s'))` by
    (Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, vars_colon_free_def, lookup_var_def,
         merge_callee_state_def]) >>
  `!i. i < LENGTH inst1.inst_outputs ==>
    !x. lookup_var x
          (adopt_return_fmp ret (merge_callee_state s1 callee_s')) <> NONE ==>
        x <> EL i inst1.inst_outputs ==>
        sigma x <> EL i inst2.inst_outputs` by (
    rpt strip_tac >>
    `colon_free x` by gvs[vars_colon_free_def] >>
    `colon_free (EL i inst1.inst_outputs)` by gvs[EVERY_EL] >>
    `?ver. EL i inst2.inst_outputs =
           version_var (EL i inst1.inst_outputs) ver` by gvs[] >>
    metis_tac[sigma_no_alias]) >>
  (* ssa_sim with FOLDL sigma *)
  conj_tac
  >- (irule foldl_update_var_ssa_sim >> gvs[])
  >- (irule vars_colon_free_foldl_update >>
      conj_tac >- gvs[] >>
      gvs[EVERY_EL, EL_ZIP])
QED

(* For INVOKE, if step_inst returns Halt or Abort, the renamed INVOKE returns
   the same result. This holds because Halt/Abort only arise from run_function
   after all intermediate steps (decode, lookup, eval, setup) succeed, and both
   sides share the same callee state. *)
Theorem invoke_step_halt_abort[local]:
  !rs inst1 s1 s2 fuel ctx.
    ssa_sim (latest_version rs) s1 s2 /\
    EVERY colon_free inst1.inst_outputs /\
    inst1.inst_opcode = INVOKE /\
    ((?h. step_inst fuel ctx inst1 s1 = Halt h) \/
     (?a s'. step_inst fuel ctx inst1 s1 = Abort a s')) ==>
    let inst2 = SND (rename_inst rs inst1) in
    step_inst fuel ctx inst2 s2 = step_inst fuel ctx inst1 s1
Proof
  rpt strip_tac >> simp[LET_THM] >>
  `inst1.inst_opcode <> PHI` by gvs[] >>
  `inst_renamed (latest_version rs) inst1 (SND (rename_inst rs inst1))`
    by metis_tac[rename_inst_produces_inst_renamed] >>
  qabbrev_tac `inst2 = SND (rename_inst rs inst1)` >>
  `inst2.inst_opcode = INVOKE` by gvs[inst_renamed_def] >>
  (* Side 1 returned Halt/Abort => all intermediate steps succeeded.
     Expand step_inst to extract them. *)
  gvs[Once step_inst_def, AllCaseEqs()] >>
  (* Now have: decode = SOME, lookup = SOME, eval = SOME, setup = SOME,
     run_function = Halt h or Abort a s' *)
  imp_res_tac decode_invoke_renamed >>
  imp_res_tac eval_operands_renamed >>
  `setup_callee callee_fn args s2 = setup_callee callee_fn args s1`
    by metis_tac[setup_callee_ssa_sim] >>
  simp[Once step_inst_def]
QED

(* INVOKE step_inst never returns IntRet — IntRet from run_function is
   consumed by bind_outputs which produces OK or Error *)
Theorem invoke_never_intret[local]:
  !fuel ctx inst s vals s'.
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst s <> IntRet vals s'
Proof
  rpt strip_tac >> gvs[Once step_inst_def, AllCaseEqs()]
QED

(* Unified non-OK handler: if a non-terminator instruction produces a non-OK
   non-Error result on side 1, then the renamed instruction on the ssa_sim-related
   side 2 produces an ssa_result_equiv-related result.
   Covers: INVOKE Halt/Abort (step equality), non-INVOKE Abort (step_base_abort_sim).
   Impossible cases: INVOKE IntRet, non-INVOKE Halt/IntRet. *)
Theorem step_non_ok_ssa_sim[local]:
  !sigma inst1 inst2 s1 s2 fuel ctx.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    ~is_terminator inst1.inst_opcode /\
    EVERY colon_free inst1.inst_outputs /\
    inst1.inst_opcode <> PHI /\
    (!v. step_inst fuel ctx inst1 s1 <> OK v) /\
    (!e. step_inst fuel ctx inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst fuel ctx inst1 s1) (step_inst fuel ctx inst2 s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst1.inst_opcode = INVOKE`
  >- (
    (* INVOKE: after Cases_on, gvs eliminates OK/Error.
       Remaining: Halt, Abort, IntRet. All handled uniformly. *)
    Cases_on `step_inst fuel ctx inst1 s1` >> gvs[]
    (* Halt, Abort: step equality via step_inst expansion *)
    >> (
      TRY (metis_tac[invoke_never_intret]) >>  (* kills IntRet *)
      (* Halt or Abort: expand side 1, gather equalities, simplify side 2 *)
      qpat_x_assum `step_inst _ _ inst1 _ = _` mp_tac >>
      simp[Once step_inst_def, AllCaseEqs()] >> strip_tac >>
      `decode_invoke inst2 =
       SOME (callee_name, MAP (renamed_operand sigma) arg_ops)`
        by metis_tac[decode_invoke_renamed] >>
      imp_res_tac eval_operands_renamed >>
      `setup_callee callee_fn args s2 = setup_callee callee_fn args s1`
        by metis_tac[setup_callee_ssa_sim] >>
      `inst2.inst_opcode = INVOKE` by fs[inst_renamed_def] >>
      simp[Once step_inst_def, ssa_result_equiv_def, execution_equiv_UNIV])
  )
  >- (
    (* non-INVOKE: step_inst = step_inst_base, only OK/Error/Abort possible *)
    `step_inst fuel ctx inst1 s1 = step_inst_base inst1 s1`
      by simp[step_inst_non_invoke] >>
    `step_inst fuel ctx inst2 s2 = step_inst_base inst2 s2`
      by (match_mp_tac step_inst_non_invoke >> fs[inst_renamed_def]) >>
    `(?s'. step_inst_base inst1 s1 = OK s') \/
     (?e. step_inst_base inst1 s1 = Error e) \/
     (?a s'. step_inst_base inst1 s1 = Abort a s')` by
      metis_tac[step_inst_base_non_term_result] >>
    gvs[] >>
    (* Only Abort remains after OK/Error excluded *)
    imp_res_tac step_base_abort_sim >>
    gvs[ssa_result_equiv_def]
  )
QED

(* Helper: when the exec_block results are both known and ssa_result_equiv,
   and the first is non-OK, close the lockstep_body goal.
   No higher-order variables — simple first-order matching for drule_all. *)
Theorem lockstep_non_ok_close[local]:
  !fuel ctx bb bb' s1 s2 r1 r2.
    exec_block fuel ctx bb s1 = r1 /\
    exec_block fuel ctx bb' s2 = r2 /\
    ssa_result_equiv r1 r2 /\
    (!v. r1 <> OK v) ==>
    ssa_result_equiv (exec_block fuel ctx bb s1) (exec_block fuel ctx bb' s2) /\
    !v v'.
      exec_block fuel ctx bb s1 = OK v /\ exec_block fuel ctx bb' s2 = OK v' ==>
      ?sigma' rs'.
        ssa_sim sigma' v v' /\ (!x. sigma' x = latest_version rs' x) /\
        vars_colon_free v
Proof
  rpt gen_tac >> strip_tac >> gvs[]
QED

(* Bridge: given OK step on original, produce OK step on renamed + ssa_sim + colon_free.
   Factored out of lockstep_body to avoid rich-context hanging issues. *)
Theorem ok_step_sim_bridge[local]:
  !rs inst1 s1 s2 fuel ctx v.
    ssa_sim (latest_version rs) s1 s2 /\
    vars_colon_free s1 /\
    EVERY colon_free inst1.inst_outputs /\
    ALL_DISTINCT inst1.inst_outputs /\
    inst_wf inst1 /\
    inst1.inst_opcode <> PHI /\
    ~is_terminator inst1.inst_opcode /\
    step_inst fuel ctx inst1 s1 = OK v ==>
    ?s2'. step_inst fuel ctx (SND (rename_inst rs inst1)) s2 = OK s2' /\
          ssa_sim (latest_version (FST (rename_inst rs inst1))) v s2' /\
          vars_colon_free v
Proof
  rw[] >>
  Cases_on `inst1.inst_opcode = INVOKE`
  >- (
    drule_all (SIMP_RULE std_ss [GSYM AND_IMP_INTRO, LET_THM]
      invoke_sigma_bridge) >>
    strip_tac >> qexists_tac `s2'` >> gvs[]
  )
  >- (
    `step_inst_base inst1 s1 = OK v` by gvs[step_inst_non_invoke] >>
    drule_all (SIMP_RULE std_ss [GSYM AND_IMP_INTRO, LET_THM]
      step_base_sigma_bridge) >>
    strip_tac >> qexists_tac `s2'` >>
    `step_inst fuel ctx (SND (rename_inst rs inst1)) s2 =
     step_inst_base (SND (rename_inst rs inst1)) s2`
      by simp[step_inst_non_invoke, rename_inst_opcode_preserved] >>
    gvs[]
  )
QED

(* When step results are ssa_result_equiv, non-OK on side 1 implies non-OK on side 2. *)
Theorem ssa_result_equiv_non_ok[local]:
  !r1 r2. ssa_result_equiv r1 r2 /\ (!v. r1 <> OK v) ==> !v. r2 <> OK v
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[ssa_result_equiv_def]
QED

(* The case dispatch is identity on non-OK results *)
Theorem case_dispatch_non_ok[local]:
  !(r : exec_result) f.
    (!v. r <> OK v) ==>
    (case r of
       OK s2' => f s2'
     | Halt h => Halt h
     | Abort a' s' => Abort a' s'
     | IntRet vals s' => IntRet vals s'
     | Error e => Error e) = r
Proof
  Cases_on `r` >> simp[]
QED

(* When step-level results are ssa_result_equiv and r1 is non-OK,
   the case dispatches in the exec_block peel preserve ssa_result_equiv.
   Used to close Halt/Abort/IntRet branches of lockstep_body. *)
Theorem non_ok_case_close[local]:
  !(r1 : exec_result) r2 f1 f2.
    ssa_result_equiv r1 r2 /\ (!v. r1 <> OK v) ==>
    ssa_result_equiv
      (case r1 of OK s => f1 s | Halt h => Halt h | Abort a s => Abort a s
       | IntRet v s => IntRet v s | Error e => Error e)
      (case r2 of OK s => f2 s | Halt h => Halt h | Abort a s => Abort a s
       | IntRet v s => IntRet v s | Error e => Error e)
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[ssa_result_equiv_def]
QED

(* If exec_block doesn't error and peel holds, step_inst doesn't error *)
Theorem step_no_error_from_peel[local]:
  !fuel ctx bb s inst j.
    (!e. exec_block fuel ctx bb s <> Error e) /\
    exec_block fuel ctx bb s =
      (case step_inst fuel ctx inst s of
         OK s' => exec_block fuel ctx bb (s' with vs_inst_idx := SUC j)
       | Halt h => Halt h | Abort a' s' => Abort a' s'
       | IntRet vals s' => IntRet vals s' | Error e => Error e) ==>
    !e. step_inst fuel ctx inst s <> Error e
Proof
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Combined closer for non-OK non-Error branches of lockstep_body.
   Takes all hypotheses available after Cases_on step_inst in the non-OK branch.
   Proved in clean context; applied via drule_all in lockstep_body. *)
Theorem non_ok_peel_close[local]:
  !sigma fuel ctx inst1 inst2 bb bb' s1 s2 j n_phi.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    ~is_terminator inst1.inst_opcode /\
    EVERY colon_free inst1.inst_outputs /\
    inst1.inst_opcode <> PHI /\
    (!v. step_inst fuel ctx inst1 s1 <> OK v) /\
    (!e. step_inst fuel ctx inst1 s1 <> Error e) /\
    exec_block fuel ctx bb s1 =
      (case step_inst fuel ctx inst1 s1 of
         OK s1' => exec_block fuel ctx bb (s1' with vs_inst_idx := SUC j)
       | Halt h => Halt h | Abort a' s' => Abort a' s'
       | IntRet vals s' => IntRet vals s' | Error e => Error e) /\
    exec_block fuel ctx bb' s2 =
      (case step_inst fuel ctx inst2 s2 of
         OK s2' => exec_block fuel ctx bb' (s2' with vs_inst_idx := SUC (n_phi + j))
       | Halt h => Halt h | Abort a' s' => Abort a' s'
       | IntRet vals s' => IntRet vals s' | Error e => Error e) ==>
    ssa_result_equiv (exec_block fuel ctx bb s1) (exec_block fuel ctx bb' s2) /\
    !v v'. exec_block fuel ctx bb s1 = OK v /\
           exec_block fuel ctx bb' s2 = OK v' ==>
      ?sigma' rs'. ssa_sim sigma' v v' /\
                   (!x. sigma' x = latest_version rs' x) /\
                   vars_colon_free v
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_result_equiv (step_inst fuel ctx inst1 s1) (step_inst fuel ctx inst2 s2)`
    by metis_tac[step_non_ok_ssa_sim] >>
  `!v. step_inst fuel ctx inst2 s2 <> OK v`
    by metis_tac[ssa_result_equiv_non_ok] >>
  `exec_block fuel ctx bb s1 = step_inst fuel ctx inst1 s1`
    by metis_tac[case_dispatch_non_ok] >>
  `exec_block fuel ctx bb' s2 = step_inst fuel ctx inst2 s2`
    by metis_tac[case_dispatch_non_ok] >>
  gvs[]
QED

(* ML helper: given step_eq : |- step_inst ... = Constructor ...,
   derive (|- !v'. step_inst ... <> OK v', |- !e. step_inst ... <> Error e).
   Fails (raises HOL_ERR) if the constructor IS OK or Error. *)
fun mk_step_not_ok_err step_eq_thm =
  let val step_lhs = lhs (concl step_eq_thm)
      val step_rhs = rhs (concl step_eq_thm)
      val vs_ty = ``:venom_state``
      val str_ty = ``:string``
      val ok_v = mk_var("v'", vs_ty)
      val err_e = mk_var("e", str_ty)
      val ok_tm = mk_eq(step_lhs, mk_comb(``OK:venom_state->exec_result``, ok_v))
      val err_tm = mk_eq(step_lhs, mk_comb(``Error:string->exec_result``, err_e))
      val ok_rhs = mk_eq(step_rhs, mk_comb(``OK:venom_state->exec_result``, ok_v))
      val err_rhs = mk_eq(step_rhs, mk_comb(``Error:string->exec_result``, err_e))
      val distinct = venomExecSemanticsTheory.exec_result_distinct
      val not_ok = GEN_ALL (EQF_ELIM (TRANS
        (PURE_REWRITE_CONV [step_eq_thm] ok_tm)
        (SIMP_CONV bool_ss [distinct] ok_rhs)))
      val not_err = GEN_ALL (EQF_ELIM (TRANS
        (PURE_REWRITE_CONV [step_eq_thm] err_tm)
        (SIMP_CONV bool_ss [distinct] err_rhs)))
  in (not_ok, not_err) end;

(* Helper: peel both exec_blocks in lockstep.
   Proved in clean context where simp/DECIDE work.
   Used inside lockstep_body via mp_tac to avoid `by` blocks in rich context. *)
Theorem lockstep_peel[local]:
  !fuel ctx bb bb' s1 s2 inst1 inst2 j n_phi.
    s1.vs_inst_idx = j /\
    j < LENGTH bb.bb_instructions /\
    EL j bb.bb_instructions = inst1 /\
    ~is_terminator inst1.inst_opcode /\
    s2.vs_inst_idx = n_phi + j /\
    LENGTH bb'.bb_instructions = n_phi + LENGTH bb.bb_instructions /\
    EL (n_phi + j) bb'.bb_instructions = inst2 /\
    ~is_terminator inst2.inst_opcode ==>
    (exec_block fuel ctx bb s1 =
     case step_inst fuel ctx inst1 s1 of
       OK s1' => exec_block fuel ctx bb (s1' with vs_inst_idx := SUC j)
     | Halt h => Halt h | Abort a' s' => Abort a' s'
     | IntRet vals s' => IntRet vals s' | Error e => Error e) /\
    (exec_block fuel ctx bb' s2 =
     case step_inst fuel ctx inst2 s2 of
       OK s2' => exec_block fuel ctx bb' (s2' with vs_inst_idx := SUC (n_phi + j))
     | Halt h => Halt h | Abort a' s' => Abort a' s'
     | IntRet vals s' => IntRet vals s' | Error e => Error e)
Proof
  rpt strip_tac >> gvs[]
  >- (irule exec_block_peel_non_term >> simp[])
  >- (
    PURE_REWRITE_TAC [GSYM (ASSUME ``s2.vs_inst_idx = n_phi + s1.vs_inst_idx``)] >>
    irule exec_block_peel_non_term >> simp[])
QED

(* Helper: for a well-formed terminated block with inst_wf instructions,
   the rename state at the terminator position equals the rename state at the end.
   Extracted to avoid rich-context issues in lockstep_body. *)
Theorem lockstep_body_term_sigma[local]:
  !rs0 bb j.
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    j < LENGTH bb.bb_instructions /\
    is_terminator (EL j bb.bb_instructions).inst_opcode /\
    (EL j bb.bb_instructions).inst_opcode <> PHI ==>
    FST (rename_block_insts rs0 (TAKE j bb.bb_instructions)) =
    FST (rename_block_insts rs0 bb.bb_instructions)
Proof
  rpt strip_tac >>
  `j = PRE (LENGTH bb.bb_instructions)` by metis_tac[bb_well_formed_def] >>
  `inst_wf (EL j bb.bb_instructions)` by metis_tac[EVERY_EL] >>
  `(EL j bb.bb_instructions).inst_outputs = []` by
    metis_tac[inst_wf_terminator_no_outputs] >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> fs[]) >>
  `LAST bb.bb_instructions = EL j bb.bb_instructions` by simp[LAST_EL] >>
  metis_tac[rename_block_insts_terminator_end]
QED

(* Lockstep body: after PHI prefix, instructions are 1-1 between bb and bb'.
   Proved by complete induction on remaining instructions (k).

   Requires: original execution does not produce Error (well-formedness).
   Non-output opcodes have empty output lists (instruction well-formedness). *)
Theorem lockstep_terminator_close[local]:
  !fuel ctx bb bb' s1 s2 inst1 inst2 sigma sigma_end.
    exec_block fuel ctx bb s1 =
      (case step_inst_base inst1 s1 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt h => Halt h | Abort a' s' => Abort a' s'
       | IntRet vals s' => IntRet vals s' | Error e => Error e) /\
    exec_block fuel ctx bb' s2 =
      (case step_inst_base inst2 s2 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt h => Halt h | Abort a' s' => Abort a' s'
       | IntRet vals s' => IntRet vals s' | Error e => Error e) /\
    (!e. exec_block fuel ctx bb s1 <> Error e) /\
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    vars_colon_free s1 /\
    EVERY colon_free inst1.inst_outputs /\
    is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    sigma = sigma_end ==>
    ssa_result_equiv (exec_block fuel ctx bb s1) (exec_block fuel ctx bb' s2) /\
    (!v v'. exec_block fuel ctx bb s1 = OK v /\
            exec_block fuel ctx bb' s2 = OK v' ==>
      ssa_sim sigma_end v v' /\ vars_colon_free v)
Proof
  rpt gen_tac >> strip_tac >>
  `!e. step_inst_base inst1 s1 <> Error e` by
    (rpt strip_tac >> gvs[]) >>
  `ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)` by
    metis_tac[step_terminator_ssa_sim] >>
  Cases_on `step_inst_base inst1 s1`
  >- (
    `?v'. step_inst_base inst2 s2 = OK v'` by
      (Cases_on `step_inst_base inst2 s2` >> gvs[ssa_result_equiv_def]) >>
    `ssa_sim sigma v v'` by
      metis_tac[step_terminator_ok_preserves_sim] >>
    `vars_colon_free v` by
      (mp_tac (Q.SPECL [`inst1`, `s1`, `v`]
         vars_colon_free_step_inst_base) >> simp[]) >>
    imp_res_tac ssa_sim_halted >> gvs[] >>
    Cases_on `v.vs_halted` >> gvs[ssa_result_equiv_def] >>
    metis_tac[ssa_sim_implies_exec_equiv_UNIV])
  >- (gvs[] >> Cases_on `step_inst_base inst2 s2` >>
      gvs[ssa_result_equiv_def])
  >- (gvs[] >> Cases_on `step_inst_base inst2 s2` >>
      gvs[ssa_result_equiv_def])
  >- (gvs[] >> Cases_on `step_inst_base inst2 s2` >>
      gvs[ssa_result_equiv_def])
  >- metis_tac[]
QED

Theorem lockstep_body[local]:
  !k fuel ctx bb bb' s1 s2 rs0 n_phi.
    let rs_at = \j. FST (rename_block_insts rs0
                      (TAKE j bb.bb_instructions)) in
    k = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    ssa_sim (latest_version (rs_at s1.vs_inst_idx)) s1 s2 /\
    s2.vs_inst_idx = n_phi + s1.vs_inst_idx /\
    s2.vs_halted = s1.vs_halted /\
    s2.vs_current_bb = s1.vs_current_bb /\
    s2.vs_prev_bb = s1.vs_prev_bb /\
    vars_colon_free s1 /\
    EVERY (\inst. EVERY colon_free inst.inst_outputs)
          bb.bb_instructions /\
    LENGTH bb'.bb_instructions = n_phi + LENGTH bb.bb_instructions /\
    (!j. j < LENGTH bb.bb_instructions ==>
      EL (n_phi + j) bb'.bb_instructions =
        SND (rename_inst (rs_at j) (EL j bb.bb_instructions))) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      (EL j bb.bb_instructions).inst_opcode <> PHI) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
      (EL j bb.bb_instructions).inst_outputs = []) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ALL_DISTINCT (EL j bb.bb_instructions).inst_outputs) /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    (!e. exec_block fuel ctx bb s1 <> Error e) ==>
    ssa_result_equiv
      (exec_block fuel ctx bb s1) (exec_block fuel ctx bb' s2) /\
    (!v v'. exec_block fuel ctx bb s1 = OK v /\
            exec_block fuel ctx bb' s2 = OK v' ==>
      ssa_sim (latest_version
        (FST (rename_block_insts rs0 bb.bb_instructions))) v v' /\
      vars_colon_free v)
Proof
  gen_tac >> completeInduct_on `k` >>
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `rs_at = \j. FST (rename_block_insts rs0
                     (TAKE j bb.bb_instructions))` >>
  reverse (Cases_on `s1.vs_inst_idx < LENGTH bb.bb_instructions`)
  >- (
    (* ====== Base case: inst_idx out of bounds ====== *)
    `exec_block fuel ctx bb s1 = Error "block not terminated"` by (
      ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def]) >>
    metis_tac[]
  ) >>
  (* ====== Step case — setup ====== *)
  qabbrev_tac `j = s1.vs_inst_idx` >>
  qabbrev_tac `inst1 = EL j bb.bb_instructions` >>
  qabbrev_tac `inst2 = EL (n_phi + j) bb'.bb_instructions` >>
  `inst2 = SND (rename_inst (rs_at j) inst1)` by (
    simp[Abbr `inst2`, Abbr `inst1`] >>
    first_assum match_mp_tac >> simp[Abbr `j`]) >>
  `inst1.inst_opcode <> PHI` by (unabbrev_all_tac >> gvs[]) >>
  `EVERY colon_free inst1.inst_outputs` by
    (unabbrev_all_tac >> gvs[EVERY_EL]) >>
  `inst2.inst_opcode = inst1.inst_opcode` by
    metis_tac[rename_inst_opcode_preserved] >>
  `inst_renamed (latest_version (rs_at j)) inst1 inst2` by
    (unabbrev_all_tac >> metis_tac[rename_inst_produces_inst_renamed]) >>
  `~opcode_has_output inst1.inst_opcode ==>
   inst1.inst_outputs = []` by (
    simp[Abbr `inst1`] >> first_x_assum match_mp_tac >>
    simp[Abbr `j`]) >>
  `ALL_DISTINCT inst1.inst_outputs` by
    (simp[Abbr `inst1`, Abbr `j`] >> first_x_assum match_mp_tac >> simp[]) >>
  Cases_on `is_terminator inst1.inst_opcode`
  >- suspend "term"
  >> suspend "non_term"
QED

Resume lockstep_body[term]:
  (* ====== Terminator case ====== *)
  `inst1.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `exec_block fuel ctx bb s1 =
   case step_inst_base inst1 s1 of
     OK s'' => if s''.vs_halted then Halt s'' else OK s''
   | Halt h => Halt h | Abort a' s' => Abort a' s'
   | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
    irule exec_block_step_term >>
    simp[Abbr `inst1`, Abbr `j`] >> gvs[]) >>
  `exec_block fuel ctx bb' s2 =
   case step_inst_base inst2 s2 of
     OK s'' => if s''.vs_halted then Halt s'' else OK s''
   | Halt h => Halt h | Abort a' s' => Abort a' s'
   | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
    irule exec_block_step_term >>
    simp[Abbr `inst2`] >> gvs[]) >>
  `rs_at j = FST (rename_block_insts rs0 bb.bb_instructions)` by (
    simp[Abbr `rs_at`] >>
    irule lockstep_body_term_sigma >>
    simp[Abbr `inst1`, Abbr `j`]) >>
  `latest_version (FST (rename_block_insts rs0 bb.bb_instructions)) =
   latest_version (rs_at j)` by ASM_REWRITE_TAC[] >>
  mp_tac lockstep_terminator_close >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `bb'`, `s1`, `s2`,
    `inst1`, `inst2`, `latest_version (rs_at j)`,
    `latest_version (FST (rename_block_insts rs0 bb.bb_instructions))`] mp_tac) >>
  disch_then match_mp_tac >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qunabbrev_tac `rs_at` >> BETA_TAC >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ]) >> first_assum ACCEPT_TAC)
QED

Resume lockstep_body[non_term]:
  (* ====== Non-terminator case — peel both sides via lockstep_peel ====== *)
  mp_tac lockstep_peel >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `bb'`, `s1`, `s2`,
    `inst1`, `inst2`, `j`, `n_phi`] mp_tac) >>
  (impl_tac >- (
    simp[Abbr `j`, Abbr `inst1`, Abbr `inst2`] >> gvs[])) >>
  strip_tac >>
  (* === Split OK vs non-OK === *)
  reverse (Cases_on `?v. step_inst fuel ctx inst1 s1 = OK v`)
  >- ( (* ---- Non-OK: use non_ok_peel_close ---- *)
    `!e. step_inst fuel ctx inst1 s1 <> Error e` by (
      mp_tac step_no_error_from_peel >>
      disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `inst1`, `j`] mp_tac) >>
      (impl_tac >- (simp[Abbr `j`, Abbr `inst1`] >> gvs[])) >>
      simp[]) >>
    `!v. step_inst fuel ctx inst1 s1 <> OK v` by (metis_tac[]) >>
    mp_tac non_ok_peel_close >>
    disch_then (qspecl_then [`latest_version (rs_at j)`, `fuel`, `ctx`,
      `inst1`, `inst2`, `bb`, `bb'`, `s1`, `s2`, `j`, `n_phi`] mp_tac) >>
    (impl_tac >- (
      simp[Abbr `rs_at`, Abbr `inst1`, Abbr `inst2`, Abbr `j`] >>
      gvs[])) >>
    strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >>
    rpt strip_tac >>
    (* exec_block = case (non-OK) = non-OK, so OK v is impossible *)
    qpat_x_assum `exec_block fuel ctx bb s1 = _` (fn eq =>
      FULL_SIMP_TAC (srw_ss()) [eq]) >>
    Cases_on `step_inst fuel ctx inst1 s1` >> gvs[]
  ) >>
  (* ---- OK case ---- *)
  pop_assum strip_assume_tac >>
  pop_assum (fn step_eq =>
    qpat_x_assum `exec_block fuel ctx bb s1 = _`
      (fn peel =>
        assume_tac (SIMP_RULE (srw_ss()) [step_eq] peel)) >>
    assume_tac step_eq) >>
  `inst_wf inst1` by
    (simp[Abbr `inst1`] >> metis_tac[EVERY_EL]) >>
  qunabbrev_tac `rs_at` >> BETA_TAC >>
  drule_all (SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
    ok_step_sim_bridge) >>
  strip_tac >>
  qpat_x_assum `exec_block fuel ctx bb' s2 = _`
    (fn peel2 =>
      qpat_x_assum `step_inst fuel ctx _ s2 = OK s2'`
        (fn step2_eq =>
          assume_tac (SIMP_RULE (srw_ss()) [step2_eq] peel2) >>
          assume_tac step2_eq)) >>
  (* Rewrite goal with both peels *)
  qpat_x_assum `exec_block fuel ctx bb' s2 = _`
    (fn peel2 => REWRITE_TAC [peel2]) >>
  qpat_assum `exec_block fuel ctx bb s1 = _`
    (fn peel1 => REWRITE_TAC [peel1]) >>
  (* Establish ssa_sim for next index — ML-level, O(1) in context *)
  qpat_x_assum `ssa_sim _ v s2'` (fn sim =>
    qpat_x_assum `j < LENGTH bb.bb_instructions` (fn jlt =>
      qpat_x_assum `Abbrev (inst1 = _)` (fn inst1_ab =>
        let
          val inst1_eq = REWRITE_RULE [markerTheory.Abbrev_def] inst1_ab
          val step_eq = MATCH_MP rename_block_insts_step jlt
          val sim2 = REWRITE_RULE [inst1_eq] sim
          val sim3 = REWRITE_RULE [GSYM step_eq] sim2
          val sim4 = MATCH_MP ssa_sim_update_inst_idx sim3
        in
          assume_tac (Q.SPECL [`SUC j`, `SUC (n_phi + j)`] sim4) >>
          assume_tac jlt >>
          assume_tac inst1_ab
        end))) >>
  (* Establish no-Error for continuation *)
  qpat_x_assum `exec_block fuel ctx bb s1 = _`
    (fn peel =>
      qpat_x_assum `!e. exec_block fuel ctx bb s1 <> Error e`
        (fn noerr =>
          assume_tac (REWRITE_RULE [peel] noerr) >>
          assume_tac peel)) >>
  (* Invoke IH *)
  last_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC j` mp_tac) >>
  (impl_tac >- (simp[])) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `bb'`,
    `v with vs_inst_idx := SUC j`,
    `s2' with vs_inst_idx := SUC (n_phi + j)`,
    `rs0`, `n_phi`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  PURE_REWRITE_TAC [ADD_CLAUSES] >>
  (* Rewrite case dispatch *)
  qpat_x_assum `inst2 = SND _` (fn inst2_eq =>
    let val inst2_eq' = CONV_RULE (RHS_CONV (DEPTH_CONV BETA_CONV)) inst2_eq
    in
      qpat_x_assum `step_inst fuel ctx _ s2 = OK s2'` (fn step2 =>
        let val step2' = REWRITE_RULE [GSYM inst2_eq'] step2
        in
          PURE_REWRITE_TAC [step2',
            CONJUNCT1 (SPEC_ALL exec_result_case_def)] >>
          assume_tac step2'
        end)
    end) >>
  (* Derive ssa_sim field equalities *)
  qpat_x_assum `ssa_sim _ _ _` (fn sim =>
    let val ss = srw_ss()
        val h = SIMP_RULE ss [] (MATCH_MP ssa_sim_halted sim)
        val c = SIMP_RULE ss [] (MATCH_MP ssa_sim_current_bb sim)
        val p = SIMP_RULE ss [] (MATCH_MP ssa_sim_prev_bb sim)
    in assume_tac h >> assume_tac c >> assume_tac p >> assume_tac sim end) >>
  (impl_tac >- (
    PURE_REWRITE_TAC (CONJUNCTS venomStateTheory.venom_state_accfupds @
      [combinTheory.K_THM]) >>
    PURE_REWRITE_TAC [vars_colon_free_update_inst_idx] >>
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    TRY (CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ]) >>
         first_assum ACCEPT_TAC) >>
    TRY (CONV_TAC (ONCE_REWRITE_CONV [ADD_COMM]) >>
         first_assum ACCEPT_TAC) >>
    TRY DECIDE_TAC >>
    first_assum ACCEPT_TAC
  )) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  disch_then ACCEPT_TAC
QED

Finalise lockstep_body;

(* ===== Helpers for lockstep_body_gen ===== *)

(* FOLDL update at non-member key: value is unchanged *)
Theorem foldl_update_non_mem[local]:
  !pairs (f:'a -> 'b) x.
    ~MEM x (MAP FST pairs) ==>
    FOLDL (\s (k,v). (k =+ v) s) f pairs x = f x
Proof
  Induct >- simp[] >>
  rpt gen_tac >> Cases_on `h` >> simp[] >> strip_tac >>
  `FOLDL (\s (k,v). (k =+ v) s) ((q =+ r) f) pairs x =
   ((q =+ r) f) x` by (first_x_assum irule >> gvs[]) >>
  gvs[combinTheory.APPLY_UPDATE_THM]
QED

(* FOLDL update preserves version_var freshness *)
Theorem foldl_update_freshness[local]:
  !outs outs' (sigma:string -> string).
    (!x. colon_free x ==> ?n. sigma x = version_var x n) /\
    LENGTH outs = LENGTH outs' /\
    EVERY colon_free outs /\
    (!i. i < LENGTH outs ==>
         ?ver. EL i outs' = version_var (EL i outs) ver) ==>
    !x. colon_free x ==>
        ?n. FOLDL (\s (k,v). (k =+ v) s) sigma (ZIP (outs, outs')) x =
            version_var x n
Proof
  Induct >- simp[] >>
  rpt gen_tac >> Cases_on `outs'` >> simp[] >> strip_tac >>
  simp[ZIP_def, FOLDL] >>
  last_x_assum (qspecl_then [`t`, `(h =+ h') sigma`] mp_tac) >>
  impl_tac
  >- (
    rpt conj_tac
    >- (rpt strip_tac >> Cases_on `x = h` >> simp[combinTheory.APPLY_UPDATE_THM]
        >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
        >> metis_tac[])
    >- simp[]
    >- gvs[]
    >- (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
  ) >>
  metis_tac[]
QED

(* FOLDL update at member: ALL_DISTINCT keys => lookup at EL i = EL i vals *)
Theorem foldl_update_at_el[local]:
  !ks vs (f:'a -> 'b) i.
    ALL_DISTINCT ks /\ LENGTH ks = LENGTH vs /\ i < LENGTH ks ==>
    FOLDL (\s (k,v). (k =+ v) s) f (ZIP (ks, vs)) (EL i ks) = EL i vs
Proof
  Induct >- simp[] >>
  rpt gen_tac >> Cases_on `vs` >> simp[] >> strip_tac >>
  Cases_on `i` >> simp[] >>
  (* i=0: FOLDL ... ((h =+ h') f) (ZIP(ks,t)) h = h' *)
  `FOLDL (\s (k,v). (k =+ v) s) ((h =+ h') f)
     (ZIP (ks, t)) h = (h =+ h') f h` by (
    irule foldl_update_non_mem >> simp[MAP_ZIP]) >>
  simp[combinTheory.APPLY_UPDATE_THM]
QED

(* FOLDL update at member matches latest_version after rename_outputs *)
Theorem foldl_output_matches_latest[local]:
  !outs sigma rs rs' outs' x.
    ALL_DISTINCT outs /\
    rename_outputs rs outs = (rs', outs') /\
    MEM x outs ==>
    FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma (ZIP (outs, outs')) x =
    latest_version rs' x
Proof
  rpt strip_tac >>
  `LENGTH outs' = LENGTH outs` by (
    drule rename_outputs_el >> simp[]) >>
  `?i. i < LENGTH outs /\ EL i outs = x` by metis_tac[MEM_EL] >>
  `FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma (ZIP (outs, outs')) x =
   EL i outs'` by (
    `FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma (ZIP (outs, outs')) (EL i outs) =
     EL i outs'` by (irule foldl_update_at_el >> simp[]) >>
    gvs[]) >>
  `latest_version rs' x =
   FOLDL (\s (o1,o2). (o1 =+ o2) s) (latest_version rs) (ZIP (outs, outs')) x`
    by metis_tac[rename_outputs_multi_latest] >>
  `FOLDL (\s (o1,o2). (o1 =+ o2) s) (latest_version rs) (ZIP (outs, outs')) x =
   EL i outs'` by (
    `FOLDL (\s (o1,o2). (o1 =+ o2) s) (latest_version rs)
       (ZIP (outs, outs')) (EL i outs) = EL i outs'`
      by (irule foldl_update_at_el >> simp[]) >>
    gvs[]) >>
  simp[]
QED

(* FOLDL output update matches latest_version after rename_inst *)
Theorem foldl_output_latest_rename[local]:
  !sigma inst1 inst2 rs x.
    inst2 = SND (rename_inst rs inst1) /\
    inst1.inst_opcode <> PHI /\
    ALL_DISTINCT inst1.inst_outputs /\
    MEM x inst1.inst_outputs ==>
    FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma
      (ZIP (inst1.inst_outputs, inst2.inst_outputs)) x =
    latest_version (FST (rename_inst rs inst1)) x
Proof
  rpt strip_tac >>
  simp[rename_inst_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  irule foldl_output_matches_latest >> simp[] >>
  metis_tac[]
QED

(* rename_inst does not change latest_version for non-output variables *)
Theorem rename_inst_non_output_stable[local]:
  !rs inst x.
    inst.inst_opcode <> PHI /\ ~MEM x inst.inst_outputs ==>
    latest_version (FST (rename_inst rs inst)) x = latest_version rs x
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs`
  >- metis_tac[rename_inst_empty_outputs_id] >>
  Cases_on `t`
  >- (
    (* Single output *)
    qspecl_then [`rs`, `inst`] mp_tac rename_inst_single_output_evolution >>
    simp[] >> Cases_on `rename_inst rs inst` >> simp[] >>
    strip_tac >> gvs[]
  ) >>
  (* Multiple outputs (INVOKE) *)
  gvs[rename_inst_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule rename_outputs_multi_latest >> strip_tac >>
  pop_assum (qspec_then `x` mp_tac) >> simp[] >>
  strip_tac >>
  irule foldl_update_non_mem >>
  `LENGTH (h::h'::t') = LENGTH outs'` by (
    qspecl_then [`h::h'::t'`, `rs`] mp_tac rename_outputs_length >>
    gvs[]) >>
  simp[MAP_ZIP]
QED

(* Multi-step stability: latest_version unchanged from step j to end
   when x is not an output at any step >= j *)
Theorem latest_version_stable[local]:
  !rs0 insts j x.
    j <= LENGTH insts /\
    (!j'. j <= j' /\ j' < LENGTH insts ==>
          ~MEM x (EL j' insts).inst_outputs) /\
    (!j'. j' < LENGTH insts ==> (EL j' insts).inst_opcode <> PHI) ==>
    latest_version (FST (rename_block_insts rs0 (TAKE j insts))) x =
    latest_version (FST (rename_block_insts rs0 insts)) x
Proof
  rpt gen_tac >>
  Induct_on `LENGTH insts - j` >>
  rpt strip_tac
  >- (`j = LENGTH insts` by simp[] >> simp[TAKE_LENGTH_ID_rwt]) >>
  `j < LENGTH insts` by simp[] >>
  qspecl_then [`j`, `insts`, `rs0`] mp_tac rename_block_insts_step >>
  simp[] >> strip_tac >>
  qspecl_then [`FST (rename_block_insts rs0 (TAKE j insts))`,
               `EL j insts`, `x`] mp_tac rename_inst_non_output_stable >>
  impl_tac
  >- (conj_tac
      >- (first_x_assum (qspec_then `j` mp_tac) >> simp[])
      >- (first_x_assum (qspec_then `j` mp_tac) >> simp[])) >>
  strip_tac >>
  `v = LENGTH insts - SUC j` by simp[] >>
  first_x_assum (qspecl_then [`insts`, `SUC j`] mp_tac) >>
  impl_tac >- (rpt strip_tac >> gvs[]) >>
  gvs[]
QED

(* ===== Generalized lockstep body ===== *)

(* Takes abstract sigma with freshness and live-set agreement.
   Derives inst_renamed at each step from:
   (1) Live agreement: sigma = latest_version on live_set
   (2) Valid liveness: operand bases used-before-def are in live_set
   (3) Inductive tracking: output vars agree after their definition step

   Output/non-output clauses restricted to steps >= s1.vs_inst_idx
   (sufficient for caller with vs_inst_idx = 0). *)
Theorem lockstep_body_gen[local]:
  !k fuel ctx bb bb' s1 s2 rs0 n_phi sigma live_set.
    let rs_at = \j. FST (rename_block_insts rs0
                      (TAKE j bb.bb_instructions)) in
    k = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    ssa_sim sigma s1 s2 /\
    (!x. colon_free x ==> ?n. sigma x = version_var x n) /\
    (* Live agreement: sigma matches latest_version on live_set *)
    (!x. MEM x live_set ==>
         sigma x = latest_version (rs_at s1.vs_inst_idx) x) /\
    (* Valid liveness: operand bases used-before-def are in live_set *)
    (!j x. s1.vs_inst_idx <= j /\ j < LENGTH bb.bb_instructions /\
           MEM (Var x) (EL j bb.bb_instructions).inst_operands /\
           (!m. s1.vs_inst_idx <= m /\ m < j ==>
                ~MEM x (EL m bb.bb_instructions).inst_outputs) ==>
           MEM x live_set) /\
    s2.vs_inst_idx = n_phi + s1.vs_inst_idx /\
    s2.vs_halted = s1.vs_halted /\
    s2.vs_current_bb = s1.vs_current_bb /\
    s2.vs_prev_bb = s1.vs_prev_bb /\
    vars_colon_free s1 /\
    EVERY (\inst. EVERY colon_free inst.inst_outputs)
          bb.bb_instructions /\
    LENGTH bb'.bb_instructions = n_phi + LENGTH bb.bb_instructions /\
    (!j. j < LENGTH bb.bb_instructions ==>
      EL (n_phi + j) bb'.bb_instructions =
        SND (rename_inst (rs_at j) (EL j bb.bb_instructions))) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      (EL j bb.bb_instructions).inst_opcode <> PHI) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
      (EL j bb.bb_instructions).inst_outputs = []) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ALL_DISTINCT (EL j bb.bb_instructions).inst_outputs) /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    (!e. exec_block fuel ctx bb s1 <> Error e) ==>
    ssa_result_equiv
      (exec_block fuel ctx bb s1) (exec_block fuel ctx bb' s2) /\
    (!v v'. exec_block fuel ctx bb s1 = OK v /\
            exec_block fuel ctx bb' s2 = OK v' ==>
      ?sigma_exit.
        ssa_sim sigma_exit v v' /\
        (!x. colon_free x ==> ?n. sigma_exit x = version_var x n) /\
        (* Non-output vars (among processed steps) agree with sigma *)
        (!x. (!j. s1.vs_inst_idx <= j /\ j < LENGTH bb.bb_instructions ==>
                  ~MEM x (EL j bb.bb_instructions).inst_outputs) ==>
             sigma_exit x = sigma x) /\
        (* Output vars agree with latest_version at end *)
        (!x j. s1.vs_inst_idx <= j /\
               j < LENGTH bb.bb_instructions /\
               MEM x (EL j bb.bb_instructions).inst_outputs ==>
               sigma_exit x =
                 latest_version (FST (rename_block_insts rs0
                   bb.bb_instructions)) x) /\
        vars_colon_free v)
Proof
  gen_tac >> completeInduct_on `k` >>
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `rs_at = \j. FST (rename_block_insts rs0
                     (TAKE j bb.bb_instructions))` >>
  reverse (Cases_on `s1.vs_inst_idx < LENGTH bb.bb_instructions`)
  >- (
    `exec_block fuel ctx bb s1 = Error "block not terminated"` by (
      ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def]) >>
    metis_tac[]
  ) >>
  qabbrev_tac `j = s1.vs_inst_idx` >>
  qabbrev_tac `inst1 = EL j bb.bb_instructions` >>
  qabbrev_tac `inst2 = EL (n_phi + j) bb'.bb_instructions` >>
  `inst2 = SND (rename_inst (rs_at j) inst1)` by (
    simp[Abbr `inst2`, Abbr `inst1`] >>
    first_assum match_mp_tac >> simp[Abbr `j`]) >>
  `inst1.inst_opcode <> PHI` by (unabbrev_all_tac >> gvs[]) >>
  `EVERY colon_free inst1.inst_outputs` by
    (unabbrev_all_tac >> gvs[EVERY_EL]) >>
  `inst2.inst_opcode = inst1.inst_opcode` by
    metis_tac[rename_inst_opcode_preserved] >>
  (* Derive inst_renamed sigma from live agreement + valid_liveness *)
  `inst_renamed sigma inst1 inst2` by (
    qpat_x_assum `inst2 = SND _` (fn eq => REWRITE_TAC [eq]) >>
    irule inst_renamed_from_agreement >> simp[] >>
    rpt strip_tac >>
    qsuff_tac `MEM x live_set`
    >- (strip_tac >>
        `sigma x = latest_version (rs_at s1.vs_inst_idx) x` by
          metis_tac[] >>
        `rs_at s1.vs_inst_idx = rs_at j` by simp[Abbr `j`] >>
        metis_tac[])
    >> first_x_assum (qspecl_then [`s1.vs_inst_idx`, `x`] mp_tac) >>
    simp[Abbr `j`, Abbr `inst1`]) >>
  `~opcode_has_output inst1.inst_opcode ==>
   inst1.inst_outputs = []` by (
    simp[Abbr `inst1`] >> first_x_assum match_mp_tac >>
    simp[Abbr `j`]) >>
  `ALL_DISTINCT inst1.inst_outputs` by
    (simp[Abbr `inst1`, Abbr `j`] >> first_x_assum match_mp_tac >> simp[]) >>
  Cases_on `is_terminator inst1.inst_opcode`
  >- suspend "gen_term" >>
  suspend "gen_non_term"
QED

Resume lockstep_body_gen[gen_term]:
  (* ====== Terminator case ====== *)
  `inst1.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `step_inst fuel ctx inst1 s1 = step_inst_base inst1 s1`
    by gvs[step_inst_non_invoke] >>
  `step_inst fuel ctx inst2 s2 = step_inst_base inst2 s2`
    by gvs[step_inst_non_invoke] >>
  `exec_block fuel ctx bb s1 =
   case step_inst_base inst1 s1 of
     OK s'' => if s''.vs_halted then Halt s'' else OK s''
   | Halt h => Halt h | Abort a' s' => Abort a' s'
   | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
    irule exec_block_step_term >>
    simp[Abbr `inst1`, Abbr `j`] >> gvs[]) >>
  `exec_block fuel ctx bb' s2 =
   case step_inst_base inst2 s2 of
     OK s'' => if s''.vs_halted then Halt s'' else OK s''
   | Halt h => Halt h | Abort a' s' => Abort a' s'
   | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
    irule exec_block_step_term >>
    simp[Abbr `inst2`] >> gvs[]) >>
  `!e. step_inst_base inst1 s1 <> Error e` by (
    rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)`
    by metis_tac[step_terminator_ssa_sim] >>
  Cases_on `step_inst_base inst1 s1`
  >- (
    rename1 `step_inst_base inst1 s1 = OK s1'` >>
    suspend "gen_term_ok"
  )
  >- (gvs[] >> Cases_on `step_inst_base inst2 s2` >>
      gvs[ssa_result_equiv_def])
  >- (gvs[] >> Cases_on `step_inst_base inst2 s2` >>
      gvs[ssa_result_equiv_def])
  >- (gvs[] >> Cases_on `step_inst_base inst2 s2` >>
      gvs[ssa_result_equiv_def])
  >- (metis_tac[])
QED

Resume lockstep_body_gen[gen_term_ok]:
  `vars_colon_free s1'` by (
    mp_tac vars_colon_free_step_inst_base >>
    disch_then (qspecl_then [`inst1`, `s1`, `s1'`] mp_tac) >>
    simp[]) >>
  `?s2'. step_inst_base inst2 s2 = OK s2'` by (
    Cases_on `step_inst_base inst2 s2` >>
    gvs[ssa_result_equiv_def]) >>
  `ssa_sim sigma s1' s2'` by (
    irule step_terminator_ok_preserves_sim >>
    qexistsl_tac [`inst1`, `inst2`, `s1`, `s2`] >> simp[]) >>
  imp_res_tac ssa_sim_halted >>
  gvs[] >>
  Cases_on `s1'.vs_halted` >> gvs[]
  >- (simp[ssa_result_equiv_def] >>
      metis_tac[ssa_sim_implies_exec_equiv_UNIV])
  >- (
    (* sigma_exit existential — gvs already resolved ssa_result_equiv + vars_colon_free *)
    qexists_tac `sigma` >> simp[] >>
    (* Terminator is last, has no outputs *)
    `inst_wf inst1` by (
      simp[Abbr `inst1`] >> metis_tac[EVERY_EL]) >>
    `inst1.inst_outputs = []` by
      metis_tac[inst_wf_terminator_no_outputs] >>
    rpt strip_tac >>
    `j' = j` by (
      `j = PRE (LENGTH bb.bb_instructions)` by
        (unabbrev_all_tac >> metis_tac[bb_well_formed_def]) >>
      DECIDE_TAC) >>
    gvs[])
QED

Resume lockstep_body_gen[gen_non_term]:
  (* ====== Non-terminator case — peel both sides ====== *)
  mp_tac lockstep_peel >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `bb'`, `s1`, `s2`,
    `inst1`, `inst2`, `j`, `n_phi`] mp_tac) >>
  (impl_tac >- (
    simp[Abbr `j`, Abbr `inst1`, Abbr `inst2`] >> gvs[])) >>
  strip_tac >>
  (* === Split OK vs non-OK === *)
  reverse (Cases_on `?v. step_inst fuel ctx inst1 s1 = OK v`)
  >- (
    (* ---- Non-OK: use non_ok_peel_close ---- *)
    `!e. step_inst fuel ctx inst1 s1 <> Error e` by (
      mp_tac step_no_error_from_peel >>
      disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `inst1`, `j`] mp_tac) >>
      (impl_tac >- (simp[Abbr `j`, Abbr `inst1`] >> gvs[])) >>
      simp[]) >>
    `!v. step_inst fuel ctx inst1 s1 <> OK v` by metis_tac[] >>
    `ssa_result_equiv (step_inst fuel ctx inst1 s1)
                      (step_inst fuel ctx inst2 s2)` by
      metis_tac[step_non_ok_ssa_sim] >>
    `!v. step_inst fuel ctx inst2 s2 <> OK v`
      by metis_tac[ssa_result_equiv_non_ok] >>
    `exec_block fuel ctx bb s1 = step_inst fuel ctx inst1 s1`
      by metis_tac[case_dispatch_non_ok] >>
    `exec_block fuel ctx bb' s2 = step_inst fuel ctx inst2 s2`
      by metis_tac[case_dispatch_non_ok] >>
    gvs[]
  ) >>
  (* ---- OK case ---- *)
  pop_assum strip_assume_tac >>
  pop_assum (fn step_eq =>
    qpat_x_assum `exec_block fuel ctx bb s1 = _`
      (fn peel =>
        assume_tac (SIMP_RULE (srw_ss()) [step_eq] peel)) >>
    assume_tac step_eq) >>
  `inst_wf inst1` by
    (simp[Abbr `inst1`] >> metis_tac[EVERY_EL]) >>
  `bound_output_count inst1.inst_opcode <= LENGTH inst1.inst_outputs` by (
    Cases_on `inst1.inst_opcode = INVOKE`
    >- gvs[bound_output_count_def, opcode_has_output_def]
    >- (`bound_output_count inst1.inst_opcode = LENGTH inst1.inst_outputs` by
          metis_tac[inst_wf_bound_output_count] >> simp[])) >>
  (* Get output_fresh for gen bridges *)
  `output_fresh sigma inst1 inst2 s1` by (
    qpat_x_assum `inst2 = SND _` (fn eq => REWRITE_TAC [eq]) >>
    irule output_fresh_from_freshness >> simp[]) >>
  (* Get rename_inst_output_props for inst2 *)
  `ALL_DISTINCT inst2.inst_outputs /\
   LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
   !i. i < LENGTH inst1.inst_outputs ==>
     ?ver. EL i inst2.inst_outputs =
           version_var (EL i inst1.inst_outputs) ver` by (
    qpat_x_assum `inst2 = SND _` SUBST1_TAC >>
    metis_tac[rename_inst_output_props]) >>
  (* ---- Split INVOKE vs non-INVOKE ---- *)
  Cases_on `inst1.inst_opcode = INVOKE`
  >- suspend "gen_invoke"
  >- suspend "gen_non_invoke"
QED

Resume lockstep_body_gen[gen_non_invoke]:
  `step_inst_base inst1 s1 = OK v` by
    fs[step_inst_non_invoke] >>
  (* Bridge *)
  mp_tac step_base_sigma_bridge_gen >>
  disch_then (qspecl_then [`sigma`, `inst1`, `inst2`, `s1`, `s2`, `v`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  suspend "bridge_done"
QED

Resume lockstep_body_gen[bridge_done]:
  (* Rewrite step_inst to step_inst_base in all assumptions *)
  fs[step_inst_non_invoke] >>
  suspend "after_fs"
QED

Resume lockstep_body_gen[after_fs]:
  (* Goal already peeled by fs[step_inst_non_invoke] in bridge_done *)
  (* Define sigma' and establish FOLDL equivalence *)
  (* Track the semantic all-output map and expose its full ordered fold. *)
    qabbrev_tac `sigma' = output_sigma inst1.inst_opcode
                  inst1.inst_outputs inst2.inst_outputs sigma` >>
    sg `sigma' = FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma
               (ZIP (inst1.inst_outputs, inst2.inst_outputs))`
    >- suspend "foldl_equiv" >>
    qpat_assum `Abbrev (sigma' = _)` (fn ab =>
      qpat_x_assum `ssa_sim _ v s2'` (fn sim =>
        let val eq = REWRITE_RULE [markerTheory.Abbrev_def] ab
        in assume_tac (REWRITE_RULE [GSYM eq] sim) end)) >>
  (* Bridge sigma' through inst_idx update and expose its state equalities. *)
    qpat_x_assum `ssa_sim _ v s2'` (fn sim =>
      let
        val sim' = Q.SPECL [`SUC j`, `SUC (j + n_phi)`]
          (MATCH_MP ssa_sim_update_inst_idx sim)
        val ss = srw_ss()
        val h = SIMP_RULE ss [] (MATCH_MP ssa_sim_halted sim')
        val c = SIMP_RULE ss [] (MATCH_MP ssa_sim_current_bb sim')
        val p = SIMP_RULE ss [] (MATCH_MP ssa_sim_prev_bb sim')
      in
        assume_tac h >> assume_tac c >> assume_tac p >> assume_tac sim'
      end) >>
  (* Invoke IH with sigma' and live_set ++ inst1.inst_outputs *)
    last_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC j` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `bb'`,
      `v with vs_inst_idx := SUC j`,
      `s2' with vs_inst_idx := SUC (j + n_phi)`,
      `rs0`, `n_phi`, `sigma'`,
      `live_set ++ inst1.inst_outputs`] mp_tac) >>
    simp_tac std_ss [LET_THM] >>
    PURE_REWRITE_TAC [ADD_CLAUSES] >>
  (* Prove IH premises *)
    impl_tac
    >- suspend "ih_premises"
    >> suspend "ih_result"
QED

Resume lockstep_body_gen[ih_premises]:
    (PURE_REWRITE_TAC (CONJUNCTS venomStateTheory.venom_state_accfupds @
        [combinTheory.K_THM]) >>
      PURE_REWRITE_TAC [vars_colon_free_update_inst_idx] >>
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      TRY (CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ]) >>
           first_assum ACCEPT_TAC) >>
      TRY (CONV_TAC (ONCE_REWRITE_CONV [ADD_COMM]) >>
           first_assum ACCEPT_TAC) >>
      TRY DECIDE_TAC
      (* sigma' freshness *)
      >- (
        qpat_assum `sigma' = FOLDL _ _ _` (fn eq => REWRITE_TAC [eq]) >>
        rpt strip_tac >>
        irule (SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
          foldl_update_freshness) >>
        simp[]
      )
      (* Live agreement: sigma' on live_set ++ outputs at rs_at(SUC j) *)
      >- (
        rpt strip_tac >> gvs[MEM_APPEND]
        (* x in live_set *)
        >- (
          qpat_assum `sigma' = FOLDL _ _ _` (fn eq => REWRITE_TAC [eq]) >>
          `~MEM x inst1.inst_outputs \/ MEM x inst1.inst_outputs`
            by metis_tac[] >>
          gvs[]
          >- (
            `FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma
               (ZIP (inst1.inst_outputs, inst2.inst_outputs)) x =
             sigma x` by (
              irule foldl_update_non_mem >> simp[MAP_ZIP]) >>
            simp[] >>
            `sigma x = latest_version (rs_at j) x` by
              (simp[Abbr `j`] >> metis_tac[]) >>
            pop_assum SUBST1_TAC >>
            `rs_at (SUC j) = FST (rename_inst (rs_at j) inst1)` by (
              simp[Abbr `rs_at`] >> metis_tac[rename_block_insts_step]) >>
            pop_assum SUBST1_TAC >>
            irule (GSYM rename_inst_non_output_stable) >> simp[]
          )
          >- (
            (* x in both live_set and outputs *)
            `rs_at (SUC j) = FST (rename_inst (rs_at j) inst1)` by (
              simp[Abbr `rs_at`] >> metis_tac[rename_block_insts_step]) >>
            pop_assum SUBST1_TAC >>
            irule foldl_output_latest_rename >> simp[]
          )
        )
        (* x in inst1.inst_outputs *)
        >- (
          qpat_assum `sigma' = FOLDL _ _ _` (fn eq => REWRITE_TAC [eq]) >>
          `rs_at (SUC j) = FST (rename_inst (rs_at j) inst1)` by (
            simp[Abbr `rs_at`] >> metis_tac[rename_block_insts_step]) >>
          pop_assum SUBST1_TAC >>
          irule foldl_output_latest_rename >> simp[]
        )
      )
      (* Valid liveness *)
      >- suspend "valid_live"
      (* rs_at mismatch: unfold abbreviation *)
      >- gvs[Abbr `rs_at`]
    )
QED

Resume lockstep_body_gen[valid_live]:
    rpt strip_tac >> simp[MEM_APPEND] >>
    Cases_on `MEM x inst1.inst_outputs` >- simp[] >>
    DISJ1_TAC >>
    qpat_x_assum `!j' x. _ <= j' /\ _ ==> MEM x live_set`
      (qspecl_then [`j'`, `x`] mp_tac) >>
    (impl_tac >- (
      gvs[] >> rpt strip_tac >>
      Cases_on `m = j` >- gvs[Abbr `inst1`] >>
      `SUC j <= m` by simp[] >>
      first_x_assum (qspec_then `m` mp_tac) >> simp[]
    )) >> simp[]
QED

Resume lockstep_body_gen[ih_result]:
  (* Continuation: process IH result *)
    CONV_TAC (DEPTH_CONV BETA_CONV) >>
    strip_tac >> conj_tac
    >- (first_assum ACCEPT_TAC) >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`v'`, `v''`] mp_tac) >> simp[] >>
    strip_tac >>
    qexists_tac `sigma_exit` >>
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC)
    >- suspend "non_output"
    >- suspend "output"
QED

Resume lockstep_body_gen[non_output]:
    (* Non-output: sigma_exit x = sigma x *)
    rpt strip_tac >>
    (* Step 1: Prove IH antecedent for x *)
    `∀j'. SUC j ≤ j' ∧ j' < LENGTH bb.bb_instructions ⇒
      ¬MEM x (EL j' bb.bb_instructions).inst_outputs` by (
        rpt gen_tac >> strip_tac >>
        first_x_assum match_mp_tac >> simp[]) >>
    (* Step 2: Apply IH via MATCH_MP to get sigma_exit x = FOLDL... x *)
    qpat_x_assum `∀x. (∀j'. _ ⇒ ¬MEM x _) ⇒ sigma_exit x = _`
      (qspec_then `x` (fn ih =>
        first_x_assum (fn ante =>
          ASSUME_TAC (MATCH_MP ih ante)))) >>
    (* Step 3: Rewrite sigma_exit x to FOLDL... x *)
    pop_assum SUBST1_TAC >>
    (* Step 4: FOLDL... x = sigma x via foldl_update_non_mem *)
    irule foldl_update_non_mem >>
    gvs[MAP_ZIP] >>
    qpat_x_assum `∀j'. j ≤ j' ∧ _ ⇒ ¬MEM x _` (qspec_then `j` mp_tac) >>
    simp[Abbr `inst1`]
QED

Resume lockstep_body_gen[output]:
    (* Output: sigma_exit x = latest_version(rs_end) x *)
    rpt strip_tac >>
    Cases_on `∃j''. SUC j ≤ j'' ∧ j'' < LENGTH bb.bb_instructions ∧
                     MEM x (EL j'' bb.bb_instructions).inst_outputs`
    >- (gvs[] >>
        qpat_x_assum `∀x j'. _ ∧ _ ∧ MEM x _ ⇒ sigma_exit x = _`
          match_mp_tac >>
        qexists_tac `j''` >> simp[]) >>
    gvs[] >>
    (* j' = j: the only output for x is at j *)
    `j' = j` by (
      CCONTR_TAC >> `SUC j ≤ j'` by simp[] >>
      first_x_assum (qspec_then `j'` mp_tac) >> simp[]) >>
    gvs[] >>
    suspend "output_case2"
QED

Resume lockstep_body_gen[output_case2]:
    (* Step 1: IH non-output antecedent *)
    `∀j''. SUC j ≤ j'' ∧ j'' < LENGTH bb.bb_instructions ⇒
      ¬MEM x (EL j'' bb.bb_instructions).inst_outputs` by (
        rpt gen_tac >> strip_tac >>
        first_x_assum (qspec_then `j''` mp_tac) >> simp[]) >>
    (* Step 2: sigma_exit x = FOLDL... x from IH *)
    qpat_x_assum `∀x. (∀j'. _ ⇒ ¬MEM x _) ⇒ sigma_exit x = _`
      (qspec_then `x` (fn ih =>
        first_x_assum (fn ante =>
          ASSUME_TAC (MATCH_MP ih ante)))) >>
    pop_assum SUBST1_TAC >>
    (* Goal: FOLDL... x = latest_version(rs_end) x *)
    (* Step 3: FOLDL... x = latest_version(FST(rename_inst ...)) x *)
    irule EQ_TRANS >>
    qexists_tac `latest_version (FST (rename_inst (rs_at j) inst1)) x` >>
    conj_tac
    >- (irule foldl_output_latest_rename >> simp[])
    >- (
      `FST (rename_inst (rs_at j) inst1) =
       FST (rename_block_insts rs0 (TAKE (SUC j) bb.bb_instructions))` by (
        simp[Abbr `rs_at`] >> metis_tac[rename_block_insts_step]) >>
      pop_assum SUBST1_TAC >>
      irule latest_version_stable >> simp[] >>
      rpt gen_tac >> strip_tac >>
      first_x_assum (qspec_then `j'` mp_tac) >> simp[])
QED

Resume lockstep_body_gen[foldl_equiv]:
  `bound_output_count inst1.inst_opcode = LENGTH inst1.inst_outputs` by
    metis_tac[inst_wf_bound_output_count] >>
  `TAKE (bound_output_count inst1.inst_opcode) inst1.inst_outputs =
   inst1.inst_outputs` by simp[] >>
  `TAKE (bound_output_count inst1.inst_opcode) inst2.inst_outputs =
   inst2.inst_outputs` by simp[] >>
  simp[Abbr `sigma'`, output_sigma_def]
QED

Resume lockstep_body_gen[gen_invoke]:
  (* ==== INVOKE case ==== *)
  mp_tac invoke_sigma_bridge_gen >>
  disch_then (qspecl_then [`sigma`, `inst1`, `inst2`, `s1`, `s2`,
    `fuel`, `ctx`, `v`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  suspend "invoke_rest"
QED

Resume lockstep_body_gen[invoke_rest]:
  (* Step 1: simplify bb' peel using step result *)
  qpat_x_assum `step_inst fuel ctx inst2 s2 = OK s2'`
    (fn th => FULL_SIMP_TAC (srw_ss()) [th] >> assume_tac th) >>
  suspend "invoke_step1"
QED

Resume lockstep_body_gen[invoke_step1]:
  (* Abbreviate sigma' *)
  qabbrev_tac `sigma' = FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma
                (ZIP (inst1.inst_outputs, inst2.inst_outputs))` >>
  (* Bridge sigma' through inst_idx update *)
  qpat_x_assum `ssa_sim _ v s2'` (fn sim =>
    qpat_x_assum `j < LENGTH bb.bb_instructions` (fn jlt =>
      qpat_x_assum `Abbrev (inst1 = _)` (fn inst1_ab =>
        let
          val inst1_eq = REWRITE_RULE [markerTheory.Abbrev_def] inst1_ab
          val step_eq = MATCH_MP rename_block_insts_step jlt
          val sim2 = REWRITE_RULE [inst1_eq] sim
          val sim3 = REWRITE_RULE [GSYM step_eq] sim2
          val sim4 = MATCH_MP ssa_sim_update_inst_idx sim3
        in
          assume_tac (Q.SPECL [`SUC j`, `SUC (n_phi + j)`] sim4) >>
          assume_tac jlt >>
          assume_tac inst1_ab
        end))) >>
  (* ssa_sim field equalities *)
  qpat_x_assum `ssa_sim sigma' _ _` (fn sim =>
    let val ss = srw_ss()
        val h = SIMP_RULE ss [] (MATCH_MP ssa_sim_halted sim)
        val c = SIMP_RULE ss [] (MATCH_MP ssa_sim_current_bb sim)
        val p = SIMP_RULE ss [] (MATCH_MP ssa_sim_prev_bb sim)
    in assume_tac h >> assume_tac c >> assume_tac p >> assume_tac sim end) >>
  suspend "invoke_ih"
QED

Resume lockstep_body_gen[invoke_ih]:
  (* Invoke IH with sigma' and live_set' = live_set ++ inst1.inst_outputs *)
  last_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC j` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `bb'`,
    `v with vs_inst_idx := SUC j`,
    `s2' with vs_inst_idx := SUC (n_phi + j)`,
    `rs0`, `n_phi`, `sigma'`,
    `live_set ++ inst1.inst_outputs`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  PURE_REWRITE_TAC [ADD_CLAUSES] >>
  impl_tac
  >- suspend "invoke_premises"
  >>
  suspend "invoke_conclusion"
QED

Resume lockstep_body_gen[invoke_premises]:
  PURE_REWRITE_TAC (CONJUNCTS venomStateTheory.venom_state_accfupds @
    [combinTheory.K_THM]) >>
  PURE_REWRITE_TAC [vars_colon_free_update_inst_idx] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (CONV_TAC (ONCE_REWRITE_CONV [EQ_SYM_EQ]) >>
       first_assum ACCEPT_TAC) >>
  TRY (CONV_TAC (ONCE_REWRITE_CONV [ADD_COMM]) >>
       first_assum ACCEPT_TAC) >>
  TRY DECIDE_TAC
  >- suspend "inv_freshness"
  >- suspend "inv_live_agreement"
  >- suspend "inv_valid_liveness"
  >- gvs[Abbr `rs_at`]
QED

Resume lockstep_body_gen[inv_freshness]:
  simp[Abbr `sigma'`] >> rpt strip_tac >>
  irule (SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
    foldl_update_freshness) >> gvs[]
QED

Resume lockstep_body_gen[inv_live_agreement]:
  rpt strip_tac >> gvs[MEM_APPEND]
  >- (
    simp[Abbr `sigma'`] >>
    `~MEM x inst1.inst_outputs \/ MEM x inst1.inst_outputs`
      by metis_tac[] >>
    gvs[]
    >- (
      `FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma
         (ZIP (inst1.inst_outputs, inst2.inst_outputs)) x =
       sigma x` by (
        irule foldl_update_non_mem >> simp[MAP_ZIP]) >>
      simp[] >>
      `sigma x = latest_version (rs_at j) x` by
        (simp[Abbr `j`] >> metis_tac[]) >>
      pop_assum SUBST1_TAC >>
      `rs_at (SUC j) = FST (rename_inst (rs_at j) inst1)` by (
        simp[Abbr `rs_at`] >> metis_tac[rename_block_insts_step]) >>
      pop_assum SUBST1_TAC >>
      irule (GSYM rename_inst_non_output_stable) >> simp[]
    )
    >- (
      `rs_at (SUC j) = FST (rename_inst (rs_at j) inst1)` by (
        simp[Abbr `rs_at`] >> metis_tac[rename_block_insts_step]) >>
      pop_assum SUBST1_TAC >>
      irule foldl_output_latest_rename >> simp[]
    )
  )
  >- (
    simp[Abbr `sigma'`] >>
    `rs_at (SUC j) = FST (rename_inst (rs_at j) inst1)` by (
      simp[Abbr `rs_at`] >> metis_tac[rename_block_insts_step]) >>
    pop_assum SUBST1_TAC >>
    irule foldl_output_latest_rename >> simp[]
  )
QED

Resume lockstep_body_gen[inv_valid_liveness]:
  rpt strip_tac >> simp[MEM_APPEND] >>
  Cases_on `MEM x inst1.inst_outputs`
  >- simp[] >>
  DISJ1_TAC >>
  qpat_x_assum `!j' x. _ <= j' /\ _ ==> MEM x live_set`
    (qspecl_then [`j'`, `x`] mp_tac) >>
  (impl_tac >- (
    simp[] >> rpt strip_tac >>
    Cases_on `m = j` >- gvs[Abbr `inst1`] >>
    `SUC j <= m` by simp[] >>
    res_tac
  )) >> simp[]
QED

Resume lockstep_body_gen[invoke_conclusion]:
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  strip_tac >> conj_tac
  >- (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  (* Connect IH result to goal *)
  first_x_assum (qspecl_then [`v'`, `v''`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `sigma_exit` >> rpt conj_tac
  >- first_assum ACCEPT_TAC   (* ssa_sim *)
  >- first_assum ACCEPT_TAC   (* freshness *)
  >- suspend "inv_non_output"
  >- suspend "inv_output"
  >- first_assum ACCEPT_TAC   (* vars_colon_free *)
QED

Resume lockstep_body_gen[inv_non_output]:
  (* Non-output: sigma_exit x = sigma x *)
  rpt strip_tac >>
  `sigma_exit x = sigma' x` by (
    qpat_x_assum `!x. _ ==> sigma_exit x = sigma' x`
      (qspec_then `x` mp_tac) >> simp[] >>
    rpt strip_tac >>
    first_x_assum (qspec_then `j'` mp_tac) >> simp[]) >>
  simp[Abbr `sigma'`] >>
  irule foldl_update_non_mem >>
  first_x_assum (qspec_then `j` mp_tac) >>
  simp[Abbr `j`] >> gvs[MAP_ZIP]
QED

Resume lockstep_body_gen[inv_output]:
  (* Output: sigma_exit x = latest_version(rs_end) x *)
  rpt strip_tac >>
  Cases_on `?j''. SUC j <= j'' /\ j'' < LENGTH bb.bb_instructions /\
                   MEM x (EL j'' bb.bb_instructions).inst_outputs`
  >- (gvs[] >> first_x_assum match_mp_tac >> qexists_tac `j''` >> simp[]) >>
  gvs[] >>
  `j' = j` by (
    CCONTR_TAC >> `SUC j <= j'` by simp[] >>
    first_x_assum (qspec_then `j'` mp_tac) >> simp[]) >>
  gvs[] >>
  `sigma_exit x = sigma' x` by (
    qpat_x_assum `!x. _ ==> sigma_exit x = sigma' x` match_mp_tac >>
    gen_tac >> rename1 `SUC j <= k` >> strip_tac >>
    qpat_x_assum `!j''. j'' <= j \/ _` (qspec_then `k` mp_tac) >> simp[]) >>
  `sigma' x = latest_version (rs_at (SUC j)) x` by (
    simp[Abbr `sigma'`] >>
    `rs_at (SUC j) = FST (rename_inst (rs_at j) inst1)` by (
      simp[Abbr `rs_at`] >> metis_tac[rename_block_insts_step]) >>
    pop_assum SUBST1_TAC >>
    irule foldl_output_latest_rename >> simp[]) >>
  `latest_version (rs_at (SUC j)) x =
   latest_version (FST (rename_block_insts rs0 bb.bb_instructions)) x` by (
    simp[Abbr `rs_at`] >>
    irule latest_version_stable >> simp[] >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `!j''. j'' <= j \/ _` (qspec_then `j'` mp_tac) >> simp[]) >>
  simp[]
QED

Finalise lockstep_body_gen;

Theorem run_block_ssa_sim:
  !fuel ctx bb bb' sigma sigma_out s1 s2 rs_mid.
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    EVERY (\inst. EVERY colon_free inst.inst_outputs) bb.bb_instructions /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
      (EL j bb.bb_instructions).inst_outputs = []) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ALL_DISTINCT (EL j bb.bb_instructions).inst_outputs) /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    (!e. run_block fuel ctx bb s1 <> Error e) /\
    phi_args_ok bb bb' sigma sigma_out s1 s2 rs_mid /\
    (* Operand agreement: sigma_out matches latest_version rs_mid
       on all operand bases used before def *)
    (!j x. j < LENGTH bb.bb_instructions /\
           MEM (Var x) (EL j bb.bb_instructions).inst_operands /\
           (!m. m < j ==> ~MEM x (EL m bb.bb_instructions).inst_outputs) ==>
           sigma_out x = latest_version rs_mid x) ==>
    ssa_result_equiv
      (run_block fuel ctx bb s1) (run_block fuel ctx bb' s2) /\
    (!v v'. run_block fuel ctx bb s1 = OK v /\
            run_block fuel ctx bb' s2 = OK v' ==>
      ?sigma_exit.
        ssa_sim sigma_exit v v' /\
        (!x. colon_free x ==> ?n. sigma_exit x = version_var x n) /\
        (!x. (!j. j < LENGTH bb.bb_instructions ==>
                  ~MEM x (EL j bb.bb_instructions).inst_outputs) ==>
             sigma_exit x = sigma_out x) /\
        (!x j. j < LENGTH bb.bb_instructions /\
               MEM x (EL j bb.bb_instructions).inst_outputs ==>
               sigma_exit x =
                 latest_version (FST (rename_block_insts rs_mid
                   bb.bb_instructions)) x) /\
        vars_colon_free v)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[phi_args_ok_def] >>
  (* Original block body has no PHIs, so run_block is just exec_block at idx 0. *)
  `run_block fuel ctx bb s1 = exec_block fuel ctx bb s1` by (
    ONCE_REWRITE_TAC[run_block_def] >>
    `EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions` by
      simp[EVERY_EL] >>
    simp[eval_phis_no_phis, no_phis_phi_prefix_length_zero]) >>
  first_x_assum (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qabbrev_tac `is_ubd = \x:string. ?j. j < LENGTH bb.bb_instructions /\
    MEM (Var x) (EL j bb.bb_instructions).inst_operands /\
    !m. m < j ==> ~MEM x (EL m bb.bb_instructions).inst_outputs` >>
  qabbrev_tac `live_set = FILTER is_ubd
    (nub (FLAT (MAP (\inst. MAP (\op. case op of Var x => x | _ => "") inst.inst_operands)
                  bb.bb_instructions)))` >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`, `fuel`, `ctx`,
    `bb`, `bb'`, `s1`, `s2_mid`, `rs_mid`,
    `s2_mid.vs_inst_idx`, `sigma_out`, `live_set`] lockstep_body_gen) >>
  simp_tac std_ss [LET_THM] >>
  ASM_REWRITE_TAC [] >>
  REWRITE_TAC [TAKE_0, rename_block_insts_def, GSYM ADD_ASSOC] >>
  simp_tac std_ss [rename_block_insts_def]
  >> strip_tac
  (* Assumption: (P ==> Q), Goal: R, where Q = R *)
  >> first_x_assum match_mp_tac
  >> rpt conj_tac
  >> TRY (first_assum ACCEPT_TAC)
  >> TRY DECIDE_TAC
  >> TRY (imp_res_tac ssa_sim_halted >>
       imp_res_tac ssa_sim_current_bb >>
       imp_res_tac ssa_sim_prev_bb >>
       gvs[])
  (* live agreement: MEM x live_set ==> sigma_out x = latest_version rs_mid x *)
  >> TRY (rpt strip_tac >>
       qpat_x_assum `MEM _ live_set` mp_tac >>
       simp[Abbr `live_set`, MEM_FILTER, Abbr `is_ubd`] >>
       strip_tac >>
       first_x_assum (qspecl_then [`j`, `x`] mp_tac) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
       simp[] >> NO_TAC)
  (* valid liveness: remaining subgoal *)
  >> suspend "valid_liveness"
QED

Resume run_block_ssa_sim[valid_liveness]:
  rpt strip_tac
  >> simp_tac std_ss [Abbr `live_set`, Abbr `is_ubd`, MEM_FILTER]
  >> conj_tac
  >- (qexists_tac `j` >> simp[])
  >> simp[MEM_nub, MEM_FLAT, MEM_MAP, MEM_EL]
  >> qexists_tac `MAP (\op. case op of Var x => x | _ => "")
       (EL j bb.bb_instructions).inst_operands`
  >> conj_tac
  >- (qexists_tac `EL j bb.bb_instructions` >>
      simp[] >> qexists_tac `j` >> simp[])
  >> gvs[MEM_EL] >> qexists_tac `n` >> gvs[EL_MAP] >>
  Cases_on `(EL n (bb:basic_block).bb_instructions❲j❳.inst_operands)` >> gvs[]
QED

Finalise run_block_ssa_sim;

(* ssa_sim implies state_equiv UNIV when inst_idx matches *)
Theorem ssa_sim_state_equiv_UNIV[local]:
  !sigma s1 s2.
    ssa_sim sigma s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    state_equiv UNIV s1 s2
Proof
  rw[ssa_sim_def, state_equiv_def, execution_equiv_def, IN_UNIV]
QED

(* ==========================================================================
   Part 4: Core fuel induction — run_function_ssa_sim
   ========================================================================== *)

(* Liveness flow: for each CFG edge A→B, every live-in variable at B
   is either live-in at A or defined by a non-terminator instruction in A. *)
Definition valid_liveness_flow_def:
  valid_liveness_flow live_in func <=>
    !bb succ_lbl vs x.
      MEM bb func.fn_blocks /\
      MEM succ_lbl (bb_succs bb) /\
      ALOOKUP live_in succ_lbl = SOME vs /\ MEM x vs ==>
      (?vs'. ALOOKUP live_in bb.bb_label = SOME vs' /\ MEM x vs') \/
      (?inst. MEM inst bb.bb_instructions /\
              MEM x inst.inst_outputs /\ ~is_terminator inst.inst_opcode)
End

(* Every PHI output's base variable is live-in at its block. *)
Definition phi_bases_live_in_def:
  phi_bases_live_in live_in func' <=>
    !lbl bb inst base ver.
      lookup_block lbl func'.fn_blocks = SOME bb /\
      MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
      MEM (version_var base ver) inst.inst_outputs /\ colon_free base ==>
      ?vs. ALOOKUP live_in lbl = SOME vs /\ MEM base vs
End

(* Live-in variables are in FDOM at block entry. This is the loop invariant. *)
Definition live_in_scope_def:
  live_in_scope live_in s <=>
    !vs x. ALOOKUP live_in s.vs_current_bb = SOME vs /\ MEM x vs ==>
           x IN FDOM s.vs_vars
End

(* phi_bases_in_scope derived from live_in_scope + phi_bases_live_in *)
Theorem phi_bases_from_liveness[local]:
  !live_in func' s.
    live_in_scope live_in s /\
    phi_bases_live_in live_in func' ==>
    !bb inst base ver.
      lookup_block s.vs_current_bb func'.fn_blocks = SOME bb /\
      MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
      MEM (version_var base ver) inst.inst_outputs /\ colon_free base ==>
      base IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  gvs[phi_bases_live_in_def] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[live_in_scope_def]
QED

(* live_in_scope is maintained through run_block:
   If live_in vars are in scope at block entry, and the liveness flow
   property holds, then live_in vars at the successor are in scope
   at block exit. *)
Theorem live_in_scope_maintained[local]:
  !fuel ctx bb s v live_in func.
    run_block fuel ctx bb s = OK v /\
    s.vs_inst_idx = 0 /\
    MEM bb func.fn_blocks /\
    bb_well_formed bb /\
    live_in_scope live_in s /\
    bb.bb_label = s.vs_current_bb /\
    valid_liveness_flow live_in func /\
    (!j. j < LENGTH bb.bb_instructions ==>
         ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
         (EL j bb.bb_instructions).inst_outputs = []) /\
    EVERY inst_wf bb.bb_instructions /\
    MEM v.vs_current_bb (bb_succs bb) ==>
    live_in_scope live_in v
Proof
  rw[live_in_scope_def] >> rpt strip_tac >>
  (* x ∈ live_in(v.vs_current_bb) which is a successor of bb *)
  `valid_liveness_flow live_in func` by gvs[] >>
  gvs[valid_liveness_flow_def] >>
  first_x_assum (qspecl_then [`bb`, `v.vs_current_bb`, `vs`, `x`] mp_tac) >>
  impl_tac >- gvs[] >>
  strip_tac
  >- (
    (* x ∈ live_in(bb.bb_label) = live_in(s.vs_current_bb) → x ∈ FDOM s → x ∈ FDOM v *)
    `x IN FDOM s.vs_vars` by metis_tac[] >>
    imp_res_tac run_block_vars_grow >>
    gvs[SUBSET_DEF])
  >>
  (* x is output of some non-terminator inst in bb *)
  rename1 `MEM inst_def bb.bb_instructions` >>
  `?idx. idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst_def`
    by metis_tac[MEM_EL] >>
  `~is_terminator (EL idx bb.bb_instructions).inst_opcode` by gvs[] >>
  `MEM x (EL idx bb.bb_instructions).inst_outputs` by gvs[] >>
  mp_tac (Q.SPECL [
    `fuel`, `ctx`, `bb`, `s`, `v`, `idx`] run_block_non_term_outputs_fdom) >>
  simp[]
QED

(* ===== Pipeline validity definitions ===== *)

(* valid_phi_coverage: for every CFG edge A->B and every LIVE variable v,
   either:
   - B has a PHI instruction with v in its outputs, or
   - The entry sigma at B agrees with the end sigma at A for v.
   Pruned SSA only places PHIs for live variables, so the liveness guard
   is needed for correctness. *)
Definition valid_phi_coverage_def:
  valid_phi_coverage bbs1 dtree succ_map rs0 live_in <=>
    !lbl_a lbl_b bb_a bb_b rs_a_entry rs_b_entry.
      lookup_block lbl_a bbs1 = SOME bb_a /\
      ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_a =
        SOME rs_a_entry /\
      MEM lbl_b (bb_succs bb_a) /\
      lookup_block lbl_b bbs1 = SOME bb_b /\
      ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_b =
        SOME rs_b_entry ==>
      !v vs. ALOOKUP live_in lbl_b = SOME vs /\ MEM v vs /\
          latest_version rs_b_entry v <>
          latest_version
            (FST (rename_block_insts rs_a_entry bb_a.bb_instructions)) v ==>
          ?i. MEM i bb_b.bb_instructions /\
              i.inst_opcode = PHI /\ MEM v i.inst_outputs
End

(* valid_liveness_uses: operand variables used before being defined
   in the block are in live_in. This is a standard property of correct
   liveness analysis — ensures no use-before-def without liveness. *)
Definition valid_liveness_uses_def:
  valid_liveness_uses live_in func <=>
    !bb x j. MEM bb func.fn_blocks /\
             j < LENGTH bb.bb_instructions /\
             MEM (Var x) (EL j bb.bb_instructions).inst_operands /\
             (!k. k < j ==> ~MEM x (EL k bb.bb_instructions).inst_outputs) ==>
             ?vs. ALOOKUP live_in bb.bb_label = SOME vs /\ MEM x vs
End

(* PHI operand correctness: after update_succ_phis from block A,
   the PHI for variable v at successor B resolves to
   Var (latest_version rs_a_end v) when prev_bb = lbl_a. *)
Definition valid_phi_operands_def:
  valid_phi_operands bbs1 bbs2 dtree succ_map rs0 <=>
    !lbl_a lbl_b bb_a1 bb_a2 bb_b inst base ver rs_a_entry.
      lookup_block lbl_a bbs1 = SOME bb_a1 /\
      lookup_block lbl_a bbs2 = SOME bb_a2 /\
      ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_a =
        SOME rs_a_entry /\
      MEM lbl_b (bb_succs bb_a2) /\
      lookup_block lbl_b bbs2 = SOME bb_b /\
      MEM inst bb_b.bb_instructions /\
      inst.inst_opcode = PHI /\
      inst.inst_outputs = [version_var base ver] /\
      colon_free base ==>
      resolve_phi lbl_a inst.inst_operands =
        SOME (Var (latest_version
          (FST (rename_block_insts rs_a_entry bb_a1.bb_instructions))
          base))
End

(* bb_well_formed gives the non-terminator prefix condition *)
Triviality bb_wf_non_term_prefix[local]:
  !bb. bb_well_formed bb ==>
    bb.bb_instructions <> [] /\
    !i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  simp[bb_well_formed_def] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `i < LENGTH bb.bb_instructions` by DECIDE_TAC >>
  `i = PRE (LENGTH bb.bb_instructions)` by (
    first_x_assum match_mp_tac >> simp[]) >>
  DECIDE_TAC
QED

(* Wrappers for exec_block navigation theorems *)
Theorem run_block_ok_prev_bb:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v /\
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] ==>
    v.vs_prev_bb = SOME s.vs_current_bb
Proof
  metis_tac[run_block_ok_prev_bb_exact]
QED

Theorem run_block_current_bb_in_succs:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v /\
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] ==>
    MEM v.vs_current_bb (bb_succs bb)
Proof
  simp[Once run_block_def] >>
  rpt strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] mp_tac eval_phis_ok_or_error_defs >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac eval_phis_preserves_current_bb >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`,
    `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `v`]
    exec_block_current_bb_in_succs) >>
  simp[phi_prefix_length_le]
QED

(* run_block OK gives prev_bb and current_bb in succs *)
Theorem run_block_ok_navigation:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    s.vs_inst_idx = 0 ==>
    v.vs_prev_bb = SOME s.vs_current_bb /\
    MEM v.vs_current_bb (bb_succs bb)
Proof
  metis_tac[run_block_ok_prev_bb, run_block_current_bb_in_succs,
            bb_wf_non_term_prefix]
QED

(* live_in_scope is preserved across a block execution:
   if live_in_scope holds at s, and we run block bb to get OK v,
   then live_in_scope holds at v (whose current_bb is a successor of bb). *)
Theorem live_in_scope_preserved:
  !fuel ctx bb s v live_in func.
    run_block fuel ctx bb s = OK v /\
    bb_well_formed bb /\ s.vs_inst_idx = 0 /\
    MEM bb func.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    live_in_scope live_in s /\
    valid_liveness_flow live_in func /\
    EVERY inst_wf bb.bb_instructions /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
      (EL j bb.bb_instructions).inst_outputs = []) ==>
    live_in_scope live_in v
Proof
  rw[live_in_scope_def] >> rpt strip_tac >>
  `bb.bb_instructions <> []` by (gvs[bb_well_formed_def]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> spose_not_then strip_assume_tac >>
    `i = PRE (LENGTH bb.bb_instructions)` by (
      gvs[bb_well_formed_def] >> first_x_assum match_mp_tac >> simp[]) >>
    DECIDE_TAC) >>
  (* x is live-in at v.vs_current_bb, which is a successor of bb *)
  `MEM v.vs_current_bb (bb_succs bb)` by (
    irule run_block_current_bb_in_succs >> simp[] >>
    qexistsl_tac [`ctx`, `fuel`, `s`] >> simp[]) >>
  (* By valid_liveness_flow: x was live-in at bb OR defined by bb *)
  gvs[valid_liveness_flow_def] >>
  first_x_assum (qspecl_then [`bb`, `v.vs_current_bb`, `vs`, `x`] mp_tac) >>
  simp[] >> strip_tac
  (* Case 1: x was live-in at bb's label = s.vs_current_bb *)
  >- (
    `x IN FDOM s.vs_vars` by metis_tac[] >>
    `FDOM s.vs_vars SUBSET FDOM v.vs_vars` by
      metis_tac[run_block_vars_grow] >>
    metis_tac[SUBSET_DEF])
  (* Case 2: x is an output of some non-terminator instruction in bb *)
  >> (
    `?idx. idx < LENGTH bb.bb_instructions /\
           EL idx bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `v`, `idx`]
              run_block_non_term_outputs_fdom) >>
    simp[])
QED

(* phi_resolve for a successor block: given valid_phi_operands and
   the navigation facts (prev_bb, MEM in succs), derive resolve_phi
   for PHI instructions in the successor block. *)
Theorem phi_resolve_successor:
  !bb bb' bb_mid bb_cur inst base ver rs_b_entry bbs1 bbs2 dtree succ_map
   rs0 lbl_a lbl_b phis.
    valid_phi_operands bbs1 bbs2 dtree succ_map rs0 /\
    lookup_block lbl_a bbs1 = SOME bb_mid /\
    lookup_block lbl_a bbs2 = SOME bb' /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_a =
      SOME rs_b_entry /\
    bb_mid.bb_instructions = phis ++ bb.bb_instructions /\
    bb_well_formed bb /\ bb.bb_instructions <> [] /\
    MEM lbl_b (bb_succs bb) /\
    succs_preserved bbs1 bbs2 /\
    lookup_block lbl_b bbs2 = SOME bb_cur /\
    MEM inst bb_cur.bb_instructions /\
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [version_var base ver] /\
    colon_free base ==>
    resolve_phi lbl_a inst.inst_operands =
      SOME (Var (latest_version
        (FST (rename_block_insts rs_b_entry bb_mid.bb_instructions)) base))
Proof
  rpt strip_tac >>
  (* bb_succs bb' = bb_succs bb *)
  `bb_succs bb' = bb_succs bb_mid` by (
    gvs[succs_preserved_def] >>
    first_x_assum (qspecl_then [`lbl_a`, `bb'`] mp_tac) >> simp[]) >>
  `LAST bb_mid.bb_instructions = LAST bb.bb_instructions` by (
    `bb_mid.bb_instructions <> []` by (gvs[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
    metis_tac[LAST_APPEND_NOT_NIL]) >>
  `bb_succs bb_mid = bb_succs bb` by (
    `!b1 b2. LAST b1.bb_instructions = LAST b2.bb_instructions /\
       b1.bb_instructions <> [] /\ b2.bb_instructions <> [] ==>
       bb_succs b1 = bb_succs b2` by (
      rpt strip_tac >> simp[bb_succs_def] >>
      Cases_on `b1.bb_instructions` >> Cases_on `b2.bb_instructions` >> gvs[]) >>
    first_x_assum match_mp_tac >> simp[] >>
    Cases_on `bb.bb_instructions` >> gvs[]) >>
  gvs[valid_phi_operands_def] >>
  first_x_assum (qspecl_then [`lbl_a`, `lbl_b`, `bb_mid`,
    `bb'`, `bb_cur`, `inst`, `base'`, `ver`, `rs_b_entry`] mp_tac) >>
  simp[]
QED




(* ==========================================================================
   Part 5: Obligation theorems — wf_function preservation
   ========================================================================== *)

(* Helper: bb_well_formed preserved through pipeline structure *)
Triviality pipeline_preserves_bb_wf[local]:
  !bb bb' n_phi.
    bb_well_formed bb /\
    LENGTH bb'.bb_instructions = n_phi + LENGTH bb.bb_instructions /\
    (!j. j < n_phi ==>
      (EL j bb'.bb_instructions).inst_opcode = PHI) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      (EL (n_phi + j) bb'.bb_instructions).inst_opcode =
      (EL j bb.bb_instructions).inst_opcode) ==>
    bb_well_formed bb'
Proof
  rw[bb_well_formed_def]
  (* 1. non-empty *)
  >- (CCONTR_TAC >> gvs[])
  (* 2. LAST is terminator *)
  >- (
    sg `0 < LENGTH bb.bb_instructions` >-
      (Cases_on `bb.bb_instructions` >> gvs[]) >>
    sg `(LAST bb'.bb_instructions).inst_opcode =
        (LAST bb.bb_instructions).inst_opcode` >- (
      sg `bb'.bb_instructions <> []` >- (CCONTR_TAC >> gvs[]) >>
      simp[LAST_EL] >>
      first_x_assum (qspec_then `PRE (LENGTH bb.bb_instructions)` mp_tac) >>
      impl_tac >- gvs[] >>
      strip_tac >>
      sg `n_phi + PRE (LENGTH bb.bb_instructions) =
          PRE (n_phi + LENGTH bb.bb_instructions)` >- DECIDE_TAC >>
      gvs[]) >>
    gvs[])
  (* 3. terminators only at end *)
  >- (
    Cases_on `i < n_phi`
    >- (
      sg `(EL i bb'.bb_instructions).inst_opcode = PHI` >- gvs[] >>
      gvs[is_terminator_def]) >>
    sg `?k. i = n_phi + k /\ k < LENGTH bb.bb_instructions` >-
      (qexists_tac `i - n_phi` >> gvs[]) >>
    gvs[])
  (* 4. PHIs precede non-PHIs *)
  >> (
    Cases_on `j < n_phi`
    >- (sg `i < n_phi` >- gvs[] >> gvs[]) >>
    sg `?k. j = n_phi + k /\ k < LENGTH bb.bb_instructions` >-
      (qexists_tac `j - n_phi` >> gvs[]) >>
    gvs[] >>
    sg `(EL (n_phi + k) bb'.bb_instructions).inst_opcode =
         (EL k bb.bb_instructions).inst_opcode` >-
      (first_x_assum (qspec_then `k` mp_tac) >> gvs[]) >>
    gvs[] >>
    Cases_on `i < n_phi` >- gvs[] >>
    sg `?m. i = n_phi + m /\ m < k` >-
      (qexists_tac `i - n_phi` >> gvs[]) >>
    gvs[] >>
    qpat_x_assum `!i j. _ ==> (EL i _).inst_opcode = PHI`
      (qspecl_then [`m`, `k`] mp_tac) >> simp[])
QED

(* Main theorem: make_ssa_fn preserves wf_function
   (modulo fn_inst_ids_distinct — PHIs use inst_id=0) *)
Theorem make_ssa_preserves_wf_function:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func ==>
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    ALL_DISTINCT (fn_labels func') /\
    fn_has_entry func' /\
    (!bb. MEM bb func'.fn_blocks ==> bb_well_formed bb) /\
    fn_succs_closed func'
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `func' = make_ssa_fn dom_frontiers dtree dom_post_order
    pred_map succ_map live_in func` >>
  sg `fn_labels func' = fn_labels func` >-
    gvs[fn_labels_def, Abbr `func'`, make_ssa_fn_preserves_labels] >>
  rpt conj_tac
  (* 1. ALL_DISTINCT labels *)
  >- gvs[wf_function_def]
  (* 2. fn_has_entry *)
  >- (gvs[fn_has_entry_def] >> CCONTR_TAC >>
      gvs[fn_labels_def, wf_function_def, fn_has_entry_def])
  (* 3. bb_well_formed for all blocks *)
  >- (rw[] >>
    rename1 `MEM bb' func'.fn_blocks` >>
    sg `ALL_DISTINCT (MAP (\bb. bb.bb_label) func'.fn_blocks)` >-
      gvs[fn_labels_def, wf_function_def] >>
    sg `lookup_block bb'.bb_label func'.fn_blocks = SOME bb'` >-
      (irule MEM_lookup_block >> gvs[]) >>
    (* Find corresponding original block via label preservation *)
    sg `?bb. lookup_block bb'.bb_label func.fn_blocks = SOME bb` >- (
      mp_tac (Q.SPECL [`func'.fn_blocks`, `func.fn_blocks`,
                        `bb'.bb_label`, `bb'`] lookup_block_some_agree) >>
      gvs[fn_labels_def]) >>
    pop_assum strip_assume_tac >>
    sg `MEM bb func.fn_blocks` >- metis_tac[lookup_block_MEM] >>
    sg `bb.bb_label = bb'.bb_label` >- metis_tac[lookup_block_label] >>
    sg `lookup_block bb.bb_label func'.fn_blocks = SOME bb'` >- gvs[] >>
    qunabbrev_tac `func'` >>
    drule_all (SIMP_RULE std_ss [LET_THM] pipeline_block_structure) >>
    strip_tac >>
    irule pipeline_preserves_bb_wf >>
    qexists_tac `bb` >> qexists_tac `n_phi` >>
    gvs[wf_function_def])
  (* 4. fn_succs_closed — use suspend to prove separately *)
  >> suspend "fn_succs_closed"
QED

Triviality fn_succs_closed_preserved:
  !func func'.
    fn_succs_closed func /\
    succs_preserved func.fn_blocks func'.fn_blocks /\
    fn_labels func' = fn_labels func /\
    ALL_DISTINCT (fn_labels func') ==>
    fn_succs_closed func'
Proof
  rw[fn_succs_closed_def, succs_preserved_def] >>
  sg `lookup_block bb.bb_label func'.fn_blocks = SOME bb` >-
    (irule MEM_lookup_block >> gvs[fn_labels_def]) >>
  first_x_assum drule >> strip_tac >>
  sg `MEM bb0 func.fn_blocks` >- metis_tac[lookup_block_MEM] >>
  metis_tac[]
QED

Resume make_ssa_preserves_wf_function[fn_succs_closed]:
  irule fn_succs_closed_preserved >>
  conj_tac >- gvs[wf_function_def] >>
  qexists_tac `func` >> rpt conj_tac
  >- gvs[wf_function_def]
  >- gvs[]
  >> (qunabbrev_tac `func'` >>
      irule (SIMP_RULE std_ss [LET_THM] make_ssa_fn_succs_preserved) >>
      gvs[wf_function_def, fn_labels_def])
QED

Finalise make_ssa_preserves_wf_function;

(* ==========================================================================
   Part 6: Main theorem — instantiate simulation with s1 = s2 = s, sigma = I
   ========================================================================== *)

(* latest_version on init_rename_state is identity *)
Theorem latest_version_init_rename_state:
  !defs x. latest_version (init_rename_state defs) x = x
Proof
  rw[init_rename_state_def, latest_version_def, LET_THM] >>
  Cases_on `ALOOKUP (MAP (\v. (v,[0n])) (MAP FST defs)) x` >>
  gvs[version_var_def] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]
QED

(* ==========================================================================
   Part 6: Discharging phi_args_ok — PHI coverage + PHI execution bridge
   ========================================================================== *)

(* --- Helper: phi MAP preserves non-PHI instructions --- *)
Theorem phi_map_non_phi_el[local]:
  !insts rs lbl j.
    j < LENGTH insts /\
    (EL j insts).inst_opcode <> PHI ==>
    EL j (MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else inst with inst_operands :=
                        update_phi_for_pred rs lbl inst.inst_operands)
              insts) = EL j insts
Proof
  rw[EL_MAP]
QED

(* --- Helper: update_succ_phis cons unfolding --- *)
Theorem update_succ_phis_cons[local]:
  !rs lbl bbs h t.
    update_succ_phis rs lbl bbs (h::t) =
    update_succ_phis rs lbl
      (case lookup_block h bbs of
         NONE => bbs
       | SOME sbb =>
           replace_block h
             (sbb with bb_instructions :=
               MAP (\inst. if inst.inst_opcode <> PHI then inst
                           else inst with inst_operands :=
                             update_phi_for_pred rs lbl inst.inst_operands)
               sbb.bb_instructions) bbs)
      t
Proof
  rw[update_succ_phis_def, FOLDL, LET_THM]
QED

(* --- Helper: update_succ_phis preserves non-PHI instructions --- *)

(* --- non_phi_refines: abstraction for "same length, non-PHI elements equal" --- *)
Definition non_phi_refines_def:
  non_phi_refines bb bb' <=>
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    !j. j < LENGTH bb.bb_instructions /\
        (EL j bb.bb_instructions).inst_opcode <> PHI ==>
        EL j bb'.bb_instructions = EL j bb.bb_instructions
End

(* phi_refines: non_phi_refines + output preservation at ALL positions *)
Definition phi_refines_def:
  phi_refines bb bb' <=>
    non_phi_refines bb bb' /\
    !j. j < LENGTH bb.bb_instructions ==>
        (EL j bb'.bb_instructions).inst_outputs =
        (EL j bb.bb_instructions).inst_outputs
End

Theorem phi_refines_refl[local]:
  !bb. phi_refines bb bb
Proof
  rw[phi_refines_def, non_phi_refines_def]
QED

Theorem phi_refines_trans[local]:
  !a b c. phi_refines a b /\ phi_refines b c ==> phi_refines a c
Proof
  rw[phi_refines_def, non_phi_refines_def]
QED

Theorem phi_refines_implies_non_phi_refines[local]:
  !bb bb'. phi_refines bb bb' ==> non_phi_refines bb bb'
Proof
  simp[phi_refines_def]
QED

Theorem non_phi_refines_refl[local]:
  !bb. non_phi_refines bb bb
Proof
  rw[non_phi_refines_def]
QED

Theorem non_phi_refines_trans[local]:
  !a b c. non_phi_refines a b /\ non_phi_refines b c ==> non_phi_refines a c
Proof
  simp[non_phi_refines_def] >> rpt strip_tac >>
  `EL j b.bb_instructions = EL j a.bb_instructions` by res_tac >>
  `(EL j b.bb_instructions).inst_opcode <> PHI` by metis_tac[] >>
  `j < LENGTH b.bb_instructions` by metis_tac[] >>
  res_tac
QED

(* non_phi_refines only depends on bb_instructions, not wrapper fields *)
Theorem non_phi_refines_wrapper[local]:
  non_phi_refines (bb1 with bb_instructions := X)
                  (bb2 with bb_instructions := Y) <=>
  non_phi_refines (bb1 with bb_instructions := X)
                  (bb1 with bb_instructions := Y)
Proof
  simp[non_phi_refines_def]
QED

(* update_succ_phis preserves inst_outputs at every position
   and non-PHI instructions entirely.
   One-step version used as the induction step. *)
Triviality update_succ_phis_one_step_outputs[local]:
  !rs lbl bbs h lbl' bb.
    lookup_block lbl' bbs = SOME bb ==>
    ?bb1. lookup_block lbl'
            (case lookup_block h bbs of
               NONE => bbs
             | SOME sbb => replace_block h
                 (sbb with bb_instructions :=
                   MAP (\inst. if inst.inst_opcode <> PHI then inst
                               else inst with inst_operands :=
                                 update_phi_for_pred rs lbl inst.inst_operands)
                   sbb.bb_instructions) bbs) = SOME bb1 /\
          LENGTH bb1.bb_instructions = LENGTH bb.bb_instructions /\
          (!j. j < LENGTH bb.bb_instructions ==>
               (EL j bb1.bb_instructions).inst_outputs =
               (EL j bb.bb_instructions).inst_outputs) /\
          (!j. j < LENGTH bb.bb_instructions /\
               (EL j bb.bb_instructions).inst_opcode <> PHI ==>
               EL j bb1.bb_instructions = EL j bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block h bbs` >- simp[] >>
  simp[] >>
  rename1 `lookup_block h bbs = SOME sbb` >>
  `sbb.bb_label = h` by metis_tac[lookup_block_label] >>
  qabbrev_tac `new_bb = sbb with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else inst with inst_operands :=
                  update_phi_for_pred rs lbl inst.inst_operands)
    sbb.bb_instructions` >>
  `new_bb.bb_label = h` by simp[Abbr `new_bb`] >>
  Cases_on `lbl' = h`
  >- (
    gvs[] >>
    `lookup_block bb.bb_label (replace_block bb.bb_label new_bb bbs) = SOME new_bb`
      by metis_tac[lookup_block_replace_eq] >>
    qexists_tac `new_bb` >> simp[Abbr `new_bb`, EL_MAP] >>
    rpt strip_tac >>
    Cases_on `(EL j bb.bb_instructions).inst_opcode = PHI` >> simp[])
  >>
  `lookup_block lbl' (replace_block h new_bb bbs) = lookup_block lbl' bbs`
    by metis_tac[lookup_block_replace_neq] >>
  qexists_tac `bb` >> simp[]
QED

Theorem update_succ_phis_preserves_outputs:
  !succs rs lbl bbs lbl' bb.
    lookup_block lbl' bbs = SOME bb ==>
    ?bb'. lookup_block lbl' (update_succ_phis rs lbl bbs succs) = SOME bb' /\
          LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
          (!j. j < LENGTH bb.bb_instructions ==>
               (EL j bb'.bb_instructions).inst_outputs =
               (EL j bb.bb_instructions).inst_outputs) /\
          (!j. j < LENGTH bb.bb_instructions /\
               (EL j bb.bb_instructions).inst_opcode <> PHI ==>
               EL j bb'.bb_instructions = EL j bb.bb_instructions)
Proof
  Induct_on `succs` >| [
    simp[update_succ_phis_def, FOLDL],
    ALL_TAC] >>
  rpt gen_tac >> strip_tac >>
  simp[update_succ_phis_cons] >>
  drule update_succ_phis_one_step_outputs >>
  disch_then (qspecl_then [`rs`, `lbl`, `h`] strip_assume_tac) >>
  rename1 `lookup_block lbl' _ = SOME bb1` >>
  first_x_assum drule >>
  disch_then (qspecl_then [`rs`, `lbl`] strip_assume_tac) >>
  qexists_tac `bb'` >> simp[]
QED

(* update_succ_phis preserves block existence (iff) *)
Triviality update_succ_phis_lookup_iff:
  !rs lbl bbs succs l.
    ((?b. lookup_block l (update_succ_phis rs lbl bbs succs) = SOME b) <=>
     (?b. lookup_block l bbs = SOME b))
Proof
  rpt gen_tac >> eq_tac >> strip_tac
  >- metis_tac[lookup_block_some_agree,
               GSYM update_succ_phis_preserves_labels]
  >>
  metis_tac[update_succ_phis_preserves_outputs]
QED

(* --- DNode case helper for rename_preserves_other --- *)
Theorem rename_blocks_DNode_phi_refines[local]:
  !children.
    (!ctrs stacks bbs succ_map lbl bb bb'.
       lookup_block lbl bbs = SOME bb /\
       ~MEM lbl (FLAT (MAP dom_tree_labels children)) /\
       lookup_block lbl (SND (rename_children ctrs stacks bbs succ_map children)) = SOME bb' ==>
       phi_refines bb bb') ==>
    !s rs bbs succ_map lbl bb bb'.
      lookup_block lbl bbs = SOME bb /\
      ~MEM lbl (dom_tree_labels (DNode s children)) /\
      lookup_block lbl (SND (rename_blocks rs bbs succ_map (DNode s children))) = SOME bb' ==>
      phi_refines bb bb'
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[dom_tree_labels_def] >>
  qpat_x_assum `lookup_block _ (SND (rename_blocks _ _ _ _)) = _` mp_tac >>
  simp[Once rename_blocks_def] >>
  Cases_on `lookup_block s bbs`
  >- simp[phi_refines_refl]
  >> simp[LET_THM] >>
  pairarg_tac >> simp[] >>
  qabbrev_tac `bb1 = x with bb_instructions := insts'` >>
  qabbrev_tac `bbs1 = replace_block s bb1 bbs` >>
  qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss` >>
  strip_tac >>
  `lookup_block lbl bbs1 = SOME bb` by (
    simp[Abbr `bbs1`] >>
    `bb1.bb_label = s` by (
      simp[Abbr `bb1`] >> metis_tac[lookup_block_label]) >>
    metis_tac[lookup_block_replace_neq]) >>
  drule update_succ_phis_preserves_outputs >>
  disch_then (qspecl_then [`succs`, `rs1`, `s`] strip_assume_tac) >>
  rename1 `lookup_block lbl (update_succ_phis _ _ _ _) = SOME bb_mid` >>
  `phi_refines bb bb_mid` by simp[phi_refines_def, non_phi_refines_def] >>
  first_x_assum (qspecl_then [`FST rs1`, `SND rs1`,
                               `update_succ_phis rs1 s bbs1 succs`,
                               `succ_map`, `lbl`, `bb_mid`, `bb'`] mp_tac) >>
  simp[] >> strip_tac >>
  irule phi_refines_trans >> metis_tac[]
QED

(* --- cons case helper for rename_preserves_other --- *)
Theorem rename_children_cons_phi_refines[local]:
  !dtree children.
    (!rs bbs succ_map lbl bb bb'.
       lookup_block lbl bbs = SOME bb /\
       ~MEM lbl (dom_tree_labels dtree) /\
       lookup_block lbl (SND (rename_blocks rs bbs succ_map dtree)) = SOME bb' ==>
       phi_refines bb bb') /\
    (!ctrs stacks bbs succ_map lbl bb bb'.
       lookup_block lbl bbs = SOME bb /\
       ~MEM lbl (FLAT (MAP dom_tree_labels children)) /\
       lookup_block lbl (SND (rename_children ctrs stacks bbs succ_map children)) = SOME bb' ==>
       phi_refines bb bb') ==>
    !ctrs stacks bbs succ_map lbl bb bb'.
      lookup_block lbl bbs = SOME bb /\
      ~MEM lbl (FLAT (MAP dom_tree_labels (dtree::children))) /\
      lookup_block lbl (SND (rename_children ctrs stacks bbs succ_map (dtree::children))) = SOME bb' ==>
      phi_refines bb bb'
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[MAP, FLAT] >>
  qpat_x_assum `lookup_block _ (SND (rename_children _ _ _ _ (_ :: _))) = _` mp_tac >>
  simp[Once rename_blocks_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  strip_tac >>
  `bbs' = SND (rename_blocks (ctrs,stacks) bbs succ_map dtree)` by
    (Cases_on `rename_blocks (ctrs,stacks) bbs succ_map dtree` >> gvs[]) >>
  `?bb_mid. lookup_block lbl bbs' = SOME bb_mid` by
    metis_tac[lookup_block_some_agree,
              rename_blocks_children_preserves_labels] >>
  `phi_refines bb bb_mid` by (
    first_x_assum
      (qspecl_then [`(ctrs,stacks)`, `bbs`, `succ_map`, `lbl`, `bb`, `bb_mid`]
         mp_tac) >>
    rw[]) >>
  `phi_refines bb_mid bb'` by (
    first_x_assum
      (qspecl_then [`ctrs'`, `stacks`, `bbs'`, `succ_map`, `lbl`, `bb_mid`, `bb'`]
         mp_tac) >>
    rw[]) >>
  irule phi_refines_trans >> metis_tac[]
QED

(* --- rename_blocks/children preserve phi_refines for blocks NOT in the tree --- *)
Theorem rename_preserves_other_phi_refines[local]:
  (!dtree rs bbs succ_map lbl bb bb'.
    lookup_block lbl bbs = SOME bb /\
    ~MEM lbl (dom_tree_labels dtree) /\
    lookup_block lbl (SND (rename_blocks rs bbs succ_map dtree)) = SOME bb' ==>
    phi_refines bb bb') /\
  (!children ctrs stacks bbs succ_map lbl bb bb'.
    lookup_block lbl bbs = SOME bb /\
    ~MEM lbl (FLAT (MAP dom_tree_labels children)) /\
    lookup_block lbl (SND (rename_children ctrs stacks bbs succ_map children)) = SOME bb' ==>
    phi_refines bb bb')
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      irule rename_blocks_DNode_phi_refines >> metis_tac[])
  >- (simp[rename_blocks_def] >> rpt strip_tac >> gvs[phi_refines_refl])
  >> (rpt strip_tac >>
      irule rename_children_cons_phi_refines >>
      qexistsl_tac [`bbs`, `children`, `ctrs`, `dtree`, `lbl`,
                     `stacks`, `succ_map`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
QED

(* For the ROOT label of a DNode, the final block has phi_refines
   relative to the immediately renamed version. *)
Theorem rename_blocks_root_refines[local]:
  !rs bbs succ_map s children bb_orig.
    lookup_block s bbs = SOME bb_orig /\
    ALL_DISTINCT (dom_tree_labels (DNode s children)) ==>
    let (rs1, insts') = rename_block_insts rs bb_orig.bb_instructions in
    let bb1 = bb_orig with bb_instructions := insts' in
    ?bb'. lookup_block s (SND (rename_blocks rs bbs succ_map (DNode s children))) = SOME bb' /\
          phi_refines bb1 bb'
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  pairarg_tac >> simp[] >>
  simp[Once rename_blocks_def] >>
  simp[LET_THM] >>
  qabbrev_tac `bb1 = bb_orig with bb_instructions := insts'` >>
  qabbrev_tac `bbs1 = replace_block s bb1 bbs` >>
  qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss` >>
  `bb1.bb_label = s` by (simp[Abbr `bb1`] >> metis_tac[lookup_block_label]) >>
  `lookup_block s bbs1 = SOME bb1` by
    (simp[Abbr `bbs1`] >> metis_tac[lookup_block_replace_eq]) >>
  drule update_succ_phis_preserves_outputs >>
  disch_then (qspecl_then [`succs`, `rs1`, `s`] strip_assume_tac) >>
  rename1 `lookup_block s (update_succ_phis _ _ _ _) = SOME bb2` >>
  `phi_refines bb1 bb2` by simp[phi_refines_def, non_phi_refines_def] >>
  `~MEM s (FLAT (MAP dom_tree_labels children))` by (
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    simp[Once dom_tree_labels_def, ETA_THM]) >>
  `?bb'. lookup_block s (SND (rename_children (FST rs1) (SND rs1)
    (update_succ_phis rs1 s bbs1 succs) succ_map children)) = SOME bb'` by (
    mp_tac (Q.SPECL [`update_succ_phis rs1 s bbs1 succs`,
      `SND (rename_children (FST rs1) (SND rs1)
        (update_succ_phis rs1 s bbs1 succs) succ_map children)`,
      `s`, `bb2`] lookup_block_some_agree) >>
    simp[CONJUNCT2 rename_blocks_children_preserves_labels]) >>
  qexists_tac `bb'` >> simp[] >>
  irule phi_refines_trans >>
  qexists_tac `bb2` >> conj_tac >- first_assum ACCEPT_TAC >>
  mp_tac (CONJUNCT2 rename_preserves_other_phi_refines) >>
  disch_then (qspecl_then [`children`, `FST rs1`, `SND rs1`,
    `update_succ_phis rs1 s bbs1 succs`, `succ_map`, `s`, `bb2`, `bb'`]
    mp_tac) >>
  simp[]
QED

(* FST of rename_inst depends only on inst_outputs *)
Triviality rename_inst_fst:
  !rs inst. FST (rename_inst rs inst) = FST (rename_outputs rs inst.inst_outputs)
Proof
  rw[rename_inst_def] >> Cases_on `inst.inst_opcode = PHI` >> simp[LET_THM] >>
  pairarg_tac >> simp[]
QED

(* rename_block_insts FST depends only on outputs *)
Theorem rename_block_insts_fst_outputs_only:
  !insts1 rs insts2.
    LENGTH insts1 = LENGTH insts2 /\
    (!j. j < LENGTH insts1 ==>
         (EL j insts1).inst_outputs = (EL j insts2).inst_outputs) ==>
    FST (rename_block_insts rs insts1) = FST (rename_block_insts rs insts2)
Proof
  Induct >> Cases_on `insts2` >> simp[rename_block_insts_def, LET_THM] >>
  rpt strip_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `h.inst_outputs = h'.inst_outputs` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `FST (rename_inst rs h) = FST (rename_inst rs h')` by simp[rename_inst_fst] >>
  gvs[] >>
  first_x_assum (qspecl_then [`rs'`, `t`] mp_tac) >>
  (impl_tac >- (
    simp[] >> rpt strip_tac >>
    first_x_assum (qspec_then `SUC j` mp_tac) >> simp[])) >>
  gvs[]
QED

(* Composing head + tail into cons-level non_phi_refines *)
Triviality non_phi_refines_cons:
  !inst1 inst2 insts1 insts2 bb.
    non_phi_refines (bb with bb_instructions := insts1)
                    (bb with bb_instructions := insts2) /\
    (inst1.inst_opcode <> PHI ==> inst1 = inst2) ==>
    non_phi_refines (bb with bb_instructions := inst1 :: insts1)
                    (bb with bb_instructions := inst2 :: insts2)
Proof
  simp[non_phi_refines_def] >> rpt strip_tac >>
  Cases_on `j` >> gvs[]
QED

(* If two instruction lists differ only at PHI positions (same LENGTH,
   same outputs, non-PHI instructions identical), then rename_block_insts
   produces non_phi_refines results. This follows because FST evolves
   identically (same outputs) and non-PHI instructions are the same. *)
Triviality rename_block_insts_non_phi_refines:
  !insts1 insts2 rs bb_orig.
    LENGTH insts1 = LENGTH insts2 /\
    (!j. j < LENGTH insts1 ==>
         (EL j insts1).inst_outputs = (EL j insts2).inst_outputs) /\
    (!j. j < LENGTH insts1 /\
         (EL j insts1).inst_opcode <> PHI ==>
         EL j insts1 = EL j insts2) ==>
    non_phi_refines
      (bb_orig with bb_instructions :=
         SND (rename_block_insts rs insts1))
      (bb_orig with bb_instructions :=
         SND (rename_block_insts rs insts2))
Proof
  Induct >> rpt gen_tac >- simp[rename_block_insts_def, non_phi_refines_def] >>
  Cases_on `insts2` >- simp[] >>
  simp[] >> strip_tac >>
  ONCE_REWRITE_TAC[rename_block_insts_def] >>
  simp_tac std_ss [LET_THM, pairTheory.UNCURRY] >>
  irule non_phi_refines_cons >>
  conj_tac
  >- (
    (* Goal 1: opcode <> PHI ==> same instruction *)
    strip_tac >>
    sg `h.inst_opcode <> PHI`
    >- metis_tac[rename_inst_opcode_preserved] >>
    sg `h = h'`
    >- (qpat_x_assum `!j. j < SUC _ /\ _ ==> _ = _` (qspec_then `0` mp_tac) >>
        simp[]) >>
    simp[])
  >- (
    (* Goal 2: non_phi_refines for tails *)
    sg `h.inst_outputs = h'.inst_outputs`
    >- (qpat_x_assum `!j. j < SUC _ ==> _.inst_outputs = _`
          (qspec_then `0` mp_tac) >> simp[]) >>
    sg `FST (rename_inst rs h) = FST (rename_inst rs h')`
    >- simp[rename_inst_fst] >>
    pop_assum (SUBST1_TAC o SYM) >>
    first_x_assum irule >>
    rpt conj_tac
    >- (rpt strip_tac >>
        qpat_x_assum `!j. j < SUC _ /\ _ ==> _ = _`
          (qspec_then `SUC j` mp_tac) >> simp[])
    >- (rpt strip_tac >>
        qpat_x_assum `!j. j < SUC _ ==> _.inst_outputs = _`
          (qspec_then `SUC j` mp_tac) >> simp[])
    >> simp[])
QED


(* rename_inst output only depends on rename state and inst_outputs *)
Triviality rename_inst_outputs[local]:
  !rs inst. (SND (rename_inst rs inst)).inst_outputs =
            SND (rename_outputs rs inst.inst_outputs)
Proof
  rw[rename_inst_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  CASE_TAC >> simp[] >>
  pairarg_tac >> gvs[]
QED

(* phi_refines version: same LENGTH, same outputs, same non-PHI ==>
   phi_refines on renamed lists *)
Triviality rename_block_insts_phi_refines:
  !insts1 insts2 rs bb1 bb2.
    LENGTH insts1 = LENGTH insts2 /\
    (!j. j < LENGTH insts1 ==>
         (EL j insts1).inst_outputs = (EL j insts2).inst_outputs) /\
    (!j. j < LENGTH insts1 /\
         (EL j insts1).inst_opcode <> PHI ==>
         EL j insts1 = EL j insts2) ==>
    phi_refines
      (bb1 with bb_instructions :=
         SND (rename_block_insts rs insts1))
      (bb2 with bb_instructions :=
         SND (rename_block_insts rs insts2))
Proof
  rpt strip_tac >>
  simp[phi_refines_def] >> conj_tac
  >- (ONCE_REWRITE_TAC[non_phi_refines_wrapper] >>
      irule rename_block_insts_non_phi_refines >> simp[])
  >> (simp[rename_block_insts_length] >> rpt strip_tac >>
      simp[rename_block_insts_el, rename_inst_outputs] >>
      `FST (rename_block_insts rs (TAKE j insts1)) =
       FST (rename_block_insts rs (TAKE j insts2))` by (
        irule rename_block_insts_fst_outputs_only >>
        simp[LENGTH_TAKE] >> rpt strip_tac >>
        simp[EL_TAKE] >> metis_tac[]) >>
      gvs[])
QED

(* Helper: phi_refines bb1 bb2 ==> phi_refines (renamed bb1) (renamed bb2) *)
Triviality phi_refines_rename_bridge:
  !bb1 bb2 rs.
    phi_refines bb1 bb2 ==>
    phi_refines
      (bb1 with bb_instructions := SND (rename_block_insts rs bb1.bb_instructions))
      (bb2 with bb_instructions := SND (rename_block_insts rs bb2.bb_instructions))
Proof
  rpt strip_tac >>
  irule rename_block_insts_phi_refines >>
  fs[phi_refines_def, non_phi_refines_def]
QED


(* ===== bbs_outputs_agree: Two block lists agree on inst_outputs ===== *)

(* Two block lists "agree on outputs" at a set of labels:
   same-length instruction lists with identical inst_outputs at each position. *)
Definition bbs_outputs_agree_def:
  bbs_outputs_agree labels bbs1 bbs2 <=>
    (!l. MEM l labels ==>
         ((?b. lookup_block l bbs1 = SOME b) <=>
          (?b. lookup_block l bbs2 = SOME b))) /\
    (!l b1 b2. MEM l labels /\
               lookup_block l bbs1 = SOME b1 /\ lookup_block l bbs2 = SOME b2 ==>
               LENGTH b1.bb_instructions = LENGTH b2.bb_instructions /\
               !j. j < LENGTH b1.bb_instructions ==>
                   (EL j b1.bb_instructions).inst_outputs =
                   (EL j b2.bb_instructions).inst_outputs)
End

(* Accessor lemmas for bbs_outputs_agree *)
Triviality bbs_outputs_agree_lookup:
  !labels bbs1 bbs2 l.
    bbs_outputs_agree labels bbs1 bbs2 /\ MEM l labels ==>
    ((?b. lookup_block l bbs1 = SOME b) <=> (?b. lookup_block l bbs2 = SOME b))
Proof
  rw[bbs_outputs_agree_def]
QED

Triviality bbs_outputs_agree_el:
  !labels bbs1 bbs2 l b1 b2.
    bbs_outputs_agree labels bbs1 bbs2 /\ MEM l labels /\
    lookup_block l bbs1 = SOME b1 /\ lookup_block l bbs2 = SOME b2 ==>
    LENGTH b1.bb_instructions = LENGTH b2.bb_instructions /\
    !j. j < LENGTH b1.bb_instructions ==>
        (EL j b1.bb_instructions).inst_outputs =
        (EL j b2.bb_instructions).inst_outputs
Proof
  rw[bbs_outputs_agree_def] >> metis_tac[]
QED

Triviality bbs_outputs_agree_mono:
  !labels1 labels2 bbs1 bbs2.
    bbs_outputs_agree labels2 bbs1 bbs2 /\
    (!l. MEM l labels1 ==> MEM l labels2) ==>
    bbs_outputs_agree labels1 bbs1 bbs2
Proof
  rw[bbs_outputs_agree_def] >> metis_tac[]
QED

(* replace_block at a non-member label preserves bbs_outputs_agree *)
Triviality bbs_outputs_agree_replace:
  !labels s bbs1 bbs2 bb1' bb2'.
    bbs_outputs_agree labels bbs1 bbs2 /\
    ~MEM s labels /\
    bb1'.bb_label = s /\ bb2'.bb_label = s ==>
    bbs_outputs_agree labels (replace_block s bb1' bbs1) (replace_block s bb2' bbs2)
Proof
  rpt strip_tac >>
  `!l. MEM l labels ==> l <> s` by (rpt strip_tac >> CCONTR_TAC >> gvs[]) >>
  simp[bbs_outputs_agree_def] >> rpt conj_tac
  >- (
    rpt strip_tac >>
    `l <> s` by metis_tac[] >>
    metis_tac[lookup_block_replace_neq, bbs_outputs_agree_lookup])
  >>
  rpt strip_tac >>
  `l <> s` by metis_tac[] >>
  `lookup_block l (replace_block s bb1' bbs1) = lookup_block l bbs1`
    by metis_tac[lookup_block_replace_neq] >>
  `lookup_block l (replace_block s bb2' bbs2) = lookup_block l bbs2`
    by metis_tac[lookup_block_replace_neq] >>
  gvs[] >>
  metis_tac[bbs_outputs_agree_el]
QED

(* update_succ_phis with same args preserves bbs_outputs_agree *)
Triviality bbs_outputs_agree_update_succ_phis:
  !labels rs lbl bbs1 bbs2 succs.
    bbs_outputs_agree labels bbs1 bbs2 ==>
    bbs_outputs_agree labels
      (update_succ_phis rs lbl bbs1 succs)
      (update_succ_phis rs lbl bbs2 succs)
Proof
  rpt strip_tac >> simp[bbs_outputs_agree_def] >> rpt conj_tac
  >- metis_tac[update_succ_phis_lookup_iff, bbs_outputs_agree_lookup]
  >>
  rpt strip_tac >>
  (* Get original blocks from bbs1 and bbs2 *)
  `?b1_orig. lookup_block l bbs1 = SOME b1_orig` by
    metis_tac[update_succ_phis_lookup_iff] >>
  (* update_succ_phis preserves outputs from b1_orig *)
  `?b1'. lookup_block l (update_succ_phis rs lbl bbs1 succs) = SOME b1' /\
         LENGTH b1'.bb_instructions = LENGTH b1_orig.bb_instructions /\
         !j'. j' < LENGTH b1_orig.bb_instructions ==>
              (EL j' b1'.bb_instructions).inst_outputs =
              (EL j' b1_orig.bb_instructions).inst_outputs` by
    metis_tac[update_succ_phis_preserves_outputs] >>
  `b1 = b1'` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `?b2_orig. lookup_block l bbs2 = SOME b2_orig` by
    metis_tac[update_succ_phis_lookup_iff] >>
  `?b2'. lookup_block l (update_succ_phis rs lbl bbs2 succs) = SOME b2' /\
         LENGTH b2'.bb_instructions = LENGTH b2_orig.bb_instructions /\
         !j'. j' < LENGTH b2_orig.bb_instructions ==>
              (EL j' b2'.bb_instructions).inst_outputs =
              (EL j' b2_orig.bb_instructions).inst_outputs` by
    metis_tac[update_succ_phis_preserves_outputs] >>
  `b2 = b2'` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  (* Original outputs agree *)
  drule_all bbs_outputs_agree_el >> strip_tac >> gvs[]
QED

Triviality bbs_outputs_agree_refl:
  !labels bbs. bbs_outputs_agree labels bbs bbs
Proof
  rw[bbs_outputs_agree_def] >> gvs[]
QED

(* One-sided replace: replace_block at s preserves agreement for labels not containing s *)
Triviality bbs_outputs_agree_replace_refl:
  !labels s bbs bb'.
    ~MEM s labels /\ bb'.bb_label = s ==>
    bbs_outputs_agree labels bbs (replace_block s bb' bbs)
Proof
  rpt strip_tac >> simp[bbs_outputs_agree_def] >> rpt conj_tac
  >- (rpt strip_tac >> `l <> s` by (metis_tac[]) >>
      imp_res_tac lookup_block_replace_neq >> metis_tac[])
  >- (rpt strip_tac >> `l <> s` by (metis_tac[]) >>
      imp_res_tac lookup_block_replace_neq >> gvs[])
QED

(* Transitivity for bbs_outputs_agree *)
Triviality bbs_outputs_agree_trans:
  !labels bbs1 bbs2 bbs3.
    bbs_outputs_agree labels bbs1 bbs2 /\
    bbs_outputs_agree labels bbs2 bbs3 ==>
    bbs_outputs_agree labels bbs1 bbs3
Proof
  rw[bbs_outputs_agree_def]
  >- metis_tac[]
  >- (`?b_mid. lookup_block l bbs2 = SOME b_mid` by metis_tac[] >>
      metis_tac[])
QED

(* One-sided update_succ_phis: bbs agrees with update_succ_phis applied to bbs *)
Triviality bbs_outputs_agree_update_succ_phis_refl:
  !labels bbs rs lbl succs.
    bbs_outputs_agree labels bbs (update_succ_phis rs lbl bbs succs)
Proof
  rpt gen_tac >> simp[bbs_outputs_agree_def] >> rpt conj_tac
  >- metis_tac[update_succ_phis_lookup_iff]
  >- (rpt strip_tac >>
      qpat_x_assum `lookup_block l bbs = SOME b1` (fn th =>
        mp_tac (MATCH_MP update_succ_phis_preserves_outputs th)) >>
      disch_then (qspecl_then [`succs`, `rs`, `lbl`] strip_assume_tac) >>
      gvs[])
QED

(* One-sided: bbs agrees with update_succ_phis(replace_block s ... bbs) for labels not containing s *)
Theorem bbs_outputs_agree_replace_update_refl:
  !labels s bbs rs1 bb' succs.
    ~MEM s labels /\ bb'.bb_label = s ==>
    bbs_outputs_agree labels bbs
      (update_succ_phis rs1 s (replace_block s bb' bbs) succs)
Proof
  rpt strip_tac >>
  irule bbs_outputs_agree_trans >>
  qexists_tac `replace_block s bb' bbs` >>
  conj_tac >- metis_tac[bbs_outputs_agree_replace_refl] >>
  simp[bbs_outputs_agree_update_succ_phis_refl]
QED

(* Composed: replace_block + update_succ_phis preserves agreement *)
Triviality bbs_outputs_agree_replace_update:
  !labels s bbs1 bbs2 rs1 bb1' bb2' succs.
    bbs_outputs_agree labels bbs1 bbs2 /\
    ~MEM s labels /\
    bb1'.bb_label = s /\ bb2'.bb_label = s ==>
    bbs_outputs_agree labels
      (update_succ_phis rs1 s (replace_block s bb1' bbs1) succs)
      (update_succ_phis rs1 s (replace_block s bb2' bbs2) succs)
Proof
  rpt strip_tac >>
  irule bbs_outputs_agree_update_succ_phis >>
  irule bbs_outputs_agree_replace >>
  metis_tac[]
QED

(* ===== rename_blocks_outputs_agree: FST + bbs_outputs_agree preservation ===== *)

Theorem rename_blocks_outputs_agree[local]:
  (!dtree rs bbs1 bbs2 succ_map ext.
    ALL_DISTINCT (dom_tree_labels dtree ++ ext) /\
    bbs_outputs_agree (dom_tree_labels dtree ++ ext) bbs1 bbs2 ==>
    FST (rename_blocks rs bbs1 succ_map dtree) =
    FST (rename_blocks rs bbs2 succ_map dtree) /\
    bbs_outputs_agree ext
      (SND (rename_blocks rs bbs1 succ_map dtree))
      (SND (rename_blocks rs bbs2 succ_map dtree))) /\
  (!children ctrs stacks bbs1 bbs2 succ_map ext.
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children) ++ ext) /\
    bbs_outputs_agree (FLAT (MAP dom_tree_labels children) ++ ext) bbs1 bbs2 ==>
    FST (rename_children ctrs stacks bbs1 succ_map children) =
    FST (rename_children ctrs stacks bbs2 succ_map children) /\
    bbs_outputs_agree ext
      (SND (rename_children ctrs stacks bbs1 succ_map children))
      (SND (rename_children ctrs stacks bbs2 succ_map children)))
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac >| [
    suspend "dnode",
    suspend "nil",
    suspend "cons"
  ]
QED

Resume rename_blocks_outputs_agree[dnode]:
  (* DNode s children *)
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  (* Establish lookup biconditional WITHOUT adding MEM to assumptions
     (gvs splits MEM x (l1 ++ l2)) *)
  `(?b. lookup_block s bbs1 = SOME b) <=>
   (?b. lookup_block s bbs2 = SOME b)` by (
    irule bbs_outputs_agree_lookup >>
    qexists_tac `dom_tree_labels (DNode s children) ++ ext` >>
    simp[Once dom_tree_labels_def, ETA_THM]) >>
  Cases_on `lookup_block s bbs1` >| [
    (* NONE case *)
    `lookup_block s bbs2 = NONE` by (
      Cases_on `lookup_block s bbs2` >> fs[] >> metis_tac[]) >>
    simp[rename_blocks_def] >>
    irule bbs_outputs_agree_mono >>
    qexists_tac `dom_tree_labels (DNode s children) ++ ext` >>
    simp[Once dom_tree_labels_def, ETA_THM, MEM_APPEND],
    ALL_TAC] >>
  rename1 `lookup_block s bbs1 = SOME bb1` >>
  `?bb2. lookup_block s bbs2 = SOME bb2` by metis_tac[] >>
  qpat_x_assum `(_ <=> _)` kall_tac >>
  `MEM s (dom_tree_labels (DNode s children) ++ ext)` by
    simp[Once dom_tree_labels_def, ETA_THM] >>
  drule_all bbs_outputs_agree_el >> strip_tac >>
  qpat_x_assum `MEM s _` kall_tac >>
  `bb1.bb_label = s` by metis_tac[lookup_block_label] >>
  `bb2.bb_label = s` by metis_tac[lookup_block_label] >>
  ONCE_REWRITE_TAC[rename_blocks_def] >> simp[] >>
  drule rename_block_insts_fst_outputs_only >>
  disch_then (qspec_then `rs` mp_tac) >>
  simp[] >> strip_tac >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  `rs1' = rs1` by fs[] >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `succs = case ALOOKUP succ_map s of
                         NONE => [] | SOME ss => ss` >>
  (* Establish bbs_outputs_agree for the replace+update result *)
  `bbs_outputs_agree (FLAT (MAP dom_tree_labels children) ++ ext)
     bbs1 bbs2` by (
    match_mp_tac bbs_outputs_agree_mono >>
    qexists_tac `dom_tree_labels (DNode s children) ++ ext` >>
    rpt strip_tac >- first_assum ACCEPT_TAC >>
    fs[Once dom_tree_labels_def, ETA_THM, MEM_APPEND]) >>
  `~MEM s (FLAT (MAP dom_tree_labels children) ++ ext)` by (
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    simp[Once dom_tree_labels_def, ETA_THM]) >>
  `bbs_outputs_agree (FLAT (MAP dom_tree_labels children) ++ ext)
     (update_succ_phis rs1 s
        (replace_block s (bb1 with bb_instructions := insts') bbs1) succs)
     (update_succ_phis rs1 s
        (replace_block s (bb2 with bb_instructions := insts'') bbs2) succs)` by (
    irule bbs_outputs_agree_replace_update >> simp[]) >>
  (* Apply IH for children *)
  first_x_assum (qspecl_then [`FST rs1`, `SND rs1`,
    `update_succ_phis rs1 s
       (replace_block s (bb1 with bb_instructions := insts') bbs1) succs`,
    `update_succ_phis rs1 s
       (replace_block s (bb2 with bb_instructions := insts'') bbs2) succs`,
    `succ_map`, `ext`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- (
      qpat_x_assum `ALL_DISTINCT _` mp_tac >>
      simp[Once dom_tree_labels_def, ETA_THM]) >>
    first_assum ACCEPT_TAC)) >>
  simp[]
QED

Resume rename_blocks_outputs_agree[nil]:
  (* [] case: rename_children ... [] = (ctrs, bbs) *)
  ONCE_REWRITE_TAC[rename_blocks_def] >> simp[]
QED

Resume rename_blocks_outputs_agree[cons]:
  (* dtree :: children case (HOL renames child→dtree, rest→children) *)
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  (* Apply child IH: rename_blocks agrees on dtree *)
  `FST (rename_blocks (ctrs,stacks) bbs1 succ_map dtree) =
   FST (rename_blocks (ctrs,stacks) bbs2 succ_map dtree) /\
   bbs_outputs_agree (FLAT (MAP dom_tree_labels children) ++ ext)
     (SND (rename_blocks (ctrs,stacks) bbs1 succ_map dtree))
     (SND (rename_blocks (ctrs,stacks) bbs2 succ_map dtree))` by (
    last_x_assum (qspecl_then [`(ctrs,stacks)`, `bbs1`, `bbs2`,
      `succ_map`, `FLAT (MAP dom_tree_labels children) ++ ext`] mp_tac) >>
    (impl_tac >- (
      conj_tac >- (
        qpat_x_assum `ALL_DISTINCT _` mp_tac >>
        simp[] >> metis_tac[APPEND_ASSOC, ALL_DISTINCT_APPEND]) >>
      match_mp_tac bbs_outputs_agree_mono >>
      qexists_tac `FLAT (MAP dom_tree_labels (dtree::children)) ++ ext` >>
      rpt strip_tac >- first_assum ACCEPT_TAC >>
      fs[MEM_APPEND])) >>
    simp[]) >>
  (* Apply rest IH: rename_children agrees on children *)
  qabbrev_tac `ctrs' = FST (rename_blocks (ctrs,stacks) bbs1 succ_map dtree)` >>
  first_x_assum (qspecl_then [`ctrs'`, `stacks`,
    `SND (rename_blocks (ctrs,stacks) bbs1 succ_map dtree)`,
    `SND (rename_blocks (ctrs,stacks) bbs2 succ_map dtree)`,
    `succ_map`, `ext`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- (
      qpat_x_assum `ALL_DISTINCT _` mp_tac >>
      simp[] >> metis_tac[APPEND_ASSOC, ALL_DISTINCT_APPEND]) >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Connect: unfold rename_children (dtree::children) *)
  ONCE_REWRITE_TAC[rename_blocks_def] >> simp[LET_THM] >>
  Cases_on `rename_blocks (ctrs,stacks) bbs1 succ_map dtree` >>
  Cases_on `rename_blocks (ctrs,stacks) bbs2 succ_map dtree` >>
  gvs[Abbr `ctrs'`]
QED

Finalise rename_blocks_outputs_agree;

(* ===== block_rename_states_outputs_agree ===== *)

(* block_rename_states produces the same entries when bbs agree on outputs.
   Key infrastructure for rename_blocks_body_match. *)
Theorem block_rename_states_outputs_agree[local]:
  (!dtree rs bbs1 bbs2 succ_map.
    ALL_DISTINCT (dom_tree_labels dtree) /\
    bbs_outputs_agree (dom_tree_labels dtree) bbs1 bbs2 ==>
    block_rename_states rs bbs1 succ_map dtree =
    block_rename_states rs bbs2 succ_map dtree) /\
  (!children ctrs stacks bbs1 bbs2 succ_map.
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
    bbs_outputs_agree (FLAT (MAP dom_tree_labels children)) bbs1 bbs2 ==>
    children_rename_states ctrs stacks bbs1 succ_map children =
    children_rename_states ctrs stacks bbs2 succ_map children)
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac >| [
    suspend "dnode",
    suspend "nil",
    suspend "cons"
  ]
QED

Resume block_rename_states_outputs_agree[dnode]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  sg `(?b. lookup_block s bbs1 = SOME b) <=>
      (?b. lookup_block s bbs2 = SOME b)`
  >- (irule bbs_outputs_agree_lookup >>
      qexists_tac `dom_tree_labels (DNode s children)` >>
      simp[Once dom_tree_labels_def, ETA_THM]) >>
  ONCE_REWRITE_TAC[block_rename_states_def] >>
  Cases_on `lookup_block s bbs1` >- (
    sg `lookup_block s bbs2 = NONE`
    >- (Cases_on `lookup_block s bbs2` >> fs[] >> metis_tac[]) >>
    simp[]) >>
  rename1 `lookup_block s bbs1 = SOME bb1` >>
  sg `?bb2. lookup_block s bbs2 = SOME bb2`
  >- metis_tac[] >>
  simp[] >>
  sg `MEM s (dom_tree_labels (DNode s children))`
  >- simp[Once dom_tree_labels_def, ETA_THM] >>
  drule_all bbs_outputs_agree_el >> strip_tac >>
  qpat_x_assum `MEM s _` kall_tac >>
  qpat_x_assum `(_ <=> _)` kall_tac >>
  drule rename_block_insts_fst_outputs_only >>
  disch_then (qspec_then `rs` mp_tac) >> simp[] >> strip_tac >>
  pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
  sg `rs1' = rs1` >- fs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!ctrs stacks _ _ _. _ ==> children_rename_states _ _ _ _ _ = _`
    (qspecl_then [`FST rs1`, `SND rs1`, `bbs1`, `bbs2`, `succ_map`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- (
      qpat_x_assum `ALL_DISTINCT (dom_tree_labels (DNode s children))` mp_tac >>
      simp[Once dom_tree_labels_def, ETA_THM, ALL_DISTINCT]) >>
    match_mp_tac bbs_outputs_agree_mono >>
    qexists_tac `dom_tree_labels (DNode s children)` >>
    rpt strip_tac >- first_assum ACCEPT_TAC >>
    fs[Once dom_tree_labels_def, ETA_THM, MEM_APPEND])) >>
  simp[]
QED

Resume block_rename_states_outputs_agree[nil]:
  simp[block_rename_states_def]
QED

Resume block_rename_states_outputs_agree[cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC[block_rename_states_def] >> simp[LET_THM] >>
  `ALL_DISTINCT (dom_tree_labels dtree)` by (
    qpat_x_assum `ALL_DISTINCT (FLAT (MAP dom_tree_labels (dtree::children)))` mp_tac >>
    simp[] >> metis_tac[ALL_DISTINCT_APPEND]) >>
  `block_rename_states (ctrs,stacks) bbs1 succ_map dtree =
   block_rename_states (ctrs,stacks) bbs2 succ_map dtree` by (
    last_x_assum (qspecl_then [`(ctrs,stacks)`, `bbs1`, `bbs2`, `succ_map`] mp_tac) >>
    (impl_tac >- (
      conj_tac >- first_assum ACCEPT_TAC >>
      match_mp_tac bbs_outputs_agree_mono >>
      qexists_tac `FLAT (MAP dom_tree_labels (dtree::children))` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp[MEM_APPEND])) >>
    simp[]) >>
  simp[] >>
  `FST (rename_blocks (ctrs,stacks) bbs1 succ_map dtree) =
   FST (rename_blocks (ctrs,stacks) bbs2 succ_map dtree)` by (
    mp_tac (CONJUNCT1 rename_blocks_outputs_agree) >>
    disch_then (qspecl_then [`dtree`, `(ctrs,stacks)`, `bbs1`, `bbs2`,
      `succ_map`, `FLAT (MAP dom_tree_labels children)`] mp_tac) >>
    (impl_tac >- (
      conj_tac >- (
        qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >> simp[] >>
        metis_tac[APPEND_ASSOC, ALL_DISTINCT_APPEND]) >>
      match_mp_tac bbs_outputs_agree_mono >>
      qexists_tac `FLAT (MAP dom_tree_labels (dtree::children))` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp[MEM_APPEND])) >>
    simp[]) >>
  Cases_on `rename_blocks (ctrs,stacks) bbs1 succ_map dtree` >>
  Cases_on `rename_blocks (ctrs,stacks) bbs2 succ_map dtree` >>
  gvs[] >>
  first_x_assum (qspecl_then [`q`, `stacks`, `bbs1`, `bbs2`, `succ_map`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- (
      qpat_x_assum `ALL_DISTINCT (_ ++ _)` mp_tac >> simp[] >>
      metis_tac[ALL_DISTINCT_APPEND]) >>
    match_mp_tac bbs_outputs_agree_mono >>
    qexists_tac `dom_tree_labels dtree ++ FLAT (MAP dom_tree_labels children)` >>
    conj_tac >- first_assum ACCEPT_TAC >>
    simp[])) >>
  simp[]
QED

Finalise block_rename_states_outputs_agree;

(* ===== rename_blocks_body_match ===== *)

(* For any label in the tree, the non-PHI body instructions in the output of
   rename_blocks match what rename_block_insts would produce.
   Uses block_rename_states to identify the correct rename state at each label.
   
   The key difficulty: rename_blocks modifies bbs as it processes each node
   (replace_block + update_succ_phis), but block_rename_states uses the
   original bbs. These agree because:
   - rename_block_insts FST depends only on inst_outputs (rename_block_insts_fst_outputs_only)
   - update_succ_phis preserves inst_outputs (update_succ_phis_preserves_outputs)
   - non-PHI instructions are unchanged by update_succ_phis *)

(* lookup_block existence depends only on labels *)
Triviality lookup_block_exists_labels:
  !l bbs1 bbs2.
    MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) bbs2 ==>
    ((?b. lookup_block l bbs1 = SOME b) <=> (?b. lookup_block l bbs2 = SOME b))
Proof
  Induct_on `bbs1` >> rpt gen_tac >>
  simp[lookup_block_def, FIND_thm] >>
  Cases_on `bbs2` >> simp[FIND_thm] >>
  strip_tac >> gvs[] >>
  Cases_on `h.bb_label = l` >> gvs[] >>
  first_x_assum (qspecl_then [`l`, `t`] mp_tac) >>
  simp[lookup_block_def]
QED

(* lookup_block preserved through rename_blocks/rename_children (existence) *)
Triviality rename_blocks_lookup_exists[local]:
  (!dtree rs bbs succ_map lbl bb.
    lookup_block lbl bbs = SOME bb ==>
    ?b'. lookup_block lbl (SND (rename_blocks rs bbs succ_map dtree)) = SOME b') /\
  (!children ctrs stacks bbs succ_map lbl bb.
    lookup_block lbl bbs = SOME bb ==>
    ?b'. lookup_block lbl (SND (rename_children ctrs stacks bbs succ_map children)) = SOME b')
Proof
  conj_tac >> rpt strip_tac >| [
    mp_tac (Q.SPECL [`lbl`, `bbs`,
      `SND (rename_blocks rs bbs succ_map dtree)`] lookup_block_exists_labels) >>
    simp[rename_blocks_preserves_labels] >>
    metis_tac[],
    mp_tac (Q.SPECL [`lbl`, `bbs`,
      `SND (rename_children ctrs stacks bbs succ_map children)`]
      lookup_block_exists_labels) >>
    simp[rename_blocks_children_preserves_labels] >>
    metis_tac[]
  ]
QED

(* rename_blocks/children preserves block content for labels outside the tree *)
Triviality rename_blocks_preserves_outside[local]:
  (!dtree rs bbs succ_map l (bb:basic_block).
    ~MEM l (dom_tree_labels dtree) /\
    lookup_block l bbs = SOME bb ==>
    ?bb'. lookup_block l (SND (rename_blocks rs bbs succ_map dtree)) = SOME bb' /\
          LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
          (!j. j < LENGTH bb.bb_instructions ==>
               (EL j bb'.bb_instructions).inst_outputs =
               (EL j bb.bb_instructions).inst_outputs)) /\
  (!children ctrs stacks bbs succ_map l (bb:basic_block).
    ~MEM l (FLAT (MAP dom_tree_labels children)) /\
    lookup_block l bbs = SOME bb ==>
    ?bb'. lookup_block l (SND (rename_children ctrs stacks bbs succ_map children)) = SOME bb' /\
          LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
          (!j. j < LENGTH bb.bb_instructions ==>
               (EL j bb'.bb_instructions).inst_outputs =
               (EL j bb.bb_instructions).inst_outputs))
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac >| [
    suspend "dnode",
    suspend "nil",
    suspend "cons"
  ]
QED

Resume rename_blocks_preserves_outside[nil]:
  simp[Once rename_blocks_def]
QED

Resume rename_blocks_preserves_outside[dnode]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `~MEM l _` mp_tac >>
  simp[Once dom_tree_labels_def, ETA_THM] >> strip_tac >>
  simp[Once rename_blocks_def, LET_THM] >>
  Cases_on `lookup_block s bbs` >> simp[] >>
  Cases_on `rename_block_insts rs x.bb_instructions` >>
  rename1 `rename_block_insts rs _ = (rs1, insts')` >> simp[] >>
  (* replace_block preserves l's block since l ≠ s *)
  `x.bb_label = s` by (imp_res_tac lookup_block_label >> simp[]) >>
  qabbrev_tac `bbs1 = replace_block s (x with bb_instructions := insts') bbs` >>
  qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss` >>
  `lookup_block l bbs1 = SOME bb` by (
    simp[Abbr `bbs1`, lookup_block_replace_neq]) >>
  (* update_succ_phis preserves outputs *)
  `?bb2. lookup_block l (update_succ_phis rs1 s bbs1 succs) = SOME bb2 /\
         LENGTH bb2.bb_instructions = LENGTH bb.bb_instructions /\
         (!j. j < LENGTH bb.bb_instructions ==>
              (EL j bb2.bb_instructions).inst_outputs =
              (EL j bb.bb_instructions).inst_outputs)` by (
    drule update_succ_phis_preserves_outputs >>
    disch_then (qspecl_then [`succs`, `rs1`, `s`] strip_assume_tac) >>
    qexists_tac `bb'` >> simp[]) >>
  (* children IH *)
  first_x_assum (qspecl_then
    [`(FST rs1)`, `(SND rs1)`,
     `update_succ_phis rs1 s bbs1 succs`,
     `succ_map`, `l`, `bb2`] mp_tac) >>
  simp[]
QED

Resume rename_blocks_preserves_outside[cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `~MEM l _` mp_tac >>
  simp[Once MAP, Once FLAT] >> strip_tac >>
  simp[Once rename_blocks_def, LET_THM] >>
  Cases_on `rename_blocks (ctrs,stacks) bbs succ_map dtree` >>
  rename1 `_ = (ctrs2, bbs2)` >> simp[] >>
  (* dtree IH: l's block preserved in bbs2 *)
  first_x_assum (qspecl_then [`(ctrs,stacks)`, `bbs`, `succ_map`, `l`, `bb`] mp_tac) >>
  impl_tac >- (simp[]) >>
  strip_tac >>
  (* bb' is in SND(rename_blocks ...) = bbs2 *)
  `lookup_block l bbs2 = SOME bb'` by (
    qpat_x_assum `lookup_block l (SND _) = _` mp_tac >>
    qpat_x_assum `_ = (ctrs2, bbs2)` (fn th => simp[th])) >>
  (* children IH *)
  first_x_assum (qspecl_then [`ctrs2`, `stacks`, `bbs2`, `succ_map`, `l`, `bb'`] mp_tac) >>
  simp[]
QED

Finalise rename_blocks_preserves_outside;

(* Keys of block_rename_states = dom_tree_labels *)
Triviality block_rename_states_keys:
  (!dtree rs bbs succ_map.
    (!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs = SOME b) ==>
    MAP FST (block_rename_states rs bbs succ_map dtree) =
    dom_tree_labels dtree) /\
  (!children ctrs stacks bbs succ_map.
    (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs = SOME b) ==>
    MAP FST (children_rename_states ctrs stacks bbs succ_map children) =
    FLAT (MAP dom_tree_labels children))
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac >| [
    suspend "dnode",
    suspend "nil",
    suspend "cons"
  ]
QED

Resume block_rename_states_keys[nil]:
  simp[Once block_rename_states_def]
QED

Resume block_rename_states_keys[dnode]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `?bb. lookup_block s bbs = SOME bb` by (
    first_assum (qspec_then `s` mp_tac) >>
    simp[Once dom_tree_labels_def, ETA_THM]) >>
  simp[Once block_rename_states_def] >>
  pairarg_tac >> fs[] >>
  ONCE_REWRITE_TAC[dom_tree_labels_def] >> simp[ETA_THM] >>
  first_x_assum match_mp_tac >>
  rpt strip_tac >>
  qpat_x_assum `!l. MEM l (dom_tree_labels _) ==> _`
    (qspec_then `l` mp_tac) >>
  simp[Once dom_tree_labels_def, ETA_THM]
QED

Resume block_rename_states_keys[cons]:
  rpt gen_tac >> ntac 2 strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once block_rename_states_def, LET_THM]
QED

Finalise block_rename_states_keys;

(* Standalone helper: rename_blocks on dtree preserves outputs for labels
   outside the tree, yielding bbs_outputs_agree. *)
Triviality rename_blocks_bbs_outputs_agree[local]:
  !dtree rs bbs succ_map labels.
    (!l. MEM l labels ==> ~MEM l (dom_tree_labels dtree)) /\
    (!l. MEM l labels ==> ?b. lookup_block l bbs = SOME b) ==>
    bbs_outputs_agree labels bbs (SND (rename_blocks rs bbs succ_map dtree))
Proof
  rpt strip_tac >>
  simp[bbs_outputs_agree_def] >> rpt conj_tac >> rpt strip_tac
  >- (
    (* existence in bbs' *)
    `~MEM l (dom_tree_labels dtree)` by metis_tac[] >>
    `?b0. lookup_block l bbs = SOME b0` by metis_tac[] >>
    mp_tac (CONJUNCT1 rename_blocks_preserves_outside) >>
    disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`,
      `l`, `b0`] mp_tac) >>
    simp[] >> metis_tac[])
  >- (
    (* LENGTH + outputs: use rename_blocks_preserves_outside *)
    `~MEM l (dom_tree_labels dtree)` by metis_tac[] >>
    mp_tac (CONJUNCT1 rename_blocks_preserves_outside) >>
    disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`,
      `l`, `b1`] mp_tac) >>
    simp[] >> strip_tac >>
    (* b2 = bb' by determinism of lookup_block *)
    `b2 = bb'` by (
      qpat_x_assum `lookup_block l (SND _) = SOME b2` mp_tac >>
      qpat_x_assum `lookup_block l (SND _) = SOME bb'` mp_tac >>
      simp[lookup_block_def]) >>
    gvs[])
  >- (
    `~MEM l (dom_tree_labels dtree)` by metis_tac[] >>
    mp_tac (CONJUNCT1 rename_blocks_preserves_outside) >>
    disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`,
      `l`, `b1`] mp_tac) >>
    simp[] >> strip_tac >>
    `b2 = bb'` by (
      qpat_x_assum `lookup_block l (SND _) = SOME b2` mp_tac >>
      qpat_x_assum `lookup_block l (SND _) = SOME bb'` mp_tac >>
      simp[lookup_block_def]) >>
    gvs[])
QED

Triviality rename_blocks_body_match:
  (!dtree rs bbs succ_map lbl bb_orig rs_entry.
    lookup_block lbl bbs = SOME bb_orig /\
    MEM lbl (dom_tree_labels dtree) /\
    ALL_DISTINCT (dom_tree_labels dtree) /\
    (!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs = SOME b) /\
    ALOOKUP (block_rename_states rs bbs succ_map dtree) lbl = SOME rs_entry ==>
    ?bb'. lookup_block lbl (SND (rename_blocks rs bbs succ_map dtree)) = SOME bb' /\
          phi_refines
            (bb_orig with bb_instructions :=
               SND (rename_block_insts rs_entry bb_orig.bb_instructions))
            bb') /\
  (!children ctrs stacks bbs succ_map lbl bb_orig rs_entry.
    lookup_block lbl bbs = SOME bb_orig /\
    MEM lbl (FLAT (MAP dom_tree_labels children)) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==> ?b. lookup_block l bbs = SOME b) /\
    ALOOKUP (children_rename_states ctrs stacks bbs succ_map children) lbl = SOME rs_entry ==>
    ?bb'. lookup_block lbl (SND (rename_children ctrs stacks bbs succ_map children)) = SOME bb' /\
          phi_refines
            (bb_orig with bb_instructions :=
               SND (rename_block_insts rs_entry bb_orig.bb_instructions))
            bb')
Proof
  ho_match_mp_tac dom_tree_induction >> rpt conj_tac >| [
    suspend "dnode",
    suspend "nil",
    suspend "cons"
  ]
QED

Resume rename_blocks_body_match[nil]:
  simp[Once dom_tree_labels_def, Once block_rename_states_def]
QED

Resume rename_blocks_body_match[dnode]:
  (* DNode s children: split into root case and children case *)
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  (* lbl is either s or in children *)
  `lbl = s \/ MEM lbl (FLAT (MAP dom_tree_labels children))` by (
    qpat_x_assum `MEM lbl (dom_tree_labels (DNode s children))` mp_tac >>
    simp[Once dom_tree_labels_def, ETA_THM] >> metis_tac[]) >| [
    suspend "dnode_root",
    suspend "dnode_child"
  ]
QED

Resume rename_blocks_body_match[dnode_root]:
  (* lbl = s: root case *)
  gvs[] >>
  (* ALOOKUP at root gives (rs, ...) *)
  qpat_x_assum `ALOOKUP (block_rename_states _ _ _ _) _ = SOME _` mp_tac >>
  simp[Once block_rename_states_def] >>
  pairarg_tac >> fs[] >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`rs`, `bbs`, `succ_map`, `lbl`, `children`, `bb_orig`]
           rename_blocks_root_refines) >>
  simp[] >> strip_tac >>
  imp_res_tac phi_refines_implies_non_phi_refines >>
  Cases_on `rename_block_insts rs bb_orig.bb_instructions` >>
  gvs[]
QED

Resume rename_blocks_body_match[dnode_child]:
  (* lbl in children: delegate to children IH *)
  `~MEM s (FLAT (MAP dom_tree_labels children))` by (
    qpat_x_assum `ALL_DISTINCT (dom_tree_labels (DNode s children))` mp_tac >>
    simp[Once dom_tree_labels_def, ETA_THM, ALL_DISTINCT]) >>
  `ALL_DISTINCT (FLAT (MAP dom_tree_labels children))` by (
    qpat_x_assum `ALL_DISTINCT (dom_tree_labels (DNode s children))` mp_tac >>
    simp[Once dom_tree_labels_def, ETA_THM, ALL_DISTINCT, ALL_DISTINCT_APPEND]) >>
  `lbl <> s` by (metis_tac[MEM]) >>
  `?bb_s. lookup_block s bbs = SOME bb_s` by (
    qpat_assum `!l. MEM l (dom_tree_labels _) ==> _`
      (qspec_then `s` mp_tac) >>
    simp[Once dom_tree_labels_def, ETA_THM]) >>
  (* Extract children ALOOKUP from DNode ALOOKUP *)
  qpat_x_assum `ALOOKUP (block_rename_states _ _ _ (DNode _ _)) _ = SOME _` mp_tac >>
  simp[Once block_rename_states_def] >>
  pairarg_tac >> fs[] >> strip_tac >>
  qabbrev_tac `bb'_s = bb_s with bb_instructions := insts'` >>
  qabbrev_tac `bbs1 = replace_block s bb'_s bbs` >>
  qabbrev_tac `succs = case ALOOKUP succ_map s of NONE => [] | SOME ss => ss` >>
  qabbrev_tac `bbs2 = update_succ_phis rs1 s bbs1 succs` >>
  (* rename_blocks output = rename_children on bbs2 *)
  `SND (rename_blocks rs bbs succ_map (DNode s children)) =
   SND (rename_children (FST rs1) (SND rs1) bbs2 succ_map children)` by (
    simp[Once rename_blocks_def, LET_THM] >>
    Cases_on `rename_block_insts rs bb_s.bb_instructions` >>
    fs[Abbr `bbs1`, Abbr `bbs2`, Abbr `bb'_s`, Abbr `succs`]) >>
  simp[] >>
  (* Get bb_orig2 from bbs2 via update_succ_phis_preserves_outputs *)
  `bb'_s.bb_label = s` by (
    simp[Abbr `bb'_s`] >> imp_res_tac lookup_block_label >> simp[]) >>
  `lookup_block lbl bbs1 = SOME bb_orig` by (
    simp[Abbr `bbs1`] >>
    imp_res_tac lookup_block_replace_neq >> gvs[]) >>
  mp_tac (Q.SPECL [`succs`, `rs1`, `s`, `bbs1`, `lbl`, `bb_orig`]
           update_succ_phis_preserves_outputs) >>
  simp[Abbr `bbs2`] >> strip_tac >>
  rename1 `lookup_block lbl (update_succ_phis rs1 s bbs1 succs) = SOME bb_orig2` >>
  qabbrev_tac `bbs2 = update_succ_phis rs1 s bbs1 succs` >>
  (* Bridge rename states: bbs and bbs2 agree on children labels *)
  `bbs_outputs_agree (FLAT (MAP dom_tree_labels children)) bbs bbs2` by (
    simp[Abbr `bbs2`, Abbr `bbs1`] >>
    irule bbs_outputs_agree_replace_update_refl >> simp[]) >>
  `children_rename_states (FST rs1) (SND rs1) bbs succ_map children =
   children_rename_states (FST rs1) (SND rs1) bbs2 succ_map children` by (
    irule (CONJUNCT2 block_rename_states_outputs_agree) >> simp[]) >>
  (* The ALOOKUP for children uses bbs, convert to bbs2 *)
  `ALOOKUP (children_rename_states (FST rs1) (SND rs1) bbs2 succ_map children) lbl =
   SOME rs_entry` by (metis_tac[]) >>
  (* Lookup precondition for bbs2 *)
  `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
       ?b. lookup_block l bbs2 = SOME b` by (
    rpt strip_tac >>
    `MEM l (dom_tree_labels (DNode s children))` by (
      simp[Once dom_tree_labels_def, ETA_THM]) >>
    `?b0. lookup_block l bbs = SOME b0` by (metis_tac[]) >>
    metis_tac[bbs_outputs_agree_lookup]) >>
  (* Apply children IH with bbs2 and bb_orig2 *)
  first_x_assum (qspecl_then [`FST rs1`, `SND rs1`, `bbs2`, `succ_map`,
                               `lbl`, `bb_orig2`, `rs_entry`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `bb'` >> simp[] >>
  (* Chain: bb_orig(rs_entry) phi_refines bb_orig2(rs_entry) phi_refines bb' *)
  irule phi_refines_trans >>
  qexists_tac `bb_orig2 with bb_instructions :=
    SND (rename_block_insts rs_entry bb_orig2.bb_instructions)` >>
  conj_tac
  >- (
    (* Conjunct 1: phi_refines (bb_orig ...) (bb_orig2 ...) *)
    irule rename_block_insts_phi_refines >> simp[])
  >> (
    (* Conjunct 2: phi_refines (bb_orig2 ...) bb' — from IH *)
    first_assum ACCEPT_TAC)
QED

Resume rename_blocks_body_match[cons]:
  rpt strip_tac >>
  (* Extract ALL_DISTINCT components early *)
  `ALL_DISTINCT (dom_tree_labels dtree) /\
   ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
   (!x. MEM x (dom_tree_labels dtree) ==>
        ~MEM x (FLAT (MAP dom_tree_labels children)))` by (
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    simp[Once MAP, Once FLAT, ALL_DISTINCT_APPEND]) >>
  `!l. MEM l (dom_tree_labels dtree) ==>
       ?b. lookup_block l bbs = SOME b` by (
    rpt strip_tac >>
    qpat_assum `!l. MEM l (FLAT (MAP dom_tree_labels (dtree::_))) ==> _`
      match_mp_tac >>
    simp[Once MAP, Once FLAT]) >>
  `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
       ?b. lookup_block l bbs = SOME b` by (
    rpt strip_tac >>
    qpat_assum `!l. MEM l (FLAT (MAP dom_tree_labels (dtree::_))) ==> _`
      match_mp_tac >>
    simp[Once MAP, Once FLAT]) >>
  (* Unfold ALOOKUP in children_rename_states cons *)
  qpat_x_assum `ALOOKUP _ lbl = SOME _` mp_tac >>
  simp[Once block_rename_states_def, LET_THM, ALOOKUP_APPEND] >>
  Cases_on `rename_blocks (ctrs,stacks) bbs succ_map dtree` >>
  rename1 `rename_blocks _ bbs _ dtree = (ctrs', bbs')` >>
  `bbs' = SND (rename_blocks (ctrs,stacks) bbs succ_map dtree)` by (fs[]) >>
  simp[] >>
  Cases_on `ALOOKUP (block_rename_states (ctrs,stacks) bbs succ_map dtree) lbl`
  >- (
    strip_tac >> suspend "none_case"
  )
  >- (
    rename1 `ALOOKUP _ lbl = SOME rs_e` >>
    strip_tac >> suspend "some_case"
  )
QED

Triviality children_rename_states_bridge[local]:
  !dtree rs bbs succ_map children ctrs' stacks bbs'.
    ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
    (!x. MEM x (dom_tree_labels dtree) ==>
         ~MEM x (FLAT (MAP dom_tree_labels children))) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
         ?b. lookup_block l bbs = SOME b) /\
    bbs' = SND (rename_blocks rs bbs succ_map dtree) ==>
    children_rename_states ctrs' stacks bbs succ_map children =
    children_rename_states ctrs' stacks bbs' succ_map children
Proof
  rpt strip_tac >>
  irule (CONJUNCT2 block_rename_states_outputs_agree) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  pop_assum (fn eq => PURE_ONCE_REWRITE_TAC [eq]) >>
  irule rename_blocks_bbs_outputs_agree >>
  rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!x. MEM x (dom_tree_labels dtree) ==> _`
        (qspec_then `l` mp_tac) >>
      metis_tac[])
QED

Triviality rename_children_cons_none_case[local]:
  !dtree rs bbs succ_map children lbl bb_orig rs_entry.
    (* IHs *)
    (!ctrs stacks bbs succ_map lbl bb_orig rs_entry.
      lookup_block lbl bbs = SOME bb_orig /\
      MEM lbl (FLAT (MAP dom_tree_labels children)) /\
      ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
      (!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
           ?b. lookup_block l bbs = SOME b) /\
      ALOOKUP (children_rename_states ctrs stacks bbs succ_map children) lbl =
        SOME rs_entry ==>
      ?bb'. lookup_block lbl
              (SND (rename_children ctrs stacks bbs succ_map children)) = SOME bb' /\
            phi_refines
              (bb_orig with bb_instructions :=
                SND (rename_block_insts rs_entry bb_orig.bb_instructions)) bb') /\
    (* Preconditions *)
    lookup_block lbl bbs = SOME bb_orig /\
    MEM lbl (FLAT (MAP dom_tree_labels (dtree::children))) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels (dtree::children))) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels (dtree::children))) ==>
         ?b. lookup_block l bbs = SOME b) /\
    ALOOKUP (block_rename_states rs bbs succ_map dtree) lbl = NONE /\
    ALOOKUP (children_rename_states
      (FST (rename_blocks rs bbs succ_map dtree))
      (SND rs)
      bbs succ_map children) lbl = SOME rs_entry ==>
    ?bb'. lookup_block lbl
            (SND (rename_children (FST rs) (SND rs) bbs succ_map
              (dtree::children))) = SOME bb' /\
          phi_refines
            (bb_orig with bb_instructions :=
              SND (rename_block_insts rs_entry bb_orig.bb_instructions)) bb'
Proof
  rpt strip_tac >>
  (* Extract disjointness from ALL_DISTINCT *)
  `ALL_DISTINCT (dom_tree_labels dtree) /\
   ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
   (!x. MEM x (dom_tree_labels dtree) ==>
        ~MEM x (FLAT (MAP dom_tree_labels children)))` by (
    qpat_x_assum `ALL_DISTINCT (FLAT (MAP dom_tree_labels (dtree::_)))` mp_tac >>
    simp[Once MAP, Once FLAT, ALL_DISTINCT_APPEND]) >>
  (* ~MEM lbl (dom_tree_labels dtree) from ALOOKUP = NONE *)
  `~MEM lbl (dom_tree_labels dtree)` by (
    CCONTR_TAC >> fs[] >>
    mp_tac (CONJUNCT1 block_rename_states_keys) >>
    disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`] mp_tac) >>
    simp[] >> strip_tac >> fs[ALOOKUP_NONE]) >>
  `MEM lbl (FLAT (MAP dom_tree_labels children))` by (
    qpat_x_assum `MEM lbl (FLAT (MAP dom_tree_labels (dtree::_)))` mp_tac >>
    simp[Once MAP, Once FLAT]) >>
  `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
       ?b. lookup_block l bbs = SOME b` by (
    rpt strip_tac >>
    qpat_assum `!l. MEM l (FLAT (MAP dom_tree_labels (dtree::_))) ==> _`
      match_mp_tac >>
    simp[Once MAP, Once FLAT]) >>
  (* Unfold rename_children cons *)
  Cases_on `rename_blocks rs bbs succ_map dtree` >>
  rename1 `rename_blocks rs bbs succ_map dtree = (ctrs', bbs')` >>
  `SND (rename_children (FST rs) (SND rs) bbs succ_map (dtree::children)) =
   SND (rename_children ctrs' (SND rs) bbs' succ_map children)` by (
    simp[Once rename_blocks_def, LET_THM]) >>
  (* Bridge rename states *)
  mp_tac children_rename_states_bridge >>
  disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`,
    `children`, `ctrs'`, `SND rs`, `bbs'`] mp_tac) >>
  simp[] >> strip_tac >>
  (* Use rename_blocks_preserves_outside: gives lookup + LENGTH + outputs *)
  mp_tac (CONJUNCT1 rename_blocks_preserves_outside) >>
  disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`,
    `lbl`, `bb_orig`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CHOOSE_THEN STRIP_ASSUME_TAC) >>
  rename1 `lookup_block lbl (SND (rename_blocks _ _ _ _)) = SOME b_out` >>
  `lookup_block lbl bbs' = SOME b_out` by (
    qpat_x_assum `lookup_block lbl (SND _) = _` mp_tac >>
    qpat_assum `rename_blocks _ _ _ _ = _`
      (fn eq => PURE_REWRITE_TAC [eq, pairTheory.SND]) >>
    disch_then ACCEPT_TAC) >>
  (* phi_refines bb_orig b_out *)
  `phi_refines bb_orig b_out` by (
    mp_tac (CONJUNCT1 rename_preserves_other_phi_refines) >>
    disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`,
      `lbl`, `bb_orig`, `b_out`] mp_tac) >>
    (impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `rename_blocks _ _ _ _ = _`
        (fn eq => PURE_ONCE_REWRITE_TAC [eq, pairTheory.SND]) >>
      first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >>
  (* Establish: every child label has a block in bbs' *)
  `!l. MEM l (FLAT (MAP dom_tree_labels children)) ==>
       ?b. lookup_block l bbs' = SOME b` by (
    rpt strip_tac >>
    `?b0. lookup_block l bbs = SOME b0` by (
      first_x_assum match_mp_tac >> first_assum ACCEPT_TAC) >>
    mp_tac (CONJUNCT1 rename_blocks_lookup_exists) >>
    disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`,
      `l`, `b0`] mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    strip_tac >>
    qpat_x_assum `lookup_block l (SND _) = _` mp_tac >>
    qpat_assum `rename_blocks _ _ _ _ = _`
      (fn eq => PURE_REWRITE_TAC [eq, pairTheory.SND]) >>
    metis_tac[]) >>
  (* Establish: ALOOKUP children_rename_states with bbs' *)
  `ALOOKUP (children_rename_states ctrs' (SND rs) bbs' succ_map children) lbl =
     SOME rs_entry` by (
    qpat_assum `children_rename_states _ _ bbs _ _ = _`
      (fn eq => PURE_ONCE_REWRITE_TAC [GSYM eq]) >>
    qpat_x_assum `ALOOKUP (children_rename_states (FST _) _ _ _ _) _ = _` mp_tac >>
    qpat_assum `rename_blocks _ _ _ _ = _`
      (fn eq => PURE_REWRITE_TAC [eq, pairTheory.FST]) >>
    disch_then ACCEPT_TAC) >>
  (* Apply children IH with b_out *)
  first_x_assum (qspecl_then [`ctrs'`, `SND rs`, `bbs'`, `succ_map`,
    `lbl`, `b_out`, `rs_entry`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CHOOSE_THEN STRIP_ASSUME_TAC) >>
  qexists_tac `bb'` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule phi_refines_trans >>
  qexists_tac `b_out with bb_instructions :=
    SND (rename_block_insts rs_entry b_out.bb_instructions)` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule phi_refines_rename_bridge >>
  first_assum ACCEPT_TAC
QED

Triviality rename_children_cons_some_case[local]:
  !dtree rs bbs succ_map children lbl bb_orig rs_entry.
    (* dtree IH *)
    (!rs bbs succ_map lbl bb_orig rs_entry.
      lookup_block lbl bbs = SOME bb_orig /\
      MEM lbl (dom_tree_labels dtree) /\
      ALL_DISTINCT (dom_tree_labels dtree) /\
      (!l. MEM l (dom_tree_labels dtree) ==>
           ?b. lookup_block l bbs = SOME b) /\
      ALOOKUP (block_rename_states rs bbs succ_map dtree) lbl =
        SOME rs_entry ==>
      ?bb'. lookup_block lbl
              (SND (rename_blocks rs bbs succ_map dtree)) = SOME bb' /\
            phi_refines
              (bb_orig with bb_instructions :=
                SND (rename_block_insts rs_entry bb_orig.bb_instructions)) bb') /\
    (* Preconditions *)
    lookup_block lbl bbs = SOME bb_orig /\
    MEM lbl (FLAT (MAP dom_tree_labels (dtree::children))) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels (dtree::children))) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels (dtree::children))) ==>
         ?b. lookup_block l bbs = SOME b) /\
    ALOOKUP (block_rename_states rs bbs succ_map dtree) lbl = SOME rs_entry ==>
    ?bb'. lookup_block lbl
            (SND (rename_children (FST rs) (SND rs) bbs succ_map
              (dtree::children))) = SOME bb' /\
          phi_refines
            (bb_orig with bb_instructions :=
              SND (rename_block_insts rs_entry bb_orig.bb_instructions)) bb'
Proof
  rpt strip_tac >>
  (* Extract disjointness from ALL_DISTINCT *)
  `ALL_DISTINCT (dom_tree_labels dtree) /\
   ALL_DISTINCT (FLAT (MAP dom_tree_labels children)) /\
   (!x. MEM x (dom_tree_labels dtree) ==>
        ~MEM x (FLAT (MAP dom_tree_labels children)))` by (
    qpat_x_assum `ALL_DISTINCT (FLAT (MAP dom_tree_labels (dtree::_)))` mp_tac >>
    simp[Once MAP, Once FLAT, ALL_DISTINCT_APPEND]) >>
  (* Derive lookup for dtree labels *)
  `!l. MEM l (dom_tree_labels dtree) ==>
       ?b. lookup_block l bbs = SOME b` by (
    rpt strip_tac >>
    qpat_assum `!l. MEM l (FLAT (MAP dom_tree_labels (dtree::_))) ==> _`
      match_mp_tac >>
    simp[Once MAP, Once FLAT]) >>
  (* MEM lbl (dom_tree_labels dtree) — from ALOOKUP SOME + keys *)
  mp_tac (CONJUNCT1 block_rename_states_keys) >>
  disch_then (qspecl_then [`dtree`, `rs`, `bbs`, `succ_map`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `MEM lbl (dom_tree_labels dtree)` by (
    qpat_x_assum `MAP FST _ = dom_tree_labels _` (SUBST1_TAC o SYM) >>
    simp[MEM_MAP] >> qexists_tac `(lbl, rs_entry)` >> simp[] >>
    match_mp_tac ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
  `~MEM lbl (FLAT (MAP dom_tree_labels children))` by metis_tac[] >>
  (* Apply dtree IH *)
  first_x_assum (qspecl_then [`rs`, `bbs`, `succ_map`,
    `lbl`, `bb_orig`, `rs_entry`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CHOOSE_THEN STRIP_ASSUME_TAC) >>
  (* Unfold rename_children cons *)
  Cases_on `rename_blocks rs bbs succ_map dtree` >>
  rename1 `rename_blocks rs bbs succ_map dtree = (ctrs', bbs')` >>
  `SND (rename_children (FST rs) (SND rs) bbs succ_map (dtree::children)) =
   SND (rename_children ctrs' (SND rs) bbs' succ_map children)` by (
    simp[Once rename_blocks_def, LET_THM]) >>
  (* lookup_block lbl bbs' = SOME bb' *)
  `lookup_block lbl bbs' = SOME bb'` by (
    qpat_x_assum `lookup_block lbl (SND _) = _` mp_tac >>
    simp_tac std_ss [pairTheory.SND]) >>
  (* Get b' from rename_children on children *)
  mp_tac (CONJUNCT2 rename_blocks_lookup_exists) >>
  disch_then (qspecl_then [`children`, `ctrs'`, `SND rs`, `bbs'`,
    `succ_map`, `lbl`, `bb'`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then CHOOSE_TAC >>
  (* phi_refines bb' b' *)
  `phi_refines bb' b'` by (
    mp_tac (CONJUNCT2 rename_preserves_other_phi_refines) >>
    disch_then (qspecl_then [`children`, `ctrs'`, `SND rs`, `bbs'`,
      `succ_map`, `lbl`, `bb'`, `b'`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp[]) >>
  (* Witness b', use transitivity *)
  qexists_tac `b'` >>
  conj_tac >- (
    qpat_assum `SND (rename_children _ _ _ _ (dtree::_)) = _`
      (fn eq => PURE_ONCE_REWRITE_TAC [eq]) >>
    first_assum ACCEPT_TAC) >>
  irule phi_refines_trans >>
  qexists_tac `bb'` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Resume rename_blocks_body_match[some_case]:
  pop_assum mp_tac >> simp_tac std_ss [] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  mp_tac (REWRITE_RULE [pairTheory.FST, pairTheory.SND]
    (Q.SPECL [`dtree`, `(ctrs, stacks)`, `bbs`, `succ_map`,
              `children`, `lbl`, `bb_orig`, `rs_e`]
      rename_children_cons_some_case)) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume rename_blocks_body_match[none_case]:
  pop_assum mp_tac >> simp_tac std_ss [] >> strip_tac >>
  mp_tac (REWRITE_RULE [pairTheory.FST, pairTheory.SND]
    (Q.SPECL [`dtree`, `(ctrs, stacks)`, `bbs`, `succ_map`,
              `children`, `lbl`, `bb_orig`, `rs_entry`]
      rename_children_cons_none_case)) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (* ALOOKUP children_rename_states (FST(rename_blocks ...)) ... *)
    qpat_assum `rename_blocks _ _ _ _ = _`
      (fn eq => PURE_REWRITE_TAC [eq, pairTheory.FST]) >>
    first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Finalise rename_blocks_body_match;

(* ==========================================================================
   Part 7: phi_args_ok_from_pipeline + run_function_ssa_sim
   (Placed after rename_blocks_body_match so non_phi_refines is available)
   ========================================================================== *)

(* dtree labels have blocks in bbs1 *)
Theorem fn_label_in_dtree:
  !df dtree dpo func lbl.
    valid_dom_tree df dtree dpo func /\
    MEM lbl (fn_labels func) ==>
    MEM lbl (dom_tree_labels dtree)
Proof
  rpt strip_tac >>
  `set (dom_tree_labels dtree) = set (fn_labels func)` by
    fs[valid_dom_tree_def] >>
  fs[EXTENSION] >> metis_tac[]
QED

Theorem dtree_labels_have_blocks:
  !dtree func bbs1.
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    phi_extends func.fn_blocks bbs1 /\
    ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks) ==>
    !l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs1 = SOME b
Proof
  rpt strip_tac >>
  `MEM l (fn_labels func)` by (
    `set (dom_tree_labels dtree) = set (fn_labels func)` by
      gvs[valid_dom_tree_def] >>
    fs[EXTENSION] >> metis_tac[]) >>
  fs[fn_labels_def, MEM_MAP] >>
  rename1 `MEM bx func.fn_blocks` >>
  mp_tac phi_extends_lookup >>
  disch_then (qspecl_then [`func.fn_blocks`, `bbs1`, `bx`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> metis_tac[]
QED

Triviality body_inst_match_via_non_phi_refines[local]:
  !phis body rs_b_entry rs_mid bb_renamed bb' n_phi j.
    rs_mid = FST (rename_block_insts rs_b_entry phis) /\
    bb_renamed.bb_instructions =
      SND (rename_block_insts rs_b_entry (phis ++ body)) /\
    n_phi = LENGTH phis /\
    non_phi_refines bb_renamed bb' /\
    j < LENGTH body /\
    (EL j body).inst_opcode <> PHI ==>
    EL (n_phi + j) bb'.bb_instructions =
    SND (rename_inst (FST (rename_block_insts rs_mid (TAKE j body)))
                     (EL j body))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  qpat_x_assum `non_phi_refines _ _` mp_tac >>
  simp[non_phi_refines_def, rename_block_insts_length] >>
  strip_tac >>
  first_x_assum (qspec_then `LENGTH phis + j` mp_tac) >>
  simp[rename_block_insts_el, rename_inst_opcode_preserved,
       EL_APPEND2, rename_block_insts_length] >>
  strip_tac >>
  simp[TAKE_APPEND2] >>
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (Q.SPECL [`phis`, `TAKE j body'`, `rs_b_entry`]
       rename_block_insts_append)) >>
  Cases_on `rename_block_insts rs_b_entry phis` >>
  Cases_on `rename_block_insts q (TAKE j body')` >> simp[]
QED

Triviality phi_refines_from_pipeline[local]:
  !dtree rs0 bbs1 succ_map func lbl bb_mid rs_b_entry bb'.
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    phi_extends func.fn_blocks bbs1 /\
    ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks) /\
    lookup_block lbl bbs1 = SOME bb_mid /\
    MEM lbl (fn_labels func) /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl =
      SOME rs_b_entry /\
    lookup_block lbl (SND (rename_blocks rs0 bbs1 succ_map dtree)) =
      SOME bb' ==>
    phi_refines
      (bb_mid with bb_instructions :=
         SND (rename_block_insts rs_b_entry bb_mid.bb_instructions))
      bb'
Proof
  rpt strip_tac >>
  mp_tac dtree_labels_have_blocks >>
  disch_then (qspecl_then [`dtree`, `func`, `bbs1`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `MEM lbl (dom_tree_labels dtree)` by (
    `set (dom_tree_labels dtree) = set (fn_labels func)` by
      gvs[valid_dom_tree_def] >>
    fs[EXTENSION] >> metis_tac[]) >>
  mp_tac (CONJUNCT1 rename_blocks_body_match) >>
  disch_then (qspecl_then [`dtree`, `rs0`, `bbs1`, `succ_map`,
    `lbl`, `bb_mid`, `rs_b_entry`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- gvs[valid_dom_tree_def]
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  `bb'' = bb'` by gvs[] >>
  gvs[]
QED


(* Helper: renamed output form for PHI instructions in bb'.
   Combines phi_refines + rename_block_insts_el + rename_inst_outputs
   to show that the j-th PHI in bb' has outputs [version_var bv ver]. *)
Triviality phi_renamed_output_form[local]:
  !phis body rs_b_entry bb' bb_mid j bv.
    phi_refines
      (bb_mid with bb_instructions :=
         SND (rename_block_insts rs_b_entry bb_mid.bb_instructions)) bb' /\
    bb_mid.bb_instructions = phis ++ body /\
    j < LENGTH phis /\
    (EL j phis).inst_outputs = [bv] ==>
    (EL j bb'.bb_instructions).inst_outputs =
      [version_var bv
        (SND (push_version
          (FST (rename_block_insts rs_b_entry (TAKE j phis))) bv))] /\
    (EL j bb'.bb_instructions).inst_outputs =
      (EL j (SND (rename_block_insts rs_b_entry phis))).inst_outputs
Proof
  rpt strip_tac
  >> (
    (* Common setup *)
    `j < LENGTH bb_mid.bb_instructions` by simp[] >>
    `(EL j bb'.bb_instructions).inst_outputs =
     (EL j (SND (rename_block_insts rs_b_entry
       bb_mid.bb_instructions))).inst_outputs` by (
      fs[phi_refines_def, rename_block_insts_length]) >>
    `EL j (SND (rename_block_insts rs_b_entry bb_mid.bb_instructions)) =
     SND (rename_inst
       (FST (rename_block_insts rs_b_entry (TAKE j bb_mid.bb_instructions)))
       (EL j bb_mid.bb_instructions))` by simp[rename_block_insts_el] >>
    `TAKE j bb_mid.bb_instructions = TAKE j phis` by
      simp[TAKE_APPEND1] >>
    `EL j bb_mid.bb_instructions = EL j phis` by
      simp[EL_APPEND1] >>
    `(SND (rename_inst
       (FST (rename_block_insts rs_b_entry (TAKE j phis)))
       (EL j phis))).inst_outputs =
     SND (rename_outputs
       (FST (rename_block_insts rs_b_entry (TAKE j phis)))
       (EL j phis).inst_outputs)` by simp[rename_inst_outputs] >>
    gvs[])
  >- (
    (* Conjunct 1: = [version_var bv ver] *)
    simp[rename_outputs_def, LET_THM] >> pairarg_tac >> simp[])
  >> (
    (* Conjunct 2: = EL j (SND (rename_block_insts rs_b_entry phis)).outputs *)
    `EL j (SND (rename_block_insts rs_b_entry phis)) =
     SND (rename_inst
       (FST (rename_block_insts rs_b_entry (TAKE j phis)))
       (EL j phis))` by simp[rename_block_insts_el] >>
    gvs[])
QED

(* Per-element proof for phi_prefix_sim bundled condition.
   bv is an explicit parameter to avoid batch-mode Q-quotation type ambiguity. *)
Triviality phi_prefix_sim_per_element[local]:
  !phis rs_b_entry bb' bb_mid bb s1 sigma prev_lbl live_in func' j bv lbl.
    j < LENGTH phis /\
    EVERY (\i. i.inst_opcode = PHI) phis /\
    (EL j phis).inst_outputs = [bv] /\ colon_free bv /\
    (!j. j < LENGTH phis ==> (EL j bb'.bb_instructions).inst_opcode = PHI) /\
    phi_refines
      (bb_mid with bb_instructions :=
        SND (rename_block_insts rs_b_entry bb_mid.bb_instructions)) bb' /\
    bb_mid.bb_instructions = phis ++ bb.bb_instructions /\
    live_in_scope live_in s1 /\
    phi_bases_live_in live_in func' /\
    lookup_block lbl func'.fn_blocks = SOME bb' /\
    s1.vs_current_bb = lbl /\
    (!inst bvar ver.
       MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI /\
       inst.inst_outputs = [version_var bvar ver] /\ colon_free bvar /\
       s1.vs_prev_bb <> NONE ==>
       resolve_phi (THE s1.vs_prev_bb) inst.inst_operands =
         SOME (Var (sigma bvar))) /\
    s1.vs_prev_bb = SOME prev_lbl /\
    LENGTH phis <= LENGTH bb'.bb_instructions ==>
    (EL j phis).inst_opcode = PHI /\
    (?bv'. (EL j phis).inst_outputs = [bv'] /\ colon_free bv') /\
    (?w. lookup_var (HD (EL j phis).inst_outputs) s1 = SOME w) /\
    (EL j bb'.bb_instructions).inst_opcode = PHI /\
    (EL j bb'.bb_instructions).inst_outputs =
      (EL j (SND (rename_block_insts rs_b_entry phis))).inst_outputs /\
    resolve_phi prev_lbl (EL j bb'.bb_instructions).inst_operands =
      SOME (Var (sigma (HD (EL j phis).inst_outputs)))
Proof
  rpt gen_tac >> strip_tac >>
  (* 1: opcode — from EVERY *)
  (conj_tac >- gvs[EVERY_EL]) >>
  (* 2: ?bv — just witness the existing bv *)
  (conj_tac >- (qexists_tac `bv` >> simp[])) >>
  (* 3: lookup_var — via phi_bases_from_liveness + phi_renamed_output_form *)
  (conj_tac >- (
    PURE_REWRITE_TAC [lookup_var_def] >>
    mp_tac phi_renamed_output_form >>
    disch_then (qspecl_then [`phis`, `bb.bb_instructions`,
      `rs_b_entry`, `bb'`, `bb_mid`, `j`, `bv`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    strip_tac >>
    `lookup_block s1.vs_current_bb func'.fn_blocks = SOME bb'` by
      (ASM_REWRITE_TAC[]) >>
    mp_tac phi_bases_from_liveness >>
    disch_then (qspecl_then [`live_in`, `func'`, `s1`] mp_tac) >>
    (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (qspecl_then [`bb'`, `EL j bb'.bb_instructions`, `bv`,
      `SND (push_version
        (FST (rename_block_insts rs_b_entry (TAKE j phis))) bv)`] mp_tac) >>
    (impl_tac >- (
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      TRY (simp[MEM_EL] >> qexists_tac `j` >> DECIDE_TAC) >>
      TRY (first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
      gvs[MEM])) >>
    strip_tac >>
    gvs[FLOOKUP_DEF])) >>
  (* Get renamed output form for conjuncts 4-6 *)
  mp_tac phi_renamed_output_form >>
  disch_then (qspecl_then [`phis`, `bb.bb_instructions`,
    `rs_b_entry`, `bb'`, `bb_mid`, `j`, `bv`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* 4: bb' opcode *)
  (conj_tac >- (first_x_assum (qspec_then `j` mp_tac) >> simp[])) >>
  (* 5: output equality *)
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (* 6: resolve_phi *)
  qpat_x_assum `!inst bvar ver. _`
    (qspecl_then [`EL j bb'.bb_instructions`, `bv`,
      `SND (push_version
        (FST (rename_block_insts rs_b_entry (TAKE j phis))) bv)`]
     mp_tac) >>
  (impl_tac >- (
    rpt conj_tac >>
    TRY (simp[MEM_EL] >> qexists_tac `j` >> DECIDE_TAC) >>
    TRY (first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
    TRY (gvs[]) >>
    first_assum ACCEPT_TAC)) >>
  `THE s1.vs_prev_bb = prev_lbl` by gvs[] >>
  `HD (EL j phis).inst_outputs = bv` by gvs[] >>
  simp[]
QED

Triviality ssa_sim_inst_idx_update[local]:
  !sigma s1 s2 idx.
    ssa_sim sigma s1 s2 ==> ssa_sim sigma s1 (s2 with vs_inst_idx := idx)
Proof
  rw[ssa_sim_def, lookup_var_def]
QED

Triviality phi_prefix_length_eq_by_el[local]:
  !insts n.
    n <= LENGTH insts /\
    (!j. j < n ==> (EL j insts).inst_opcode = PHI) /\
    (!j. n <= j /\ j < LENGTH insts ==>
      (EL j insts).inst_opcode <> PHI) ==>
    phi_prefix_length insts = n
Proof
  Induct_on `insts`
  >- rw[phi_prefix_length_def] >>
  gen_tac >> Cases_on `n` >> strip_tac
  >- (
    `h.inst_opcode <> PHI` by (
      qpat_x_assum `!j. 0 <= j /\ j < LENGTH (h::insts) ==> _`
        (qspec_then `0` mp_tac) >> simp[]) >>
    simp[phi_prefix_length_def]) >>
  `h.inst_opcode = PHI` by (
    qpat_x_assum `!j. j < SUC n' ==> _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  simp[phi_prefix_length_def] >>
  qpat_x_assum `!n. n <= LENGTH insts /\ _ ==> phi_prefix_length insts = n`
    (qspec_then `n'` mp_tac) >>
  impl_tac >- (
    rpt conj_tac
    >- gvs[]
    >- (rpt strip_tac >>
        qpat_x_assum `!j. j < SUC n' ==> _`
          (qspec_then `SUC j` mp_tac) >> simp[])
    >- (rpt strip_tac >>
        qpat_x_assum `!j. SUC n' <= j /\ _ ==> _`
          (qspec_then `SUC j` mp_tac) >> simp[])) >>
  simp[]
QED

(* Standalone helper for runtime proof — avoids 40+ assumption context *)
Triviality phi_runtime_from_pipeline[local]:
  !phis rs_b_entry bb bb' s1 s2 sigma live_in func' bb_mid lbl.
    ssa_sim sigma s1 s2 /\
    (!x. colon_free x ==> ?n. sigma x = version_var x n) /\
    vars_colon_free s1 /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    EVERY (\i. i.inst_opcode = PHI) phis /\
    LENGTH phis <= LENGTH bb'.bb_instructions /\
    (* Opcode agreement at PHI positions *)
    (!j. j < LENGTH phis ==>
      (EL j bb'.bb_instructions).inst_opcode = PHI) /\
    (* Per-PHI output structure *)
    (!j. j < LENGTH phis ==>
         ?bv. (EL j phis).inst_outputs = [bv] /\ colon_free bv) /\
    (* Non-PHI body after the inserted PHI prefix *)
    (!j. LENGTH phis <= j /\ j < LENGTH bb'.bb_instructions ==>
      (EL j bb'.bb_instructions).inst_opcode <> PHI) /\
    (* Renamed output form — from phi_refines *)
    phi_refines
      (bb_mid with bb_instructions :=
        SND (rename_block_insts rs_b_entry bb_mid.bb_instructions)) bb' /\
    bb_mid.bb_instructions = phis ++ bb.bb_instructions /\
    (* Liveness *)
    live_in_scope live_in s1 /\
    phi_bases_live_in live_in func' /\
    lookup_block lbl func'.fn_blocks = SOME bb' /\
    s1.vs_current_bb = lbl /\
    (* Resolve *)
    (!inst bvar ver.
       MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI /\
       inst.inst_outputs = [version_var bvar ver] /\
       colon_free bvar /\ s1.vs_prev_bb <> NONE ==>
       resolve_phi (THE s1.vs_prev_bb) inst.inst_operands =
         SOME (Var (sigma bvar))) /\
    (* distinct + prev_bb *)
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis)) /\
    (phis <> [] ==> s1.vs_prev_bb <> NONE) ==>
    ?sigma_out.
      (!x. colon_free x ==> ?n. sigma_out x = version_var x n) /\
      (!x. (!i. MEM i phis ==> ~MEM x i.inst_outputs) ==>
           sigma_out x = sigma x) /\
      (!x i. MEM i phis /\ MEM x i.inst_outputs ==>
           sigma_out x =
             latest_version (FST (rename_block_insts rs_b_entry phis)) x) /\
      !fuel ctx.
        ?s2_mid.
          s2_mid.vs_inst_idx = LENGTH phis /\
          ssa_sim sigma_out s1 s2_mid /\
          (s2_mid.vs_halted <=> s2.vs_halted) /\
          s2_mid.vs_current_bb = s2.vs_current_bb /\
          s2_mid.vs_prev_bb = s2.vs_prev_bb /\
          run_block fuel ctx bb' s2 = exec_block fuel ctx bb' s2_mid
Proof
  rpt gen_tac >> strip_tac >>
  `s2.vs_prev_bb = s1.vs_prev_bb` by gvs[ssa_sim_def] >>
  Cases_on `phis = []`
  >- (
    gvs[] >>
    qexists_tac `sigma` >>
    rpt conj_tac >> TRY (simp[rename_block_insts_def]) >>
    rpt gen_tac >>
    qexists_tac `s2` >>
    `EVERY (\inst. inst.inst_opcode <> PHI) bb'.bb_instructions` by (
      simp[EVERY_EL] >> rpt strip_tac >>
      qpat_x_assum `!j. 0 <= j /\ j < LENGTH bb'.bb_instructions ==> _`
        (qspec_then `n` mp_tac) >> simp[]) >>
    simp[run_block_no_phis_eq_exec_block] >>
    gvs[]) >>
  `?prev_lbl. s2.vs_prev_bb = SOME prev_lbl` by (
    `s1.vs_prev_bb <> NONE` by (first_x_assum irule >> simp[]) >>
    Cases_on `s2.vs_prev_bb` >> gvs[]) >>
  mp_tac (Q.SPECL [`phis`, `rs_b_entry`, `bb'.bb_instructions`, `s2`,
    `prev_lbl`, `sigma`, `s1`] phi_prefix_sim) >>
  impl_tac
  >- (
    conj_tac >- gvs[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      qpat_assum `!j. j < LENGTH phis ==> ?bv. _`
        (fn th => STRIP_ASSUME_TAC (UNDISCH (Q.SPEC `j` th))) >>
      mp_tac phi_prefix_sim_per_element >>
      disch_then (qspecl_then [`phis`, `rs_b_entry`, `bb'`, `bb_mid`, `bb`,
        `s1`, `sigma`, `prev_lbl`, `live_in`, `func'`, `j`, `bv`,
        `s1.vs_current_bb`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
      simp[]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `eval_phis s2 bb'.bb_instructions = OK s2_phi` >>
  qexists_tac `sigma_out` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >>
  qexists_tac `s2_phi with vs_inst_idx := LENGTH phis` >>
  `phi_prefix_length bb'.bb_instructions = LENGTH phis` by (
    irule phi_prefix_length_eq_by_el >> simp[]) >>
  rpt conj_tac
  >- simp[]
  >- (irule ssa_sim_inst_idx_update >> first_assum ACCEPT_TAC)
  >- gvs[]
  >- gvs[]
  >- gvs[]
  >- (ONCE_REWRITE_TAC[run_block_def] >> simp[])
QED

(* phi_args_ok_from_pipeline: construct phi_args_ok from pipeline
   structure. bb_mid, rs_b_entry, phis are given as parameters (the caller
   derives them from phi_extends + block_rename_states).
   Coverage is NOT required — sigma_out characterization is output instead. *)
Theorem phi_args_ok_from_pipeline:
  !bb bb' sigma bbs1 dtree succ_map rs0 func func' s1 s2 live_in
   bb_mid rs_b_entry phis dom_frontiers dom_post_order.
    wf_function func /\ fn_inst_wf func /\
    phi_extends func.fn_blocks bbs1 /\
    func'.fn_blocks = SND (rename_blocks rs0 bbs1 succ_map dtree) /\
    valid_phi_operands bbs1 func'.fn_blocks dtree succ_map rs0 /\
    MEM bb func.fn_blocks /\
    lookup_block bb.bb_label func'.fn_blocks = SOME bb' /\
    ssa_sim sigma s1 s2 /\
    (!x. colon_free x ==> ?n. sigma x = version_var x n) /\
    vars_colon_free s1 /\ s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    s1.vs_current_bb = bb.bb_label /\
    live_in_scope live_in s1 /\
    phi_bases_live_in live_in func' /\
    (* PHI resolution *)
    (!inst base ver.
       MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI /\
       inst.inst_outputs = [version_var base ver] /\
       colon_free base /\ s1.vs_prev_bb <> NONE ==>
       resolve_phi (THE s1.vs_prev_bb) inst.inst_operands =
         SOME (Var (sigma base))) /\
    (* Per-instruction wf for original *)
    (!inst. MEM inst bb.bb_instructions ==>
       inst.inst_opcode <> PHI /\
       EVERY colon_free inst.inst_outputs /\
       ALL_DISTINCT inst.inst_outputs /\
       (~opcode_has_output inst.inst_opcode ==> inst.inst_outputs = [])) /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    (* Pipeline block structure — given by caller *)
    lookup_block bb.bb_label bbs1 = SOME bb_mid /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
      bb.bb_label = SOME rs_b_entry /\
    bb_mid.bb_instructions = phis ++ bb.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) phis /\
    (* Per-PHI output structure *)
    (!j. j < LENGTH phis ==>
         ?bv. (EL j phis).inst_outputs = [bv] /\ colon_free bv) /\
    (* Distinct PHI output bases *)
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis)) /\
    (* PHIs only in blocks with predecessor *)
    (phis <> [] ==> s1.vs_prev_bb <> NONE) ==>
    ?sigma_out.
      phi_args_ok bb bb' sigma sigma_out s1 s2
        (FST (rename_block_insts rs_b_entry phis)) /\
      (!x. (!i. MEM i phis ==> ~MEM x i.inst_outputs) ==>
           sigma_out x = sigma x) /\
      (!x i. MEM i phis /\ MEM x i.inst_outputs ==>
           sigma_out x =
             latest_version (FST (rename_block_insts rs_b_entry phis)) x)
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `MEM bb.bb_label (fn_labels func)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  qabbrev_tac `rs_mid = FST (rename_block_insts rs_b_entry phis)` >>
  (* Get phi_refines from pipeline *)
  `lookup_block bb.bb_label (SND (rename_blocks rs0 bbs1 succ_map dtree)) =
     SOME bb'` by (
    qpat_assum `func'.fn_blocks = _` (fn eq =>
      PURE_REWRITE_TAC [GSYM eq]) >>
    first_assum ACCEPT_TAC) >>
  `MEM bb.bb_label (dom_tree_labels dtree)` by
    metis_tac[fn_label_in_dtree] >>
  `!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs1 = SOME b` by (
    mp_tac dtree_labels_have_blocks >>
    disch_then (qspecl_then [`dtree`, `func`, `bbs1`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  `phi_refines
    (bb_mid with bb_instructions :=
       SND (rename_block_insts rs_b_entry bb_mid.bb_instructions))
    bb'` by (
    mp_tac phi_refines_from_pipeline >>
    disch_then (qspecl_then [`dtree`, `rs0`, `bbs1`, `succ_map`, `func`,
      `bb.bb_label`, `bb_mid`, `rs_b_entry`, `bb'`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  `non_phi_refines
    (bb_mid with bb_instructions :=
       SND (rename_block_insts rs_b_entry bb_mid.bb_instructions))
    bb'` by
    metis_tac[phi_refines_implies_non_phi_refines] >>
  (* Get opcodes_preserved for LENGTH + opcode agreement *)
  `opcodes_preserved bbs1 (SND (rename_blocks rs0 bbs1 succ_map dtree))` by
    metis_tac[CONJUNCT1 rename_blocks_opcodes_preserved] >>
  `LENGTH bb'.bb_instructions = LENGTH bb_mid.bb_instructions /\
   !j. j < LENGTH bb_mid.bb_instructions ==>
     (EL j bb'.bb_instructions).inst_opcode =
     (EL j bb_mid.bb_instructions).inst_opcode` by (
    mp_tac opcodes_preserved_lookup >>
    disch_then (qspecl_then [`bbs1`,
      `SND (rename_blocks rs0 bbs1 succ_map dtree)`,
      `bb.bb_label`, `bb_mid`, `bb'`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  `LENGTH bb'.bb_instructions = LENGTH phis + LENGTH bb.bb_instructions`
    by gvs[] >>
  (* Get sigma_out from phi_runtime_from_pipeline *)
  mp_tac phi_runtime_from_pipeline >>
  disch_then (qspecl_then [`phis`, `rs_b_entry`, `bb`, `bb'`, `s1`, `s2`,
    `sigma`, `live_in`, `func'`, `bb_mid`, `bb.bb_label`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- gvs[] >>
    conj_tac >- (
      rpt strip_tac >>
      gvs[EVERY_EL, EL_APPEND1]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      `j < LENGTH bb_mid.bb_instructions` by (
        qpat_x_assum `j < LENGTH bb'.bb_instructions` mp_tac >> gvs[]) >>
      qpat_assum `!j. j < LENGTH bb_mid.bb_instructions ==> _`
        (qspec_then `j` mp_tac) >>
      simp[EL_APPEND2] >>
      `MEM (EL (j - LENGTH phis) bb.bb_instructions) bb.bb_instructions` by
        (simp[MEM_EL] >> qexists_tac `j - LENGTH phis` >> DECIDE_TAC) >>
      qpat_x_assum `!inst. MEM inst bb.bb_instructions ==> _`
        (qspec_then `EL (j - LENGTH phis) bb.bb_instructions` mp_tac) >>
      simp[]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qexists_tac `sigma_out` >>
  (* Prove the three conjuncts *)
  rpt conj_tac
  >- (
    (* phi_args_ok *)
    PURE_REWRITE_TAC [phi_args_ok_def] >>
    qexists_tac `LENGTH phis` >>
    rpt conj_tac
    >- DECIDE_TAC
    >- ( (* PHIs at start *)
      rpt strip_tac >>
      `j < LENGTH bb_mid.bb_instructions` by DECIDE_TAC >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
      gvs[EL_APPEND1, EVERY_EL])
    >- ( (* Non-PHI after n_phi *)
      rpt gen_tac >> strip_tac >>
      `j < LENGTH bb_mid.bb_instructions` by DECIDE_TAC >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
      gvs[EL_APPEND2, EVERY_EL] >>
      `MEM (EL (j - LENGTH phis) bb.bb_instructions) bb.bb_instructions` by
        (simp[MEM_EL] >> qexists_tac `j - LENGTH phis` >> simp[]) >>
      qpat_x_assum `!inst. MEM inst bb.bb_instructions ==> _`
        (qspec_then `EL (j - LENGTH phis) bb.bb_instructions` mp_tac) >>
      simp[])
    >- first_assum ACCEPT_TAC (* LENGTH *)
    >- ( (* Body match *)
      rpt gen_tac >> strip_tac >>
      `LENGTH phis + j < LENGTH bb_mid.bb_instructions` by DECIDE_TAC >>
      `(EL (LENGTH phis + j) bb_mid.bb_instructions).inst_opcode <> PHI` by (
        `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
          (simp[MEM_EL] >> qexists_tac `j` >> simp[]) >>
        qpat_x_assum `!inst. MEM inst bb.bb_instructions ==> _`
          (qspec_then `EL j bb.bb_instructions` mp_tac) >>
        gvs[EL_APPEND2]) >>
      `(EL (LENGTH phis + j)
          (SND (rename_block_insts rs_b_entry
                  bb_mid.bb_instructions))).inst_opcode <> PHI` by
        metis_tac[rename_block_insts_opcodes] >>
      `EL (LENGTH phis + j) bb'.bb_instructions =
       EL (LENGTH phis + j)
         (SND (rename_block_insts rs_b_entry bb_mid.bb_instructions))` by (
        gvs[non_phi_refines_def, rename_block_insts_length] >>
        first_x_assum (qspec_then `LENGTH phis + j` mp_tac) >>
        simp[rename_block_insts_length]) >>
      `EL (LENGTH phis + j)
         (SND (rename_block_insts rs_b_entry bb_mid.bb_instructions)) =
       SND (rename_inst
         (FST (rename_block_insts rs_b_entry
                 (TAKE (LENGTH phis + j) bb_mid.bb_instructions)))
         (EL (LENGTH phis + j) bb_mid.bb_instructions))` by
        simp[rename_block_insts_el] >>
      `TAKE (LENGTH phis + j) bb_mid.bb_instructions =
       phis ++ TAKE j bb.bb_instructions` by (
        gvs[] >> simp[TAKE_APPEND2]) >>
      `EL (LENGTH phis + j) bb_mid.bb_instructions =
       EL j bb.bb_instructions` by gvs[EL_APPEND2] >>
      `FST (rename_block_insts rs_b_entry (phis ++ TAKE j bb.bb_instructions)) =
       FST (rename_block_insts
         (FST (rename_block_insts rs_b_entry phis))
         (TAKE j bb.bb_instructions))` by
        simp[rename_block_insts_fst_append] >>
      gvs[Abbr `rs_mid`])
    >- ( (* No PHIs in original *)
      rpt strip_tac >>
      `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
        (simp[MEM_EL] >> qexists_tac `j` >> simp[]) >>
      qpat_x_assum `!inst. MEM inst bb.bb_instructions ==> _`
        (qspec_then `EL j bb.bb_instructions` mp_tac) >>
      simp[])
    >- first_assum ACCEPT_TAC (* vars_colon_free *)
    >- first_assum ACCEPT_TAC (* sigma_out version_var *)
    >> ( (* Runtime *)
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!fuel ctx. ?s2_mid. _`
        (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
      qexists_tac `s2_mid` >>
      simp[Abbr `rs_mid`]))
  >- first_assum ACCEPT_TAC (* non-PHI preservation *)
  >> (qpat_assum `Abbrev (rs_mid = _)` (fn ab =>
        PURE_REWRITE_TAC [PURE_REWRITE_RULE [markerTheory.Abbrev_def] ab]) >>
      first_assum ACCEPT_TAC)
QED


