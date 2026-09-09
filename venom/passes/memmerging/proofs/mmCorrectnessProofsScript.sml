(*
 * Memmerging — Correctness Definitions and Proofs
 *
 * Definitions (invariants, fresh sets, block wf predicates) and
 * proof infrastructure for the memmerging correctness argument.
 * Re-exported by mmCorrectnessScript.sml.
 *)

Theory mmCorrectnessProofs
Ancestors
  mmTransform mmCopyEquiv passSimulationDefs passSimulationProofs
  crossBlockSimProofs crossBlockSimDefs passSimulationProps stateEquivProps
  stateEquiv stateEquivProofs venomExecSemantics execEquivParamProofs
  analysisSimProofsBase analysisSimDefs venomInstProofs venomWf
  dfgAnalysisProps dfgDefs
  venomInst venomState venomEffects pred_set finite_map
  list rich_list arithmetic words alist
  mmCopy mmScan passSharedField execEquivProps

(* ===== Fresh variables ===== *)

(* Variables whose load instructions get nop'd by the transform.
   These exist in the original execution but not the transformed one. *)
Definition mm_fresh_vars_def:
  mm_fresh_vars fn =
    let dfg = dfg_build_function fn in
    { v | ?bb inst mode.
        MEM bb fn.fn_blocks /\
        MEM inst bb.bb_instructions /\
        inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} /\
        MEM v inst.inst_outputs /\
        (* The load gets nop'd: all uses are within its copy group *)
        load_safe_to_nop dfg v
          (FLAT (MAP (\cg. cg.cg_inst_ids)
                     (scan_block dfg mode bb).ss_flushed)) }
End

(* ===== Per-block fresh variable computation ===== *)

(* Output variables of NOP'd instructions (loads whose results are dead) *)
Definition nop_output_vars_def:
  nop_output_vars dfg nop_ids =
    { v | ?id inst. MEM id nop_ids /\
        dfg_get_inst_by_id dfg id = SOME inst /\
        MEM v inst.inst_outputs }
End

Definition mm_block_fresh_mode_def:
  mm_block_fresh_mode dfg mode bb =
    let groups = (scan_block dfg mode bb).ss_flushed in
    let nop_set = nop_ids_of_groups dfg mode bb.bb_instructions groups in
    let rep_map = rep_map_of_groups bb.bb_instructions groups in
    nop_output_vars dfg nop_set UNION
    { STRCAT "__mm_load_" (toString rep_id) |
        ?(cg : copy_group). ALOOKUP rep_map rep_id = SOME cg /\ cg.cg_length = 32 }
End

(* Fresh variables for memzero sub-pass:
   - NOP'd instruction outputs (empty for zero-stores, but included for generality)
   - Calldatasize variables introduced by representatives with cg_length > 32
     (the transform inserts a calldatasize instruction producing fresh_calldatasize_var) *)
Definition mm_block_fresh_memzero_def:
  mm_block_fresh_memzero dfg bb =
    let groups = (scan_block_memzero dfg bb).mz_flushed in
    let nop_set = nop_ids_of_groups dfg Mem2Mem bb.bb_instructions groups in
    let rep_map = rep_map_of_groups bb.bb_instructions groups in
    nop_output_vars dfg nop_set UNION
    { fresh_calldatasize_var rep_id |
        ?(cg : copy_group). ALOOKUP rep_map rep_id = SOME cg /\ cg.cg_length <> 32 }
End

Definition mm_block_fresh_dload_def:
  mm_block_fresh_dload dfg bb =
    let pairs = find_dload_pairs dfg bb.bb_instructions in
    { v | ?dp inst. MEM dp pairs /\
        dfg_get_inst_by_id dfg dp.dp_dload_id = SOME inst /\
        MEM v inst.inst_outputs }
End

(* Full per-block fresh set: union across all sub-passes.
   Each sub-pass's fresh set is computed on the block AFTER previous
   sub-passes, matching the sequential composition in transform_block. *)
Definition mm_block_fresh_def:
  mm_block_fresh dfg bb =
    let bb1 = transform_block_dload dfg bb in
    let bb2 = transform_block_memzero dfg bb1 in
    let bb3 = transform_block_mode dfg CalldataMerge bb2 in
    let bb4 = transform_block_mode dfg DloadMerge bb3 in
    mm_block_fresh_dload dfg bb UNION
    mm_block_fresh_memzero dfg bb1 UNION
    mm_block_fresh_mode dfg CalldataMerge bb2 UNION
    mm_block_fresh_mode dfg DloadMerge bb3 UNION
    mm_block_fresh_mode dfg Mem2Mem bb4
End

(* ===== Dload pair well-formedness ===== *)

(* The output variable of a dload pair: fresh var produced by DLOAD *)
Definition dp_out_var_def:
  dp_out_var dfg dp =
    case dfg_get_inst_by_id dfg dp.dp_dload_id of
      SOME inst => HD inst.inst_outputs
    | NONE => ""
End

(* A dload pair is well-formed w.r.t. a block's instruction list when:
   1. The DLOAD and MSTORE are in the block at known positions
   2. DLOAD appears before MSTORE (dload_idx < mstore_idx)
   3. The output variable is only written by the DLOAD instruction (SSA)
   4. If dp_src is a Var, it's not overwritten between DLOAD and MSTORE
   5. Single use: dp_out only appears as operand in the MSTORE
   6. DFG consistency: the DFG maps dp_dload_id to the block instruction *)
Definition dload_pair_wf_def:
  dload_pair_wf dfg dp insts <=>
    (* Unique instruction IDs — standard for SSA IRs *)
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    ?dload_inst mstore_inst di mi.
      di < LENGTH insts /\ mi < LENGTH insts /\ di < mi /\
      EL di insts = dload_inst /\ EL mi insts = mstore_inst /\
      dload_inst.inst_id = dp.dp_dload_id /\
      mstore_inst.inst_id = dp.dp_mstore_id /\
      dload_inst.inst_opcode = DLOAD /\
      dload_inst.inst_operands = [dp.dp_src] /\
      dload_inst.inst_outputs = [dp_out_var dfg dp] /\
      mstore_inst.inst_opcode = MSTORE /\
      mstore_inst.inst_operands = [dp.dp_dst; Var (dp_out_var dfg dp)] /\
      (* DFG consistency *)
      dfg_get_inst_by_id dfg dp.dp_dload_id = SOME dload_inst /\
      (* SSA: no other instruction writes to dp_out *)
      (!j. j < LENGTH insts /\ j <> di ==>
        ~MEM (dp_out_var dfg dp) (EL j insts).inst_outputs) /\
      (* Source stability: if dp_src is a Var, nothing between DLOAD
         and MSTORE overwrites it *)
      (!x j. dp.dp_src = Var x /\ di < j /\ j < mi ==>
        ~MEM x (EL j insts).inst_outputs) /\
      (* Single use: only the MSTORE reads dp_out *)
      (!j. j < LENGTH insts /\ j <> mi ==>
        ~MEM (Var (dp_out_var dfg dp)) (EL j insts).inst_operands) /\
      (* dp_src and dp_dst don't alias dp_out (trivially true in SSA) *)
      (!x. dp.dp_src = Var x ==> x <> dp_out_var dfg dp) /\
      (!x. dp.dp_dst = Var x ==> x <> dp_out_var dfg dp)
End

(* ===== Helper lemmas ===== *)

(* Index uniqueness: if inst_ids are ALL_DISTINCT, same id implies same index *)
Theorem all_distinct_inst_id_idx:
  !insts i j.
    ALL_DISTINCT (MAP (\inst. inst.inst_id) insts) /\
    i < LENGTH insts /\ j < LENGTH insts /\
    (EL i insts).inst_id = (EL j insts).inst_id ==>
    i = j
Proof
  rpt strip_tac >>
  `EL i (MAP (\inst. inst.inst_id) insts) =
   EL j (MAP (\inst. inst.inst_id) insts)`
    by simp[EL_MAP] >>
  `i < LENGTH (MAP (\inst. inst.inst_id) insts) /\
   j < LENGTH (MAP (\inst. inst.inst_id) insts)` by simp[] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Label preservation: transforms don't change block labels *)
Theorem transform_block_mode_label[simp]:
  !dfg mode bb.
    (transform_block_mode dfg mode bb).bb_label = bb.bb_label
Proof
  simp[transform_block_mode_def]
QED

Theorem transform_block_memzero_label[simp]:
  !dfg bb.
    (transform_block_memzero dfg bb).bb_label = bb.bb_label
Proof
  simp[transform_block_memzero_def]
QED

Theorem transform_block_dload_label[simp]:
  !dfg bb.
    (transform_block_dload dfg bb).bb_label = bb.bb_label
Proof
  simp[transform_block_dload_def]
QED

Theorem transform_block_label[simp]:
  !dfg bb.
    (transform_block dfg bb).bb_label = bb.bb_label
Proof
  simp[transform_block_def, transform_block_mode_def,
       transform_block_memzero_def, transform_block_dload_def]
QED

(* NOP step is identity *)
Theorem step_inst_nop:
  !fuel ctx inst s.
    step_inst fuel ctx (mk_nop_from inst) s = OK s
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_nop_from_def]
QED

(* NOP is not a terminator *)
Theorem nop_not_terminator[simp]:
  !inst. ~is_terminator (mk_nop_from inst).inst_opcode
Proof
  simp[mk_nop_from_def, is_terminator_def]
QED

(* Monotonicity: weaker relation (larger fresh) preserves lift_result *)
Theorem lift_result_state_equiv_mono:
  !fresh1 fresh2 r1 r2.
    lift_result (state_equiv fresh1) (execution_equiv fresh1) (execution_equiv fresh1) r1 r2 /\
    fresh1 SUBSET fresh2 ==>
    lift_result (state_equiv fresh2) (execution_equiv fresh2) (execution_equiv fresh2) r1 r2
Proof
  rpt strip_tac >>
  irule lift_result_weaken_proof >>
  qexists_tac `state_equiv fresh1` >>
  qexists_tac `execution_equiv fresh1` >>
  qexists_tac `execution_equiv fresh1` >>
  simp[] >> metis_tac[state_equiv_subset, execution_equiv_subset]
QED

(* ===== General helpers ===== *)

(* Chaining Error ∨ lift_result.
   If r1→r2 and r2→r3 are both Error-or-lift_result,
   then r1→r3 is Error-or-lift_result. *)
Theorem eol_chain[local]:
  !fresh r1 r2 r3.
    ((?e. r1 = Error e) \/
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r1 r2) /\
    ((?e. r2 = Error e) \/
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r2 r3) ==>
    (?e. r1 = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r1 r3
Proof
  rpt strip_tac >> gvs[]
  >- (imp_res_tac lift_result_error_left >>
      DISJ1_TAC >> metis_tac[])
  >- (DISJ2_TAC >>
      Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
      gvs[lift_result_def] >>
      metis_tac[state_equiv_trans, execution_equiv_trans])
QED

(* state_equiv fresh is reflexive *)
Theorem state_equiv_refl[simp]:
  !fresh s. state_equiv fresh s s
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

(* execution_equiv fresh is reflexive *)
Theorem execution_equiv_refl[local,simp]:
  !fresh s. execution_equiv fresh s s
Proof
  rw[execution_equiv_def]
QED

(* lift_result reflexivity *)
Theorem lift_result_refl[local]:
  !R_ok R_term R_abort r.
    (!s. R_ok s s) /\ (!s. R_term s s) /\ (!s. R_abort s s) ==>
    lift_result R_ok R_term R_abort r r
Proof
  Cases_on `r` >> rw[lift_result_def]
QED

(* ===== MAP block simulation ===== *)

(* Helper: lift_result for terminator when states are equiv *)
Theorem lift_result_terminator_ok[local]:
  !fresh s1 s2.
    state_equiv fresh s1 s2 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (if s1.vs_halted then Halt s1 else OK s1)
      (if s2.vs_halted then Halt s2 else OK s2)
Proof
  rw[state_equiv_def, execution_equiv_def, lift_result_def]
QED

(* Per-instruction step simulation predicate.
   Says: running inst1 on s1 and inst2 on s2 produces lift_result-related
   results, or the first side errors. Also requires same terminator status. *)
Definition inst_step_sim_def:
  inst_step_sim fresh fuel ctx inst1 inst2 s1 s2 <=>
    (is_terminator inst1.inst_opcode <=> is_terminator inst2.inst_opcode) /\
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (step_inst fuel ctx inst1 s1) (step_inst fuel ctx inst2 s2)
End

(* Helper: induction core for map_block_sim (unconditional lift_result).
   Kept separate from map_block_sim_err_ind because the Error-free case
   has a simpler structure. *)
Theorem map_block_sim_ind[local]:
  !fresh bb1 bb2 fuel ctx.
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!i s1 s2. i < LENGTH bb1.bb_instructions /\
               state_equiv fresh s1 s2 ==>
      inst_step_sim fresh fuel ctx
        (EL i bb1.bb_instructions) (EL i bb2.bb_instructions) s1 s2)
  ==>
  !n sa sb.
    n = LENGTH bb1.bb_instructions - sa.vs_inst_idx /\
    state_equiv fresh sa sb /\
    sa.vs_inst_idx <= LENGTH bb1.bb_instructions ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb1 sa) (exec_block fuel ctx bb2 sb)
Proof
  rpt gen_tac >> strip_tac >>
  Induct >> rpt strip_tac
  >- (`sb.vs_inst_idx = sa.vs_inst_idx` by fs[state_equiv_def] >>
      ONCE_REWRITE_TAC[exec_block_def] >>
      simp[get_instruction_def, lift_result_def])
  >>
  `sb.vs_inst_idx = sa.vs_inst_idx` by fs[state_equiv_def] >>
  `sa.vs_inst_idx < LENGTH bb1.bb_instructions` by fs[] >>
  `sa.vs_inst_idx < LENGTH bb2.bb_instructions` by fs[] >>
  `inst_step_sim fresh fuel ctx
     (EL sa.vs_inst_idx bb1.bb_instructions)
     (EL sa.vs_inst_idx bb2.bb_instructions) sa sb`
    by (qpat_x_assum `!i s1 s2. _ ==> inst_step_sim _ _ _ _ _ _ _`
          (qspecl_then [`sa.vs_inst_idx`, `sa`, `sb`] mp_tac) >>
        simp[]) >>
  fs[inst_step_sim_def] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx (EL sa.vs_inst_idx bb1.bb_instructions) sa` >>
  Cases_on `step_inst fuel ctx (EL sa.vs_inst_idx bb2.bb_instructions) sb` >>
  gvs[lift_result_def] >>
  IF_CASES_TAC >> gvs[]
  >- (irule lift_result_terminator_ok >> simp[]) >>
  imp_res_tac step_inst_preserves_inst_idx >>
  first_x_assum irule >>
  gvs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* General relational block simulation for MAP transforms.
   If two same-length blocks satisfy per-instruction simulation for
   all related states, then exec_block produces related results. *)
Theorem map_block_sim[local]:
  !fresh bb1 bb2 fuel ctx.
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!i s1 s2. i < LENGTH bb1.bb_instructions /\
               state_equiv fresh s1 s2 ==>
      inst_step_sim fresh fuel ctx
        (EL i bb1.bb_instructions) (EL i bb2.bb_instructions) s1 s2)
  ==>
  !s1 s2. state_equiv fresh s1 s2 /\ s1.vs_inst_idx = 0 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >>
  irule map_block_sim_ind >> simp[]
QED

(* ===== Error-tolerant MAP block simulation ===== *)

(* Per-instruction simulation that allows the original to error.
   When original errors, we get the Error disjunct at block level. *)
Definition inst_step_sim_err_def:
  inst_step_sim_err fresh fuel ctx inst1 inst2 s1 s2 <=>
    (is_terminator inst1.inst_opcode <=> is_terminator inst2.inst_opcode) /\
    ((?e. step_inst fuel ctx inst1 s1 = Error e) \/
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
       (step_inst fuel ctx inst1 s1) (step_inst fuel ctx inst2 s2))
End

(* update_var on fresh variable preserves state_equiv with any related state *)
Theorem update_var_fresh_state_equiv_rel[local]:
  !fresh v val s1 s2. v IN fresh /\ state_equiv fresh s1 s2 ==>
    state_equiv fresh (update_var v val s1) s2
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE] >>
  metis_tac[IN_DEF]
QED

(* Induction core for error-tolerant map block simulation.
   Like map_block_sim_ind but per-instruction allows Error disjunct.
   Conclusion: Error ∨ lift_result at block level. *)
Theorem map_block_sim_err_ind[local]:
  !fresh bb1 bb2 fuel ctx.
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!i s1 s2. i < LENGTH bb1.bb_instructions /\
               state_equiv fresh s1 s2 ==>
      inst_step_sim_err fresh fuel ctx
        (EL i bb1.bb_instructions) (EL i bb2.bb_instructions) s1 s2)
  ==>
  !n sa sb.
    n = LENGTH bb1.bb_instructions - sa.vs_inst_idx /\
    state_equiv fresh sa sb /\
    sa.vs_inst_idx <= LENGTH bb1.bb_instructions ==>
    (?e. exec_block fuel ctx bb1 sa = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb1 sa) (exec_block fuel ctx bb2 sb)
Proof
  rpt gen_tac >> strip_tac >>
  Induct >> rpt strip_tac
  >- ((* Base case: idx >= LENGTH *)
      `sb.vs_inst_idx = sa.vs_inst_idx` by fs[state_equiv_def] >>
      ONCE_REWRITE_TAC[exec_block_def] >>
      simp[get_instruction_def, lift_result_def])
  >> (* Step case *)
  `sb.vs_inst_idx = sa.vs_inst_idx` by fs[state_equiv_def] >>
  `sa.vs_inst_idx < LENGTH bb1.bb_instructions` by fs[] >>
  `sa.vs_inst_idx < LENGTH bb2.bb_instructions` by fs[] >>
  `inst_step_sim_err fresh fuel ctx
     (EL sa.vs_inst_idx bb1.bb_instructions)
     (EL sa.vs_inst_idx bb2.bb_instructions) sa sb`
    by (first_x_assum (qspecl_then [`sa.vs_inst_idx`, `sa`, `sb`] mp_tac) >>
        simp[]) >>
  fs[inst_step_sim_err_def]
  >- ((* Original step errors *)
      DISJ1_TAC >>
      ONCE_REWRITE_TAC[exec_block_def] >>
      simp[get_instruction_def] >>
      Cases_on `step_inst fuel ctx (EL sa.vs_inst_idx bb1.bb_instructions) sa` >>
      gvs[])
  >> (* lift_result holds for this step *)
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx (EL sa.vs_inst_idx bb1.bb_instructions) sa` >>
  Cases_on `step_inst fuel ctx (EL sa.vs_inst_idx bb2.bb_instructions) sb` >>
  gvs[lift_result_def] >>
  (* OK/OK case: split on terminator *)
  IF_CASES_TAC >> gvs[]
  >- ((* Terminator *)
      DISJ2_TAC >> irule lift_result_terminator_ok >> simp[])
  >> (* Non-terminator: recurse via IH *)
  imp_res_tac step_inst_preserves_inst_idx >>
  first_x_assum irule >>
  gvs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Entry point: error-tolerant MAP block simulation *)
Theorem map_block_sim_err[local]:
  !fresh bb1 bb2 fuel ctx.
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!i s1 s2. i < LENGTH bb1.bb_instructions /\
               state_equiv fresh s1 s2 ==>
      inst_step_sim_err fresh fuel ctx
        (EL i bb1.bb_instructions) (EL i bb2.bb_instructions) s1 s2)
  ==>
  !s1 s2. state_equiv fresh s1 s2 /\ s1.vs_inst_idx = 0 ==>
    (?e. exec_block fuel ctx bb1 s1 = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >>
  irule map_block_sim_err_ind >> simp[]
QED

(* run_insts on appended lists *)
Theorem run_insts_append[local]:
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

(* Generic FLAT MAP instruction simulation combinator.
   Given a per-instruction simulation property (inst_sim), proves the
   list-level simulation for run_insts vs run_insts on FLAT MAP transform.
   Reusable across memzero, mode, and any other 1:N instruction transform. *)
Theorem flat_map_inst_sim[local]:
  !transform inst_ok inv.
    (!inst fuel ctx s1 s1_mid s2.
       inst_ok inst /\ inv s1 s2 /\
       step_inst fuel ctx inst s1 = OK s1_mid ==>
       ?s2_mid.
         run_insts fuel ctx (transform inst) s2 = OK s2_mid /\
         inv s1_mid s2_mid)
    ==>
    !insts fuel ctx s1 s2.
      inv s1 s2 /\ EVERY inst_ok insts ==>
      (!s'. run_insts fuel ctx insts s1 <> OK s') \/
      ?s1' s2'.
        run_insts fuel ctx insts s1 = OK s1' /\
        run_insts fuel ctx (FLAT (MAP transform insts)) s2 = OK s2' /\
        inv s1' s2'
Proof
  rpt gen_tac >> strip_tac >>
  Induct >- simp[run_insts_def] >>
  rpt strip_tac >>
  rename1 `inst :: insts` >>
  fs[EVERY_DEF] >>
  simp[run_insts_def] >>
  Cases_on `step_inst fuel ctx inst s1` >> simp[]
  >- (
    rename1 `step_inst _ _ inst s1 = OK s1_mid` >>
    simp[run_insts_append] >>
    (* Apply per-instruction sim *)
    first_x_assum (qspecl_then [`inst`, `fuel`, `ctx`, `s1`, `s1_mid`, `s2`]
      mp_tac) >>
    (impl_tac >- fs[]) >>
    strip_tac >>
    (* s2 side OK with inv preserved — apply IH *)
    first_x_assum (qspecl_then [`fuel`, `ctx`, `s1_mid`, `s2_mid`] mp_tac) >>
    (impl_tac >- fs[]) >>
    strip_tac >- (disj1_tac >> simp[]) >>
    disj2_tac >>
    qexistsl_tac [`s1'`, `s2'`] >> simp[])
QED


(* ===== Block simulation ===== *)

(* Each sub-pass preserves block simulation.
   The argument:
   - Between copy groups: instructions are identical
   - Within a copy group: N individual copies ≡ 1 bulk copy (mmCopyEquiv)
   - Fresh vars: load outputs that get nop'd are not used outside group
   - Terminators: preserved (scan doesn't touch terminators) *)

(* ===== inst_wf preservation ===== *)

Theorem inst_wf_mk_nop_from[local,simp]:
  !inst. inst_wf (mk_nop_from inst)
Proof
  simp[EVAL ``inst_wf (mk_nop_from inst)``]
QED

Theorem inst_wf_mk_dloadbytes_inst[local,simp]:
  !inst src dst. inst_wf (mk_dloadbytes_inst inst src dst)
Proof
  simp[EVAL ``inst_wf (mk_dloadbytes_inst inst src dst)``]
QED

Theorem inst_wf_mk_bulk_copy_inst[local,simp]:
  !mode inst cg. inst_wf (mk_bulk_copy_inst mode inst cg)
Proof
  Cases_on `mode` >> simp[EVAL ``inst_wf (mk_bulk_copy_inst CalldataMerge inst cg)``,
                          EVAL ``inst_wf (mk_bulk_copy_inst DloadMerge inst cg)``,
                          EVAL ``inst_wf (mk_bulk_copy_inst Mem2Mem inst cg)``]
QED

Theorem inst_wf_mk_load_inst[local,simp]:
  !mode inst src out. inst_wf (mk_load_inst mode inst src out)
Proof
  Cases_on `mode` >> simp[EVAL ``inst_wf (mk_load_inst CalldataMerge inst src out)``,
                          EVAL ``inst_wf (mk_load_inst DloadMerge inst src out)``,
                          EVAL ``inst_wf (mk_load_inst Mem2Mem inst src out)``]
QED

Theorem inst_wf_mk_mstore_from_load[local,simp]:
  !inst dst load_var. inst_wf (mk_mstore_from_load inst dst load_var)
Proof
  simp[EVAL ``inst_wf (mk_mstore_from_load inst dst load_var)``]
QED

Theorem transform_block_dload_inst_wf:
  !dfg bb. EVERY inst_wf bb.bb_instructions ==>
    EVERY inst_wf (transform_block_dload dfg bb).bb_instructions
Proof
  rw[transform_block_dload_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> rw[] >>
  CASE_TAC >> simp[]
QED

Theorem inst_wf_mk_zero_store_inst[local,simp]:
  !inst dst. inst_wf (mk_zero_store_inst inst dst)
Proof
  simp[EVAL ``inst_wf (mk_zero_store_inst inst dst)``]
QED

Theorem inst_wf_mk_calldatasize_inst[local,simp]:
  !id. inst_wf (mk_calldatasize_inst id)
Proof
  rw[mk_calldatasize_inst_def, inst_wf_def]
QED

Theorem inst_wf_mk_memzero_calldatacopy[local,simp]:
  !inst cg cds_var. inst_wf (mk_memzero_calldatacopy inst cg cds_var)
Proof
  rw[mk_memzero_calldatacopy_def, inst_wf_def]
QED

(* Shared tactic for inst_wf preservation through FLAT MAP transforms.
   Pattern: unfold transform def, extract membership via MEM_FLAT/MEM_MAP,
   expand per-inst function, split IF/CASE in assumptions, close with simp+res_tac. *)
Theorem transform_block_memzero_inst_wf:
  !dfg bb. EVERY inst_wf bb.bb_instructions ==>
    EVERY inst_wf (transform_block_memzero dfg bb).bb_instructions
Proof
  rw[transform_block_memzero_def, EVERY_MEM, MEM_FLAT, MEM_MAP,
     PULL_EXISTS] >>
  rpt strip_tac >>
  fs[apply_memzero_inst_def, LET_THM] >>
  rpt (pop_assum mp_tac) >>
  rpt (IF_CASES_TAC >> simp[]) >>
  rpt (CASE_TAC >> simp[]) >>
  rw[] >> simp[]
QED

Theorem transform_block_mode_inst_wf:
  !dfg mode bb. EVERY inst_wf bb.bb_instructions ==>
    EVERY inst_wf (transform_block_mode dfg mode bb).bb_instructions
Proof
  rw[transform_block_mode_def, EVERY_MEM, MEM_FLAT, MEM_MAP,
     PULL_EXISTS] >>
  rpt strip_tac >>
  fs[apply_groups_inst_def, LET_THM] >>
  rpt (pop_assum mp_tac) >>
  rpt (IF_CASES_TAC >> simp[]) >>
  rpt (CASE_TAC >> simp[]) >>
  rw[] >> simp[]
QED

(* ===== Mode simulation: helpers ===== *)

(* write_memory_with_expansion only changes vs_memory *)
Theorem wmexp_only_changes_memory[local]:
  !offset bytes (s:venom_state).
    (write_memory_with_expansion offset bytes s) with vs_memory :=
      s.vs_memory = s
Proof
  rw[write_memory_with_expansion_def, LET_THM, venom_state_component_equality]
QED

(* General: memory-write-only opcodes only change vs_memory.
   Covers MSTORE, MCOPY, CALLDATACOPY, DLOADBYTES.
   All resolve to write_memory_with_expansion (or mstore which wraps it). *)
Theorem step_mem_write_only_memory[local]:
  !fuel ctx inst s s'.
    inst.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    inst_wf inst /\
    step_inst fuel ctx inst s = OK s' ==>
    s' with vs_memory := s.vs_memory = s
Proof
  rpt strip_tac >> gvs[] >> gvs[inst_wf_def] >>
  gvs[step_inst_non_invoke, step_inst_base_def, is_terminator_def,
      exec_write2_def, mstore_def, mcopy_def, LET_THM] >>
  BasicProvers.every_case_tac >> gvs[wmexp_only_changes_memory] >>
  simp[venom_state_component_equality]
QED

(* General: load opcodes only change vs_vars via update_var.
   Covers MLOAD, CALLDATALOAD, DLOAD. *)
Theorem step_load_only_vars[local]:
  !fuel ctx inst s s'.
    inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} /\
    inst_wf inst /\
    step_inst fuel ctx inst s = OK s' ==>
    ?out val. s' = update_var out val s /\ MEM out inst.inst_outputs
Proof
  rpt strip_tac >> gvs[inst_wf_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  fs[step_inst_non_invoke, step_inst_base_def, is_terminator_def] >>
  Cases_on `inst.inst_operands` >> fs[] >> Cases_on `t` >> fs[] >>
  Cases_on `inst.inst_outputs` >> fs[] >> Cases_on `t` >> fs[] >>
  gvs[exec_read1_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  metis_tac[MEM]
QED

(* ===== Memzero helpers ===== *)

(* For a zero-store instruction, mk_zero_store_inst with the correct
   cg_dst produces the same step_inst result. *)
Theorem mk_zero_store_step_eq[local]:
  !fuel ctx inst dst s.
    is_zero_store inst /\
    operand_lit_val (HD inst.inst_operands) = SOME dst ==>
    step_inst fuel ctx (mk_zero_store_inst inst dst) s =
    step_inst fuel ctx inst s
Proof
  rw[is_zero_store_def, mk_zero_store_inst_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  Cases_on `h` >> fs[operand_lit_val_def] >>
  Cases_on `h'` >> fs[operand_lit_val_def] >>
  gvs[n2w_w2n] >>
  simp[step_inst_non_invoke, step_inst_base_def, is_terminator_def,
       exec_write2_def]
QED

(* apply_memzero_inst for instructions not in nop_set and not in rep_map *)
Theorem apply_memzero_unchanged:
  !nop_set rep_map inst.
    ~MEM inst.inst_id nop_set /\
    ALOOKUP rep_map inst.inst_id = NONE ==>
    apply_memzero_inst nop_set rep_map inst = [inst]
Proof
  simp[apply_memzero_inst_def]
QED

(* apply_groups_inst for instructions not in nop_set and not in rep_map *)
Theorem apply_groups_unchanged:
  !mode nop_set rep_map inst.
    ~MEM inst.inst_id nop_set /\
    ALOOKUP rep_map inst.inst_id = NONE ==>
    apply_groups_inst mode nop_set rep_map inst = [inst]
Proof
  simp[apply_groups_inst_def]
QED


(* apply_groups_inst always returns a non-empty list *)
Theorem apply_groups_inst_nonempty:
  !mode nop_set rep_map inst. apply_groups_inst mode nop_set rep_map inst <> []
Proof
  rw[apply_groups_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt CASE_TAC
QED

(* apply_memzero_inst always returns a non-empty list *)
Theorem apply_memzero_inst_nonempty:
  !nop_set rep_map inst. apply_memzero_inst nop_set rep_map inst <> []
Proof
  rw[apply_memzero_inst_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt CASE_TAC
QED

(* ===== Memzero: helpers ===== *)

(* Non-volatile instructions preserve memory *)
Theorem non_vol_step_preserves_memory[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_volatile_memory inst /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE
    ==>
    s'.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  `Eff_MEMORY NOTIN write_effects inst.inst_opcode` by
    fs[is_volatile_memory_def] >>
  metis_tac[write_effects_sound_memory]
QED

(* ===== Memzero: run_insts level simulation ===== *)

(* Generalized invariant: original state s1 and transformed state s2
   differ only in vs_memory (s1 has pending zero-writes that s2 lacks).
   Non-volatile-memory instructions produce same non-memory result on both. *)
Definition memzero_inv_def:
  memzero_inv fresh s1 s2 <=>
    (* All non-memory fields agree *)
    s1.vs_halted = s2.vs_halted /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    (* Variables agree on non-fresh *)
    (!v. v NOTIN fresh ==> lookup_var v s1 = lookup_var v s2)
End

(* memzero_inv implies state_equiv when memories also agree *)
Theorem memzero_inv_eq_mem_state_equiv[local]:
  !fresh s1 s2. memzero_inv fresh s1 s2 /\ s1.vs_memory = s2.vs_memory ==>
    state_equiv fresh s1 s2
Proof
  rw[memzero_inv_def, state_equiv_def, execution_equiv_def]
QED

(* memzero_inv implies state_equiv between memory-swapped s1 and s2 *)
Theorem memzero_inv_mem_swap_state_equiv[local]:
  !fresh s1 s2.
    memzero_inv fresh s1 s2 ==>
    state_equiv fresh (s1 with vs_memory := s2.vs_memory) s2
Proof
  rw[memzero_inv_def, state_equiv_def, execution_equiv_def,
     lookup_var_def]
QED

(* Reverse direction: swap s2's memory to s1's *)
Theorem memzero_inv_mem_swap_state_equiv_rev[local]:
  !fresh s1 s2.
    memzero_inv fresh s1 s2 ==>
    state_equiv fresh s1 (s2 with vs_memory := s1.vs_memory)
Proof
  rw[memzero_inv_def, state_equiv_def, execution_equiv_def,
     lookup_var_def]
QED

(* memzero_inv from state_equiv between memory-swapped states *)
Theorem state_equiv_mem_swap_memzero_inv[local]:
  !fresh s1' s2'.
    state_equiv fresh (s1' with vs_memory := s2'.vs_memory) s2' ==>
    memzero_inv fresh s1' s2'
Proof
  rw[memzero_inv_def, state_equiv_def, execution_equiv_def,
     lookup_var_def]
QED

(* memzero_inv is reflexive *)
Theorem memzero_inv_refl[local]:
  !fresh s. memzero_inv fresh s s
Proof
  rw[memzero_inv_def]
QED

(* KEY ABSTRACTION: memzero_inv doesn't mention vs_memory, so arbitrary
   memory changes on BOTH sides preserve it. This subsumes all
   memory-write-only invariant preservation lemmas. *)
Theorem memzero_inv_memory_irrelevant[local]:
  !fresh s1 s2 m1 m2.
    memzero_inv fresh s1 s2 ==>
    memzero_inv fresh (s1 with vs_memory := m1) (s2 with vs_memory := m2)
Proof
  rw[memzero_inv_def, lookup_var_def]
QED

(* Corollary: changing only s1's memory preserves memzero_inv *)
Theorem memzero_inv_change_mem_left[local]:
  !fresh s1 s2 m1.
    memzero_inv fresh s1 s2 ==>
    memzero_inv fresh (s1 with vs_memory := m1) s2
Proof
  rpt strip_tac >>
  `s2 = s2 with vs_memory := s2.vs_memory` by simp[venom_state_component_equality] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  irule memzero_inv_memory_irrelevant >> simp[]
QED

(* Both sides only changed memory → memzero_inv preserved.
   This is the workhorse for all rep-case proofs. *)
Theorem mem_write_both_preserves_memzero_inv[local]:
  !fresh s1 s2 s1' s2'.
    memzero_inv fresh s1 s2 /\
    (s1' with vs_memory := s1.vs_memory = s1) /\
    (s2' with vs_memory := s2.vs_memory = s2) ==>
    memzero_inv fresh s1' s2'
Proof
  rpt strip_tac >>
  gvs[venom_state_component_equality] >>
  fs[memzero_inv_def, lookup_var_def]
QED

(* Writing a fresh variable preserves memzero_inv *)
Theorem memzero_inv_update_fresh_var[local]:
  !fresh s1 s2 v val.
    memzero_inv fresh s1 s2 /\ v IN fresh ==>
    memzero_inv fresh s1 (update_var v val s2)
Proof
  rpt strip_tac >>
  gvs[memzero_inv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `v <> v'` by metis_tac[IN_DEF] >> gvs[]
QED

(* General: any memory-write-only opcode preserves memzero_inv when NOP'd.
   The original instruction only changes vs_memory; the NOP does nothing. *)
Theorem nop_mem_write_preserves_memzero_inv[local]:
  !fuel ctx inst s1 s2 s1' fresh.
    memzero_inv fresh s1 s2 /\ inst_wf inst /\
    inst.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
    step_inst fuel ctx inst s1 = OK s1'
    ==>
    memzero_inv fresh s1' s2
Proof
  rpt strip_tac >>
  `s1' with vs_memory := s1.vs_memory = s1` by
    (irule step_mem_write_only_memory >> metis_tac[]) >>
  qpat_x_assum `_ = s1` (strip_assume_tac o
    SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  fs[memzero_inv_def, lookup_var_def]
QED

(* NOP'd load preserves memzero_inv when all outputs are fresh.
   The original load writes to fresh variable(s); the NOP does nothing.
   memzero_inv only tracks non-fresh variables, so the difference is invisible. *)
Theorem nop_load_preserves_memzero_inv[local]:
  !fuel ctx inst s1 s2 s1' fresh.
    memzero_inv fresh s1 s2 /\ inst_wf inst /\
    inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} /\
    EVERY (\v. v IN fresh) inst.inst_outputs /\
    step_inst fuel ctx inst s1 = OK s1'
    ==>
    memzero_inv fresh s1' s2
Proof
  rpt strip_tac >>
  drule_all step_load_only_vars >> strip_tac >>
  gvs[update_var_def] >>
  fs[memzero_inv_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rw[] >>
  gvs[EVERY_MEM]
QED

(* Operand agreement under memzero_inv: if operands avoid fresh vars,
   eval_operand gives the same result on both states. *)
Theorem memzero_inv_eval_operand[local]:
  !fresh s1 s2 op.
    memzero_inv fresh s1 s2 /\
    (!x. op = Var x ==> x NOTIN fresh) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def] >>
  fs[memzero_inv_def]
QED

(* Key: for non-volatile instructions whose operands avoid fresh vars,
   step_inst OK on s1 implies step_inst OK on s2 with memzero_inv preserved
   and memory unchanged on both sides.
   Proof: compose step_inst_mem_frame (memory swap) with
   step_inst_base_result_equiv (variable equivalence). *)
(* Combined non-volatile step result under memzero_inv.
   OK case: both succeed with memzero_inv preserved and memory preserved.
   Fail case: s1 fails iff s2 fails.
   This replaces separate OK-sim and error-propagation for unchanged insts. *)
Theorem non_vol_step_memzero_result[local]:
  !fuel ctx inst s1 s2 fresh.
    memzero_inv fresh s1 s2 /\
    ~is_volatile_memory inst /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh)
    ==>
    (!s1'. step_inst fuel ctx inst s1 = OK s1' ==>
      ?s2'. step_inst fuel ctx inst s2 = OK s2' /\
            memzero_inv fresh s1' s2' /\
            s1'.vs_memory = s1.vs_memory /\
            s2'.vs_memory = s2.vs_memory) /\
    ((!s1'. step_inst fuel ctx inst s1 <> OK s1') ==>
     (!s2'. step_inst fuel ctx inst s2 <> OK s2')) /\
    ((!s2'. step_inst fuel ctx inst s2 <> OK s2') ==>
     (!s1'. step_inst fuel ctx inst s1 <> OK s1'))
Proof
  rpt strip_tac >>
  `Eff_MEMORY NOTIN write_effects inst.inst_opcode` by
    fs[is_volatile_memory_def] >>
  rpt conj_tac
  >- ( (* OK case: s1 OK => s2 OK + memzero_inv preserved *)
    rpt strip_tac >>
    `s1'.vs_memory = s1.vs_memory` by metis_tac[write_effects_sound_memory] >>
    `step_inst fuel ctx inst (s1 with vs_memory := s2.vs_memory) =
     OK (s1' with vs_memory := s2.vs_memory)` by (
      irule step_inst_mem_frame >> metis_tac[]) >>
    `step_inst_base inst (s1 with vs_memory := s2.vs_memory) =
     OK (s1' with vs_memory := s2.vs_memory)` by
      gvs[step_inst_non_invoke] >>
    `state_equiv fresh (s1 with vs_memory := s2.vs_memory) s2` by
      metis_tac[memzero_inv_mem_swap_state_equiv] >>
    `result_equiv fresh
      (step_inst_base inst (s1 with vs_memory := s2.vs_memory))
      (step_inst_base inst s2)` by (
      irule step_inst_base_result_equiv >> simp[] >> metis_tac[]) >>
    Cases_on `step_inst_base inst s2` >>
    gvs[result_equiv_def] >>
    rename1 `step_inst_base inst s2 = OK s2'` >>
    `step_inst fuel ctx inst s2 = OK s2'` by gvs[step_inst_non_invoke] >>
    `s2'.vs_memory = s2.vs_memory` by metis_tac[write_effects_sound_memory] >>
    qexists_tac `s2'` >> gvs[step_inst_non_invoke] >>
    irule state_equiv_mem_swap_memzero_inv >> simp[])
  >- ( (* s1 fail => s2 fail: contrapositive — if s2 OK then s1 OK *)
    rpt strip_tac >>
    (* mem_frame: s2 OK => (s2 with mem := s1.mem) OK *)
    `step_inst fuel ctx inst (s2 with vs_memory := s1.vs_memory) =
     OK (s2' with vs_memory := s1.vs_memory)` by (
      irule step_inst_mem_frame >> metis_tac[]) >>
    (* state_equiv s1 (s2{mem:=s1.mem}) from memzero_inv *)
    `state_equiv fresh s1 (s2 with vs_memory := s1.vs_memory)` by
      metis_tac[memzero_inv_mem_swap_state_equiv_rev] >>
    (* result_equiv between step_inst_base on s1 vs s2{mem:=s1.mem} *)
    `result_equiv fresh
      (step_inst_base inst s1)
      (step_inst_base inst (s2 with vs_memory := s1.vs_memory))` by (
      irule step_inst_base_result_equiv >> simp[] >> metis_tac[]) >>
    (* s2{mem:=s1.mem} side is OK at step_inst_base level *)
    `step_inst_base inst (s2 with vs_memory := s1.vs_memory) =
     OK (s2' with vs_memory := s1.vs_memory)` by
      gvs[step_inst_non_invoke] >>
    (* so s1 side must be OK too *)
    Cases_on `step_inst_base inst s1` >>
    gvs[result_equiv_def, step_inst_non_invoke])
  >- ( (* s2 fail => s1 fail: contrapositive — if s1 OK then s2 OK *)
    rpt strip_tac >>
    (* mem_frame: s1 OK => (s1 with mem := s2.mem) OK *)
    `step_inst fuel ctx inst (s1 with vs_memory := s2.vs_memory) =
     OK (s1' with vs_memory := s2.vs_memory)` by (
      irule step_inst_mem_frame >> metis_tac[]) >>
    `state_equiv fresh (s1 with vs_memory := s2.vs_memory) s2` by
      metis_tac[memzero_inv_mem_swap_state_equiv] >>
    `result_equiv fresh
      (step_inst_base inst (s1 with vs_memory := s2.vs_memory))
      (step_inst_base inst s2)` by (
      irule step_inst_base_result_equiv >> simp[] >> metis_tac[]) >>
    `step_inst_base inst (s1 with vs_memory := s2.vs_memory) =
     OK (s1' with vs_memory := s2.vs_memory)` by
      gvs[step_inst_non_invoke] >>
    Cases_on `step_inst_base inst s2` >>
    gvs[result_equiv_def, step_inst_non_invoke])
QED

(* Backward-compat wrapper: OK case only (used by callers of old non_vol_step_memzero_inv) *)
Theorem non_vol_step_memzero_inv[local]:
  !fuel ctx inst s1 s1' s2 fresh.
    memzero_inv fresh s1 s2 /\
    ~is_volatile_memory inst /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    step_inst fuel ctx inst s1 = OK s1'
    ==>
    ?s2'. step_inst fuel ctx inst s2 = OK s2' /\
          memzero_inv fresh s1' s2' /\
          s1'.vs_memory = s1.vs_memory /\
          s2'.vs_memory = s2.vs_memory
Proof
  rpt strip_tac >>
  drule_all non_vol_step_memzero_result >> strip_tac >>
  metis_tac[]
QED


(* MSTORE preserves memzero_inv.
   MSTORE only changes vs_memory on both sides.
   Since operands agree (operands avoid fresh, memzero_inv gives lookup agreement),
   exec_write2 succeeds on s2 whenever it succeeds on s1.
   All non-memory fields unchanged → memzero_inv preserved. *)
Theorem mstore_preserves_memzero_inv[local]:
  !fuel ctx inst s1 s2 s1' fresh.
    memzero_inv fresh s1 s2 /\
    inst.inst_opcode = MSTORE /\ inst_wf inst /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    step_inst fuel ctx inst s1 = OK s1'
    ==>
    ?s2'. step_inst fuel ctx inst s2 = OK s2' /\
          memzero_inv fresh s1' s2'
Proof
  rpt strip_tac >>
  (* Operands: inst_wf + MSTORE gives [a; b] *)
  `LENGTH inst.inst_operands = 2` by gvs[inst_wf_def] >>
  `?a b. inst.inst_operands = [a; b]` by
    (Cases_on `inst.inst_operands` >> fs[] >> Cases_on `t` >> fs[]) >>
  (* Expand s1's MSTORE step to get concrete operand values *)
  qpat_x_assum `step_inst _ _ _ s1 = OK s1'` mp_tac >>
  simp[step_inst_non_invoke, is_terminator_def, step_inst_base_def, exec_write2_def] >>
  Cases_on `eval_operand a s1` >> simp[] >>
  Cases_on `eval_operand b s1` >> simp[] >>
  strip_tac >>
  (* Operand agreement via memzero_inv_eval_operand *)
  `eval_operand a s2 = SOME x` by
    (`eval_operand a s1 = eval_operand a s2` by
       (irule memzero_inv_eval_operand >> qexists_tac `fresh` >>
        simp[] >> metis_tac[]) >> fs[]) >>
  `eval_operand b s2 = SOME x'` by
    (`eval_operand b s1 = eval_operand b s2` by
       (irule memzero_inv_eval_operand >> qexists_tac `fresh` >>
        simp[] >> metis_tac[]) >> fs[]) >>
  (* s2 steps to mstore (w2n x) x' s2 *)
  qexists_tac `mstore (w2n x) x' s2` >>
  simp[step_inst_non_invoke, is_terminator_def, step_inst_base_def, exec_write2_def] >>
  (* memzero_inv: mstore only changes memory *)
  gvs[memzero_inv_def, mstore_def, LET_THM, lookup_var_def]
QED

(* ===== Mode simulation: per-instruction ===== *)

(* Instruction classification for mode transform. *)
Definition mode_inst_ok_def:
  mode_inst_ok nop_set rep_map fresh inst <=>
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (* NOP'd instructions have literal operands (always succeed) *)
    (MEM inst.inst_id nop_set ==>
       EVERY (\op. ?v. op = Lit v) inst.inst_operands) /\
    (* NOP'd memory-write instructions *)
    (MEM inst.inst_id nop_set /\
     inst.inst_opcode NOTIN {MLOAD; CALLDATALOAD; DLOAD} ==>
       inst.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}) /\
    (* NOP'd load instructions: outputs are fresh *)
    (MEM inst.inst_id nop_set /\
     inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} ==>
       EVERY (\v. v IN fresh) inst.inst_outputs) /\
    (* Identity instructions: non-volatile, don't read/write memory, non-aborting *)
    (~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = NONE ==>
       ~is_volatile_memory inst /\
       Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
       ~is_alloca_op inst.inst_opcode /\
       ~is_ext_call_op inst.inst_opcode /\
       inst.inst_opcode <> ASSERT /\
       inst.inst_opcode <> ASSERT_UNREACHABLE) /\
    (* Rep instructions: memory-write opcodes with literal operands *)
    (!cg. ALOOKUP rep_map inst.inst_id = SOME cg ==>
       inst.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}) /\
    (!cg. ALOOKUP rep_map inst.inst_id = SOME cg ==>
       EVERY (\op. ?v. op = Lit v) inst.inst_operands) /\
    (* Rep load_var is fresh (needed for mk_load_inst + mk_mstore_from_load path) *)
    (!cg. ALOOKUP rep_map inst.inst_id = SOME cg /\ cg.cg_length = 32 ==>
       STRCAT "__mm_load_" (toString inst.inst_id) IN fresh) /\
    (* Fresh variables not used in operands *)
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh)
End

(* mode_block_wf: bundles all per-block conditions needed for mode sub-pass
   simulation. Analogous to memzero_block_wf. *)
Definition mode_block_wf_def:
  mode_block_wf dfg mode bb <=>
    let scan_result = scan_block dfg mode bb in
    let groups = scan_result.ss_flushed in
    let nop_set = nop_ids_of_groups dfg mode bb.bb_instructions groups in
    let rep_map = rep_map_of_groups bb.bb_instructions groups in
    let non_terms = FILTER (\i. ~is_terminator i.inst_opcode)
                      bb.bb_instructions in
    (* Terminator not in scan results *)
    ~MEM (LAST bb.bb_instructions).inst_id nop_set /\
    ALOOKUP rep_map (LAST bb.bb_instructions).inst_id = NONE /\
    (* Transformed non-terms are all non-terminator non-INVOKE *)
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP (apply_groups_inst mode nop_set rep_map) non_terms)) /\
    (* Per-instruction WF for simulation *)
    (!fresh. mm_block_fresh_mode dfg mode bb SUBSET fresh ==>
       EVERY (mode_inst_ok nop_set rep_map fresh) non_terms) /\
    (* Memory convergence: original and transformed produce same memory.
       Follows from group coverage properties of the scanner. *)
    (!fuel ctx s0 s1 s2.
       run_insts fuel ctx non_terms s0 = OK s1 /\
       run_insts fuel ctx
         (FLAT (MAP (apply_groups_inst mode nop_set rep_map) non_terms))
         s0 = OK s2
       ==> s1.vs_memory = s2.vs_memory)
End

(* Per-instruction simulation for mode transform.
   Three cases: NOP'd, identity, representative. *)
Theorem mode_inst_step_sim[local]:
  !nop_set rep_map fresh mode inst fuel ctx s1 s1_mid s2.
    mode_inst_ok nop_set rep_map fresh inst /\
    memzero_inv fresh s1 s2 /\
    step_inst fuel ctx inst s1 = OK s1_mid
    ==>
    ?s2_mid.
      run_insts fuel ctx (apply_groups_inst mode nop_set rep_map inst) s2
        = OK s2_mid /\
      memzero_inv fresh s1_mid s2_mid
Proof
  rpt strip_tac >>
  gvs[mode_inst_ok_def] >>
  Cases_on `MEM inst.inst_id nop_set` >>
  gvs[apply_groups_inst_def] >>
  simp[run_insts_def, LET_THM]
  >| [suspend "nop", suspend "non_nop"]
QED

Resume mode_inst_step_sim[nop]:
  simp[step_inst_nop] >>
  Cases_on `inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD}` >| [
    (* Load case *)
    SUBGOAL_THEN ``EVERY (\v. v IN fresh) inst.inst_outputs``
      ASSUME_TAC THENL [res_tac >> gvs[], ALL_TAC] >>
    drule_all nop_load_preserves_memzero_inv >> simp[],
    (* Mem-write case *)
    SUBGOAL_THEN ``inst.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}``
      ASSUME_TAC THENL [res_tac >> gvs[], ALL_TAC] >>
    drule_all nop_mem_write_preserves_memzero_inv >> simp[]
  ]
QED

(* mk_bulk_copy_inst succeeds on any state and only changes memory *)
Theorem bulk_copy_step[local]:
  !fuel ctx mode inst cg s.
    ?s'. step_inst fuel ctx (mk_bulk_copy_inst mode inst cg) s = OK s' /\
         s' with vs_memory := s.vs_memory = s
Proof
  rpt gen_tac >>
  Cases_on `mode` >> (
    simp[mk_bulk_copy_inst_def, mode_copy_opcode_def] >>
    simp[step_inst_non_invoke, step_inst_base_def,
         is_terminator_def, eval_operand_def,
         mcopy_def, LET_THM] >>
    simp[wmexp_only_changes_memory]
  )
QED

(* mk_load_inst succeeds (mode <> DloadMerge) and only adds a variable *)
Theorem load_inst_step[local]:
  !fuel ctx mode inst src_addr out_var s.
    mode <> DloadMerge ==>
    ?val. step_inst fuel ctx (mk_load_inst mode inst src_addr out_var) s =
          OK (update_var out_var val s)
Proof
  rpt strip_tac >>
  Cases_on `mode` >> gvs[] >>
  simp[mk_load_inst_def, mode_load_opcode_def,
       step_inst_non_invoke, step_inst_base_def,
       is_terminator_def, eval_operand_def,
       exec_read1_def, update_var_def] >>
  metis_tac[]
QED

(* mk_mstore_from_load succeeds when load_var is defined, only changes memory *)
Theorem mstore_from_load_step[local]:
  !fuel ctx inst dst_addr load_var s.
    FLOOKUP s.vs_vars load_var <> NONE ==>
    ?s'. step_inst fuel ctx (mk_mstore_from_load inst dst_addr load_var) s = OK s' /\
         s' with vs_memory := s.vs_memory = s
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_vars load_var` >> gvs[] >>
  simp[mk_mstore_from_load_def,
       step_inst_non_invoke, step_inst_base_def,
       is_terminator_def, exec_write2_def, eval_operand_def,
       lookup_var_def, mstore_def, LET_THM] >>
  simp[wmexp_only_changes_memory, venom_state_component_equality]
QED

Resume mode_inst_step_sim[non_nop]:
  Cases_on `ALOOKUP rep_map inst.inst_id`
  >| [suspend "none_case", suspend "some_case"]
QED

Resume mode_inst_step_sim[none_case]:
  (* ALOOKUP = NONE: identity — non-volatile step *)
  gvs[] >>
  simp[run_insts_def, LET_THM] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `s1_mid`, `s2`, `fresh`]
    mp_tac non_vol_step_memzero_inv >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexists_tac `s2'` >> simp[]
QED

Resume mode_inst_step_sim[some_case]:
  (* ALOOKUP = SOME x: simplify case expr, derive mem-only, suspend *)
  simp[] >>
  suspend "some_main"
QED

Resume mode_inst_step_sim[some_main]:
  (* Derive: s1_mid only changed memory *)
  qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `s1_mid`]
    mp_tac step_mem_write_only_memory >>
  (impl_tac >- (fs[] >> simp[])) >>
  strip_tac >>
  (* Split by cg_length without expanding opcode disjunction *)
  reverse (Cases_on `x.cg_length = 32`)
  >| [suspend "bulk", suspend "len32"]
QED

Resume mode_inst_step_sim[bulk]:
  (* cg_length <> 32: bulk_copy *)
  simp[run_insts_def, LET_THM] >>
  qspecl_then [`fuel`, `ctx`, `mode`, `inst`, `x`, `s2`]
    strip_assume_tac bulk_copy_step >>
  qexists_tac `s'` >> simp[] >>
  irule mem_write_both_preserves_memzero_inv >>
  qexistsl_tac [`s1`, `s2`] >> simp[]
QED

Resume mode_inst_step_sim[len32]:
  (* cg_length = 32: simplify first IF, split by DloadMerge *)
  simp[] >>
  reverse (Cases_on `mode = DloadMerge`)
  >| [suspend "not_dload", suspend "dload_bulk"]
QED

Resume mode_inst_step_sim[dload_bulk]:
  (* DloadMerge + 32B: bulk_copy *)
  simp[run_insts_def, LET_THM] >>
  qspecl_then [`fuel`, `ctx`, `DloadMerge`, `inst`, `x`, `s2`]
    strip_assume_tac bulk_copy_step >>
  qexists_tac `s'` >> simp[] >>
  irule mem_write_both_preserves_memzero_inv >>
  qexistsl_tac [`s1`, `s2`] >> simp[]
QED

Resume mode_inst_step_sim[not_dload]:
  (* 32B, not DloadMerge: MSTORE identity or load+mstore *)
  simp[] >>
  reverse (Cases_on `inst.inst_opcode = MSTORE`)
  >| [suspend "load_mstore", suspend "mstore_id"]
QED

Resume mode_inst_step_sim[mstore_id]:
  (* MSTORE 32B identity: run [inst] on s2 *)
  simp[run_insts_def, LET_THM] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `s2`, `s1_mid`, `fresh`]
    mp_tac mstore_preserves_memzero_inv >>
  (impl_tac >- gvs[]) >>
  strip_tac >> qexists_tac `s2'` >> simp[]
QED

Resume mode_inst_step_sim[load_mstore]:
  (* Load + mstore (MCOPY/CALLDATACOPY/DLOADBYTES, 32B, not DloadMerge) *)
  (* Specialize ∀cg assumptions first *)
  `STRCAT "__mm_load_" (toString inst.inst_id) IN fresh` by (
    first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
  qabbrev_tac `lv = STRCAT "__mm_load_" (toString inst.inst_id)` >>
  (* Step 1: load succeeds *)
  `?val. step_inst fuel ctx (mk_load_inst mode inst x.cg_src lv) s2 =
     OK (update_var lv val s2)` by (
    irule load_inst_step >> simp[]) >>
  (* Step 2: mstore succeeds, only changes memory *)
  `?s2_fin. step_inst fuel ctx (mk_mstore_from_load inst x.cg_dst lv)
     (update_var lv val s2) = OK s2_fin /\
     s2_fin with vs_memory := (update_var lv val s2).vs_memory =
     update_var lv val s2` by (
    irule mstore_from_load_step >>
    simp[update_var_def, FLOOKUP_UPDATE]) >>
  (* Derive run_insts and memzero_inv, suspend both for inspection *)
  suspend "finish"
QED

Resume mode_inst_step_sim[finish]:
  (* Normalize: resolve IF, expand lv, normalize all strings *)
  simp[] >>
  qunabbrev_tac `lv` >>
  gvs[stringTheory.STRCAT_def] >>
  (* All 3 opcode cases: resolve run_insts, then prove memzero_inv *)
  simp[run_insts_def] >>
  irule mem_write_both_preserves_memzero_inv >>
  qexistsl_tac [`s1`, `update_var
    (STRCAT "__mm_load_" (toString inst.inst_id)) val s2`] >>
  gvs[stringTheory.STRCAT_def] >>
  irule memzero_inv_update_fresh_var >> fs[]
QED

Finalise mode_inst_step_sim;

(* List-level simulation via flat_map_inst_sim *)
Theorem mode_run_insts_sim[local]:
  !nop_set rep_map fresh mode insts fuel ctx s1 s2.
    memzero_inv fresh s1 s2 /\
    EVERY (mode_inst_ok nop_set rep_map fresh) insts
    ==>
    (!s'. run_insts fuel ctx insts s1 <> OK s') \/
    ?s1' s2'.
      run_insts fuel ctx insts s1 = OK s1' /\
      run_insts fuel ctx
        (FLAT (MAP (apply_groups_inst mode nop_set rep_map) insts)) s2
        = OK s2' /\
      memzero_inv fresh s1' s2'
Proof
  rpt strip_tac >>
  qspecl_then [`apply_groups_inst mode nop_set rep_map`,
               `mode_inst_ok nop_set rep_map fresh`,
               `memzero_inv fresh`]
    mp_tac flat_map_inst_sim >>
  (impl_tac >- metis_tac[mode_inst_step_sim]) >>
  disch_then (qspecl_then [`insts`, `fuel`, `ctx`, `s1`, `s2`] mp_tac) >>
  (impl_tac >- fs[]) >> simp[]
QED

(* mode_run_insts_lift_result and mm_block_simulates_mode are after
   flat_map_same_start_block_bridge and bb_wf_decompose below. *)

(* mm_block_simulates_mode: proved in mmBlockSimScript as
   mm_block_simulates_mode_proof. No forward declaration needed. *)

(* Generalized run_insts simulation for memzero transform.
   Starts from memzero_inv-related states (needed for within-group induction).
   Within groups: NOP'd stores cause memory divergence, non_vol_step preserves inv.
   Group-end representative reconverges memory; memzero_inv + mem_eq = state_equiv.

   For the top-level call: both sides start from same state s,
   so memzero_inv_refl gives the precondition, and the conclusion gives
   memzero_inv which combined with memory equality gives state_equiv. *)

Definition memzero_inst_ok_def:
  memzero_inst_ok nop_set rep_map fresh inst <=>
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (* NOP'd instructions are zero-stores *)
    (MEM inst.inst_id nop_set ==> is_zero_store inst) /\
    (* Unchanged instructions are non-volatile-memory, don't read memory, non-aborting *)
    (~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = NONE ==>
       ~is_volatile_memory inst /\
       Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
       ~is_alloca_op inst.inst_opcode /\
       ~is_ext_call_op inst.inst_opcode /\
       inst.inst_opcode <> ASSERT /\
       inst.inst_opcode <> ASSERT_UNREACHABLE) /\
    (* 32B reps are zero-stores with matching dst *)
    (!cg. ALOOKUP rep_map inst.inst_id = SOME cg /\ cg.cg_length = 32 ==>
       is_zero_store inst /\
       operand_lit_val (HD inst.inst_operands) = SOME cg.cg_dst) /\
    (* >32B reps are zero-stores with fresh calddatasize variable *)
    (!cg. ALOOKUP rep_map inst.inst_id = SOME cg /\ cg.cg_length <> 32 ==>
       is_zero_store inst /\
       fresh_calldatasize_var inst.inst_id IN fresh) /\
    (* Fresh variables not used *)
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh)
End

(* Per-instruction simulation for memzero transform.
   Standalone helper: avoids fs[memzero_inst_ok_def] destroying step_inst
   assumptions in the induction context (see L406). *)
Theorem memzero_inst_step_sim[local]:
  !nop_set rep_map fresh inst fuel ctx s1 s1_mid s2.
    memzero_inst_ok nop_set rep_map fresh inst /\
    memzero_inv fresh s1 s2 /\
    step_inst fuel ctx inst s1 = OK s1_mid
    ==>
    ?s2_mid.
      run_insts fuel ctx (apply_memzero_inst nop_set rep_map inst) s2
        = OK s2_mid /\
      memzero_inv fresh s1_mid s2_mid
Proof
  rpt strip_tac >>
  fs[memzero_inst_ok_def] >>
  Cases_on `MEM inst.inst_id nop_set`
  >| [suspend "nop", ALL_TAC] >>
  Cases_on `ALOOKUP rep_map inst.inst_id`
  >| [suspend "unchanged", ALL_TAC] >>
  rename1 `ALOOKUP rep_map inst.inst_id = SOME cg` >>
  Cases_on `cg.cg_length = 32`
  >| [suspend "rep32", suspend "rep_gt32"]
QED

Resume memzero_inst_step_sim[nop]:
  (* NOP'd case: is_zero_store from assumption + MEM *)
  `is_zero_store inst` by fs[] >>
  simp[apply_memzero_inst_def, run_insts_def, step_inst_nop] >>
  irule nop_mem_write_preserves_memzero_inv >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s1`] >>
  gvs[is_zero_store_def]
QED

Resume memzero_inst_step_sim[unchanged]:
  (* Unchanged case *)
  simp[apply_memzero_inst_def, run_insts_def] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `s1_mid`, `s2`, `fresh`]
    mp_tac non_vol_step_memzero_inv >>
  (impl_tac >- fs[]) >> strip_tac >>
  qexists_tac `s2'` >> simp[]
QED

Resume memzero_inst_step_sim[rep32]:
  (* 32B replacement case *)
  `is_zero_store inst /\
   operand_lit_val (HD inst.inst_operands) = SOME cg.cg_dst` by
    (first_x_assum (qspec_then `cg` mp_tac) >> fs[]) >>
  `?s2'. step_inst fuel ctx inst s2 = OK s2' /\
         memzero_inv fresh s1_mid s2'` by (
    qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `s2`, `s1_mid`, `fresh`]
      mp_tac mstore_preserves_memzero_inv >>
    (impl_tac >- fs[is_zero_store_def]) >> metis_tac[]) >>
  `step_inst fuel ctx (mk_zero_store_inst inst cg.cg_dst) s2 =
   step_inst fuel ctx inst s2` by
    (irule mk_zero_store_step_eq >> fs[]) >>
  simp[apply_memzero_inst_def, run_insts_def]
QED

Resume memzero_inst_step_sim[rep_gt32]:
  (* >32B case — ALL claims use sg >- (never by >> which absorbs) *)
  (sg `is_zero_store inst /\ fresh_calldatasize_var inst.inst_id IN fresh`
   >- (first_x_assum (qspec_then `cg` mp_tac) >> fs[])) >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `s1_mid`]
    mp_tac step_mem_write_only_memory >>
  (impl_tac >- (fs[is_zero_store_def])) >>
  strip_tac >>
  qpat_x_assum `_ = s1` (strip_assume_tac o
    SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  qabbrev_tac `cds_var = fresh_calldatasize_var inst.inst_id` >>
  simp[apply_memzero_inst_def, run_insts_def, LET_THM] >>
  (sg `step_inst fuel ctx (mk_calldatasize_inst inst.inst_id) s2 =
    OK (update_var cds_var (n2w (LENGTH s2.vs_call_ctx.cc_calldata)) s2)`
   >- (simp[mk_calldatasize_inst_def, step_inst_non_invoke, is_terminator_def,
           step_inst_base_def, exec_read0_def, Abbr `cds_var`])) >>
  simp[] >>
  qabbrev_tac `s2_a = update_var cds_var
    (n2w (LENGTH s2.vs_call_ctx.cc_calldata)) s2` >>
  (sg `eval_operand (Var cds_var) s2_a =
    SOME (n2w (LENGTH s2.vs_call_ctx.cc_calldata))`
   >- (simp[eval_operand_def, Abbr `s2_a`, update_var_def, lookup_var_def,
           FLOOKUP_UPDATE])) >>
  simp[mk_memzero_calldatacopy_def, step_inst_non_invoke, is_terminator_def,
       step_inst_base_def, eval_operand_def] >>
  simp[memzero_inv_def, write_memory_with_expansion_def, LET_THM,
       Abbr `s2_a`, update_var_def] >>
  fs[memzero_inv_def] >> rpt strip_tac >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `v = cds_var` >- fs[] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[lookup_var_def]
QED

Finalise memzero_inst_step_sim;

Theorem memzero_run_insts_sim[local]:
  !nop_set rep_map fresh insts fuel ctx s1 s2.
    memzero_inv fresh s1 s2 /\
    EVERY (memzero_inst_ok nop_set rep_map fresh) insts
    ==>
    (!s'. run_insts fuel ctx insts s1 <> OK s') \/
    ?s1' s2'.
      run_insts fuel ctx insts s1 = OK s1' /\
      run_insts fuel ctx
        (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s2 = OK s2' /\
      memzero_inv fresh s1' s2'
Proof
  rpt strip_tac >>
  qspecl_then [`apply_memzero_inst nop_set rep_map`,
               `memzero_inst_ok nop_set rep_map fresh`,
               `memzero_inv fresh`]
    mp_tac flat_map_inst_sim >>
  (impl_tac >- metis_tac[memzero_inst_step_sim]) >>
  disch_then (qspecl_then [`insts`, `fuel`, `ctx`, `s1`, `s2`] mp_tac) >>
  (impl_tac >- fs[]) >> simp[]
QED

(* ===== Memory convergence ===== *)

(* Key insight: for instructions satisfying memzero_inst_ok,
   the final memory after run_insts depends ONLY on the zero-store
   writes applied to the initial memory. Non-volatile instructions
   don't modify memory (non_vol_step_preserves_memory), and zero-stores
   have literal operands so their memory effect depends only on
   current memory, not variable state.

   We prove this by showing both sides (original and transformed)
   produce the same final memory when starting from the same state. *)

(* mstore with literal 0 only changes vs_memory, and the change
   depends only on the current vs_memory *)
Theorem mstore_0w_only_mem[local]:
  !dst (s:venom_state).
    (mstore dst (0w:bytes32) s).vs_memory =
    (mstore dst 0w ((init_venom_state "") with vs_memory := s.vs_memory)).vs_memory
Proof
  rw[mstore_def, LET_THM]
QED

(* Zero-store step result: mstore with literal operands *)
Theorem zero_store_step_is_mstore[local]:
  !fuel ctx inst s s_mid.
    is_zero_store inst /\ inst_wf inst /\
    step_inst fuel ctx inst s = OK s_mid
    ==>
    s_mid = mstore (THE (operand_lit_val (HD inst.inst_operands))) (0w:bytes32) s
Proof
  rw[is_zero_store_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  Cases_on `h` >> fs[operand_lit_val_def] >>
  Cases_on `h'` >> fs[operand_lit_val_def] >>
  gvs[step_inst_non_invoke, step_inst_base_def, is_terminator_def,
      exec_write2_def, eval_operand_def, n2w_w2n]
QED

(* memzero_inst_ok implies inst_wf *)
Theorem memzero_inst_ok_wf[local]:
  !nop_set rep_map fresh inst.
    memzero_inst_ok nop_set rep_map fresh inst ==> inst_wf inst
Proof
  simp[memzero_inst_ok_def]
QED

(* Non-zero-store with memzero_inst_ok preserves memory *)
Theorem memzero_non_zs_preserves_memory[local]:
  !nop_set rep_map fresh fuel ctx inst s s'.
    memzero_inst_ok nop_set rep_map fresh inst /\
    ~is_zero_store inst /\
    step_inst fuel ctx inst s = OK s'
    ==>
    s'.vs_memory = s.vs_memory
Proof
  rw[memzero_inst_ok_def] >>
  `~MEM inst.inst_id nop_set` by metis_tac[] >>
  `ALOOKUP rep_map inst.inst_id = NONE` by
    (Cases_on `ALOOKUP rep_map inst.inst_id` >> fs[] >> metis_tac[]) >>
  metis_tac[non_vol_step_preserves_memory]
QED

(* For the s1 side: the final memory equals the sequential application
   of all zero-store mstores to the initial memory.
   Non-volatile instructions don't change memory. *)
Theorem run_insts_s1_mem_factor[local]:
  !nop_set rep_map fresh insts fuel ctx s s'.
    EVERY (memzero_inst_ok nop_set rep_map fresh) insts /\
    run_insts fuel ctx insts s = OK s'
    ==>
    s'.vs_memory =
    FOLDL (\m inst.
      if is_zero_store inst then
        (mstore (THE (operand_lit_val (HD inst.inst_operands))) (0w:bytes32)
         ((init_venom_state "") with vs_memory := m)).vs_memory
      else m)
      s.vs_memory insts
Proof
  Induct_on `insts` >- simp[run_insts_def] >>
  rpt strip_tac >> fs[EVERY_DEF, run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> fs[] >>
  rename1 `step_inst fuel ctx inst s = OK s_mid` >>
  Cases_on `is_zero_store inst` >> fs[]
  >- ((* Zero-store: s_mid = mstore ... s *)
    `inst_wf inst` by metis_tac[memzero_inst_ok_wf] >>
    drule_all zero_store_step_is_mstore >> disch_then SUBST_ALL_TAC >>
    simp[GSYM mstore_0w_only_mem] >>
    first_x_assum irule >> metis_tac[])
  >- ((* Non-zero-store: memory unchanged *)
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `fuel`, `ctx`, `inst`, `s`, `s_mid`]
      mp_tac memzero_non_zs_preserves_memory >>
    (impl_tac >- fs[]) >> strip_tac >>
    `s'.vs_memory = FOLDL (\m inst.
      if is_zero_store inst then
        (mstore (THE (operand_lit_val (HD inst.inst_operands))) 0w
         ((init_venom_state "") with vs_memory := m)).vs_memory
      else m) s_mid.vs_memory insts` by
      (first_x_assum irule >> metis_tac[]) >>
    fs[])
QED

(* ===== Byte-level memory convergence infrastructure ===== *)

(* Zero-write abstraction: write n zero bytes at offset *)
Definition apply_zero_write_def:
  apply_zero_write (offset:num, n:num) mem =
    (write_memory_with_expansion offset (REPLICATE n (0w:word8))
       ((init_venom_state "") with vs_memory := mem)).vs_memory
End

(* Length after write_memory_with_expansion *)
Theorem wmexp_mem_length[local]:
  !offset bytes (st:venom_state).
    LENGTH (write_memory_with_expansion offset bytes st).vs_memory =
    MAX (LENGTH st.vs_memory) (offset + LENGTH bytes)
Proof
  rw[write_memory_with_expansion_def, LET_THM] >>
  simp[LENGTH_APPEND, LENGTH_TAKE_EQ, LENGTH_DROP, LENGTH_REPLICATE, MAX_DEF]
QED

(* wmexp only depends on vs_memory — general version of mstore_0w_only_mem *)
Theorem wmexp_only_mem[local]:
  !offset bytes (s:venom_state).
    (write_memory_with_expansion offset bytes s).vs_memory =
    (write_memory_with_expansion offset bytes
       ((init_venom_state "") with vs_memory := s.vs_memory)).vs_memory
Proof
  rw[write_memory_with_expansion_def, LET_THM]
QED

(* EL characterization for write_memory_with_expansion *)
Theorem wmexp_el[local]:
  !offset bytes (st:venom_state) i.
    i < LENGTH (write_memory_with_expansion offset bytes st).vs_memory ==>
    EL i (write_memory_with_expansion offset bytes st).vs_memory =
      if i < offset then
        if i < LENGTH st.vs_memory then EL i st.vs_memory else 0w
      else if i < offset + LENGTH bytes then
        EL (i - offset) bytes
      else
        if i < LENGTH st.vs_memory then EL i st.vs_memory else 0w
Proof
  rw[write_memory_with_expansion_def, LET_THM] >>
  simp[EL_APPEND_EQN, LENGTH_TAKE_EQ, LENGTH_DROP, LENGTH_REPLICATE] >>
  rw[] >> fs[] >>
  simp[EL_TAKE, EL_DROP, EL_APPEND_EQN, EL_REPLICATE, LENGTH_REPLICATE]
QED

(* EL after wmexp with zero bytes: simpler — all written bytes are 0w *)
Theorem wmexp_zeros_el[local]:
  !offset n (st:venom_state) i.
    i < LENGTH (write_memory_with_expansion offset (REPLICATE n (0w:word8)) st).vs_memory ==>
    EL i (write_memory_with_expansion offset (REPLICATE n 0w) st).vs_memory =
      if offset <= i /\ i < offset + n then 0w
      else if i < LENGTH st.vs_memory then EL i st.vs_memory
      else 0w
Proof
  rpt strip_tac >>
  `EL i (write_memory_with_expansion offset (REPLICATE n 0w) st).vs_memory =
    if i < offset then
      if i < LENGTH st.vs_memory then EL i st.vs_memory else 0w
    else if i < offset + LENGTH (REPLICATE n (0w:word8)) then
      EL (i - offset) (REPLICATE n (0w:word8))
    else if i < LENGTH st.vs_memory then EL i st.vs_memory
    else 0w` by (irule wmexp_el >> fs[]) >>
  fs[LENGTH_REPLICATE, EL_REPLICATE] >>
  rw[] >> fs[]
QED

(* apply_zero_write EL characterization *)
Theorem apply_zero_write_el[local]:
  !offset n mem i. i < LENGTH (apply_zero_write (offset, n) mem) ==>
    EL i (apply_zero_write (offset, n) mem) =
      if offset <= i /\ i < offset + n then 0w
      else if i < LENGTH mem then EL i mem else 0w
Proof
  simp[apply_zero_write_def] >> rpt strip_tac >>
  qspecl_then [`offset`, `n`, `((init_venom_state "") with vs_memory := mem)`, `i`] mp_tac wmexp_zeros_el >>
  fs[LENGTH_REPLICATE, wmexp_mem_length]
QED

(* apply_zero_write length *)
Theorem apply_zero_write_length[local]:
  !offset n mem.
    LENGTH (apply_zero_write (offset, n) mem) = MAX (LENGTH mem) (offset + n)
Proof
  simp[apply_zero_write_def, wmexp_mem_length, LENGTH_REPLICATE]
QED

Theorem foldl_zero_write_length_ge[local]:
  !writes x mem.
    x <= LENGTH mem ==>
    x <= LENGTH (FOLDL (\m w. apply_zero_write w m) mem writes)
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[apply_zero_write_length, MAX_DEF]
QED

(* FOLDL of zero writes: EL characterization — order independent! *)
Theorem foldl_zero_write_el[local]:
  !writes mem i.
    i < LENGTH (FOLDL (\m w. apply_zero_write w m) mem writes) ==>
    EL i (FOLDL (\m w. apply_zero_write w m) mem writes) =
      if EXISTS (\(offset,n). offset <= i /\ i < offset + n) writes then 0w
      else if i < LENGTH mem then EL i mem
      else 0w
Proof
  Induct_on `writes` >> simp[] >>
  rpt gen_tac >>
  PairCases_on `h` >> simp[] >>
  strip_tac >>
  qabbrev_tac `mem' = apply_zero_write (h0,h1) mem` >>
  `LENGTH mem <= LENGTH mem'` by
    (simp[Abbr `mem'`, apply_zero_write_length, MAX_DEF]) >>
  first_x_assum (qspecl_then [`mem'`, `i`] mp_tac) >> fs[] >> strip_tac >>
  Cases_on `EXISTS (\(offset,n). offset <= i /\ i < offset + n) writes` >> fs[] >>
  Cases_on `h0 <= i /\ i < h0 + h1` >> fs[] >>
  Cases_on `i < LENGTH mem'` >> fs[] >>
  qspecl_then [`h0`, `h1`, `mem`, `i`] mp_tac apply_zero_write_el >>
  fs[Abbr `mem'`]
QED

(* Two FOLDL zero-write sequences with same coverage produce same memory *)
Theorem foldl_zero_write_eq[local]:
  !writes1 writes2 mem.
    LENGTH (FOLDL (\m w. apply_zero_write w m) mem writes1) =
    LENGTH (FOLDL (\m w. apply_zero_write w m) mem writes2) /\
    (!i. EXISTS (\(offset,n). offset <= i /\ i < offset + n) writes1 <=>
         EXISTS (\(offset,n). offset <= i /\ i < offset + n) writes2)
    ==>
    FOLDL (\m w. apply_zero_write w m) mem writes1 =
    FOLDL (\m w. apply_zero_write w m) mem writes2
Proof
  rpt strip_tac >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  `x < LENGTH (FOLDL (\m w. apply_zero_write w m) mem writes1)` by fs[] >>
  `x < LENGTH (FOLDL (\m w. apply_zero_write w m) mem writes2)` by fs[] >>
  drule foldl_zero_write_el >> strip_tac >>
  qspecl_then [`writes2`, `mem`, `x`] mp_tac foldl_zero_write_el >>
  simp[]
QED

(* Bridge: mstore 0w FOLDL = apply_zero_write FOLDL with 32-byte writes *)
Theorem foldl_mstore_eq_zero_write[local]:
  !dsts mem.
    FOLDL (\m d. (mstore d (0w:bytes32) ((init_venom_state "") with vs_memory := m)).vs_memory) mem dsts =
    FOLDL (\m w. apply_zero_write w m) mem (MAP (\d. (d, 32)) dsts)
Proof
  Induct >> simp[apply_zero_write_def, mstore_0w_eq_write]
QED

(* Bridge: conditional FOLDL from run_insts_s1_mem_factor = FOLDL over FILTER *)
Theorem conditional_foldl_eq_filter_foldl[local]:
  !insts mem.
    FOLDL (\m inst. if is_zero_store inst then
      (mstore (THE (operand_lit_val (HD inst.inst_operands))) (0w:bytes32)
       ((init_venom_state "") with vs_memory := m)).vs_memory
    else m) mem insts =
    FOLDL (\m d. (mstore d 0w ((init_venom_state "") with vs_memory := m)).vs_memory) mem
      (MAP (\inst. THE (operand_lit_val (HD inst.inst_operands)))
           (FILTER is_zero_store insts))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `is_zero_store h` >> simp[]
QED

(* Zero-write list for s1: each zero-store writes 32 bytes at its destination *)
Definition s1_zero_writes_def:
  s1_zero_writes insts =
    MAP (\inst. (THE (operand_lit_val (HD inst.inst_operands)), 32:num))
      (FILTER is_zero_store insts)
End

(* Zero-write list for s2: each rep writes cg.cg_length bytes at cg.cg_dst *)
Definition s2_zero_writes_def:
  s2_zero_writes rep_map insts =
    FLAT (MAP (\inst.
      case ALOOKUP rep_map inst.inst_id of
        NONE => []
      | SOME cg => [(cg.cg_dst, cg.cg_length)])
    insts)
End

(* WF predicate: s1 and s2 zero-writes cover the same byte positions.
   This captures the essential group structure property:
   - Each group's range = union of its member zero-stores' 32-byte ranges
   - Satisfied by any correct scan that forms groups from contiguous zero-stores *)
Definition memzero_coverage_wf_def:
  memzero_coverage_wf nop_set rep_map insts <=>
    (* Coverage equivalence: same byte positions written *)
    (!i. EXISTS (\(offset,n). offset <= i /\ i < offset + n)
           (s1_zero_writes insts) <=>
         EXISTS (\(offset,n). offset <= i /\ i < offset + n)
           (s2_zero_writes rep_map insts)) /\
    (* Every zero-store is either NOP'd or has a rep entry *)
    EVERY (\inst. is_zero_store inst ==>
             MEM inst.inst_id nop_set \/
             ?cg. ALOOKUP rep_map inst.inst_id = SOME cg)
      insts /\
    (* NOP'd instructions don't have rep entries *)
    EVERY (\inst. MEM inst.inst_id nop_set ==>
             ALOOKUP rep_map inst.inst_id = NONE)
      insts /\
    (* Maximum write extent matches (ensures same final memory length) *)
    (!mem. LENGTH (FOLDL (\m w. apply_zero_write w m) mem (s1_zero_writes insts)) =
           LENGTH (FOLDL (\m w. apply_zero_write w m) mem (s2_zero_writes rep_map insts)))
End

(* ===== S2 memory factoring ===== *)

(* Per-instruction s2 memory characterization:
   after running the transformed instructions, memory = apply_zero_write
   of the rep_map entry (if any), or unchanged (if no rep entry).
   Precondition: if inst is a zero-store, it's either NOP'd or has a rep entry
   (prevents unchanged zero-stores which would write but have no rep entry). *)
Theorem memzero_inst_s2_mem_effect[local]:
  !nop_set rep_map fresh inst fuel ctx s s'.
    memzero_inst_ok nop_set rep_map fresh inst /\
    (is_zero_store inst ==>
       MEM inst.inst_id nop_set \/
       ?cg. ALOOKUP rep_map inst.inst_id = SOME cg) /\
    (MEM inst.inst_id nop_set ==>
       ALOOKUP rep_map inst.inst_id = NONE) /\
    (!cg. ALOOKUP rep_map inst.inst_id = SOME cg ==>
       cg.cg_dst < dimword (:256) /\
       cg.cg_length < dimword (:256)) /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    run_insts fuel ctx (apply_memzero_inst nop_set rep_map inst) s = OK s'
    ==>
    s'.vs_memory =
    FOLDL (\m w. apply_zero_write w m) s.vs_memory
      (case ALOOKUP rep_map inst.inst_id of
         NONE => []
       | SOME cg => [(cg.cg_dst, cg.cg_length)])
Proof
  rpt strip_tac >>
  Cases_on `MEM inst.inst_id nop_set`
  >- ( (* NOP'd: NOP preserves memory, ALOOKUP=NONE *)
    `ALOOKUP rep_map inst.inst_id = NONE` by fs[] >>
    fs[apply_memzero_inst_def, run_insts_def, step_inst_nop])
  >> Cases_on `ALOOKUP rep_map inst.inst_id`
  >- ( (* Unchanged, ALOOKUP=NONE: not zero-store => memory unchanged *)
    `~is_zero_store inst` by (CCONTR_TAC >> fs[]) >>
    `apply_memzero_inst nop_set rep_map inst = [inst]` by
      fs[apply_memzero_inst_def] >>
    fs[run_insts_def] >>
    pop_assum kall_tac >>
    Cases_on `step_inst fuel ctx inst s` >> fs[] >>
    metis_tac[memzero_non_zs_preserves_memory])
  >> rename1 `ALOOKUP rep_map inst.inst_id = SOME cg` >>
  simp[] >>
  `is_zero_store inst` by
    (fs[memzero_inst_ok_def] >>
     Cases_on `cg.cg_length = 32` >> res_tac >> fs[]) >>
  `inst_wf inst` by fs[memzero_inst_ok_def] >>
  Cases_on `cg.cg_length = 32`
  >- ( (* 32B rep *)
    fs[] >>
    `operand_lit_val (HD inst.inst_operands) = SOME cg.cg_dst` by
      (fs[memzero_inst_ok_def] >> res_tac >> fs[]) >>
    `apply_memzero_inst nop_set rep_map inst =
       [mk_zero_store_inst inst cg.cg_dst]` by
      fs[apply_memzero_inst_def] >>
    fs[run_insts_def] >>
    `step_inst fuel ctx (mk_zero_store_inst inst cg.cg_dst) s =
     step_inst fuel ctx inst s` by metis_tac[mk_zero_store_step_eq] >>
    Cases_on `step_inst fuel ctx inst s` >> fs[] >>
    drule_all zero_store_step_is_mstore >> strip_tac >>
    gvs[apply_zero_write_def, mstore_0w_eq_write, mstore_0w_only_mem] >>
    simp[Once wmexp_only_mem])
  >> ( (* >32B rep: calldatasize + calldatacopy *)
    fs[] >>
    `fresh_calldatasize_var inst.inst_id IN fresh` by
      (fs[memzero_inst_ok_def] >> res_tac >> fs[]) >>
    qabbrev_tac `cds_var = fresh_calldatasize_var inst.inst_id` >>
    fs[apply_memzero_inst_def, run_insts_def, LET_THM] >>
    (* Step 1: CALLDATASIZE *)
    `step_inst fuel ctx (mk_calldatasize_inst inst.inst_id) s =
     OK (update_var cds_var (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)` by
      simp[mk_calldatasize_inst_def, step_inst_non_invoke, is_terminator_def,
           step_inst_base_def, exec_read0_def, Abbr `cds_var`] >>
    fs[] >>
    qabbrev_tac `s_a = update_var cds_var
      (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s` >>
    (* Step 2: CALLDATACOPY — operand evaluation *)
    `s_a.vs_memory = s.vs_memory` by simp[Abbr `s_a`, update_var_def] >>
    `s_a.vs_call_ctx = s.vs_call_ctx` by simp[Abbr `s_a`, update_var_def] >>
    `eval_operand (Var cds_var) s_a =
     SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata))` by
      simp[eval_operand_def, Abbr `s_a`, update_var_def, lookup_var_def,
           FLOOKUP_UPDATE] >>
    fs[mk_memzero_calldatacopy_def, step_inst_non_invoke, is_terminator_def,
       step_inst_base_def, eval_operand_def] >>
    (* Eliminate MOD dimword (all values < dimword) *)
    `LENGTH s.vs_call_ctx.cc_calldata MOD dimword (:256) =
     LENGTH s.vs_call_ctx.cc_calldata` by simp[] >>
    `cg.cg_length MOD dimword (:256) = cg.cg_length` by simp[] >>
    `cg.cg_dst MOD dimword (:256) = cg.cg_dst` by simp[] >>
    fs[] >>
    (* calldatacopy past end: offset = LENGTH calldata, gives all zeros *)
    `TAKE cg.cg_length
      (DROP (LENGTH s.vs_call_ctx.cc_calldata) s.vs_call_ctx.cc_calldata ++
       REPLICATE cg.cg_length 0w) =
     REPLICATE cg.cg_length 0w` by
      simp[calldatacopy_past_end_bytes] >>
    fs[] >>
    gvs[TAKE_LENGTH_ID_rwt] >>
    simp[Once wmexp_only_mem, apply_zero_write_def])
QED

(* run_insts preserves vs_call_ctx for non-terminator/non-INVOKE/non-alloca/non-ext_call *)
Theorem run_insts_preserves_call_ctx[local]:
  !insts fuel ctx s s'.
    run_insts fuel ctx insts s = OK s' /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) insts
    ==> s'.vs_call_ctx = s.vs_call_ctx
Proof
  Induct >- simp[run_insts_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  rename1 `inst :: insts` >>
  fs[run_insts_def] >>
  Cases_on `step_inst fuel ctx inst s` >> fs[] >>
  drule step_inst_preserves_all >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* apply_memzero_inst instructions satisfy the EVERY condition for call_ctx preservation *)
Theorem apply_memzero_inst_preserves_call_ctx[local]:
  !nop_set rep_map inst.
    memzero_inst_ok nop_set rep_map fresh inst ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (apply_memzero_inst nop_set rep_map inst)
Proof
  rw[apply_memzero_inst_def, memzero_inst_ok_def] >>
  simp[mk_nop_from_def, mk_zero_store_inst_def,
       mk_calldatasize_inst_def, mk_memzero_calldatacopy_def,
       is_terminator_def, is_alloca_op_def, is_ext_call_op_def] >>
  Cases_on `ALOOKUP rep_map inst.inst_id` >>
  simp[mk_zero_store_inst_def, mk_calldatasize_inst_def,
       mk_memzero_calldatacopy_def,
       is_terminator_def, is_alloca_op_def, is_ext_call_op_def] >>
  Cases_on `x.cg_length = 32` >>
  simp[mk_zero_store_inst_def, mk_calldatasize_inst_def,
       mk_memzero_calldatacopy_def,
       is_terminator_def, is_alloca_op_def, is_ext_call_op_def]
QED

(* S2 memory factoring: after running ALL transformed instructions,
   memory = FOLDL apply_zero_write of s2_zero_writes.
   Uses only EVERY preconditions (not full memzero_coverage_wf) for induction. *)
Theorem run_insts_s2_mem_factor[local]:
  !insts nop_set rep_map fresh fuel ctx s s'.
    EVERY (memzero_inst_ok nop_set rep_map fresh) insts /\
    EVERY (\inst. is_zero_store inst ==>
       MEM inst.inst_id nop_set \/
       ?cg. ALOOKUP rep_map inst.inst_id = SOME cg) insts /\
    EVERY (\inst. MEM inst.inst_id nop_set ==>
       ALOOKUP rep_map inst.inst_id = NONE) insts /\
    EVERY (\inst. !cg. ALOOKUP rep_map inst.inst_id = SOME cg ==>
       cg.cg_dst < dimword (:256) /\ cg.cg_length < dimword (:256)) insts /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    run_insts fuel ctx
      (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s = OK s'
    ==>
    s'.vs_memory =
    FOLDL (\m w. apply_zero_write w m) s.vs_memory
      (s2_zero_writes rep_map insts)
Proof
  Induct
  >- simp[run_insts_def, s2_zero_writes_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  rename1 `inst :: insts` >>
  (* Decompose FLAT MAP: apply_memzero_inst inst ++ FLAT MAP rest *)
  fs[MAP, FLAT] >>
  (* Use run_insts_append to split at the inst boundary *)
  `?s_mid. run_insts fuel ctx (apply_memzero_inst nop_set rep_map inst) s = OK s_mid` by
    (fs[run_insts_append] >>
     Cases_on `run_insts fuel ctx (apply_memzero_inst nop_set rep_map inst) s` >>
     fs[]) >>
  (* Split run_insts at inst boundary using run_insts_append *)
  `run_insts fuel ctx
     (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s_mid = OK s'` by
    (qpat_x_assum `run_insts _ _ (_ ++ _) _ = _` mp_tac >>
     simp[run_insts_append]) >>
  (* Per-inst: s_mid.vs_memory = FOLDL ... s.vs_memory (per-inst writes) *)
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `inst`, `fuel`, `ctx`, `s`, `s_mid`]
    mp_tac memzero_inst_s2_mem_effect >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Calldata preserved through non-INVOKE instruction *)
  `s_mid.vs_call_ctx = s.vs_call_ctx` by
    (qspecl_then [`apply_memzero_inst nop_set rep_map inst`,
                  `fuel`, `ctx`, `s`, `s_mid`]
       mp_tac run_insts_preserves_call_ctx >>
     simp[] >> metis_tac[apply_memzero_inst_preserves_call_ctx]) >>
  (* IH: s'.vs_memory = FOLDL ... s_mid.vs_memory (rest writes) *)
  first_x_assum (qspecl_then [`nop_set`, `rep_map`, `fresh`,
    `fuel`, `ctx`, `s_mid`, `s'`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Combine: s2_zero_writes for cons list *)
  fs[s2_zero_writes_def, FOLDL_APPEND]
QED

(* Combined: memzero_inv + memory convergence => state_equiv *)
Theorem memzero_run_insts_state_equiv[local]:
  !nop_set rep_map fresh insts fuel ctx s s1' s2'.
    EVERY (memzero_inst_ok nop_set rep_map fresh) insts /\
    memzero_coverage_wf nop_set rep_map insts /\
    EVERY (\inst. !cg. ALOOKUP rep_map inst.inst_id = SOME cg ==>
       cg.cg_dst < dimword (:256) /\ cg.cg_length < dimword (:256)) insts /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    run_insts fuel ctx insts s = OK s1' /\
    run_insts fuel ctx
      (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s = OK s2'
    ==>
    state_equiv fresh s1' s2'
Proof
  rpt strip_tac >>
  (* Step 1: memzero_inv from memzero_run_insts_sim *)
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `insts`, `fuel`, `ctx`, `s`, `s`]
    mp_tac memzero_run_insts_sim >>
  (impl_tac >- fs[memzero_inv_refl]) >>
  strip_tac >> gvs[] >>
  (* Step 2: s1 memory factoring *)
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `insts`, `fuel`, `ctx`, `s`, `s1'`]
    mp_tac run_insts_s1_mem_factor >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Step 3: s2 memory factoring *)
  qspecl_then [`insts`, `nop_set`, `rep_map`, `fresh`, `fuel`, `ctx`, `s`, `s2'`]
    mp_tac run_insts_s2_mem_factor >>
  (impl_tac >- fs[memzero_coverage_wf_def]) >> strip_tac >>
  (* Step 4: memory convergence via foldl_zero_write_eq *)
  `s1'.vs_memory = s2'.vs_memory` by
    (qpat_x_assum `s1'.vs_memory = _` (fn th => PURE_REWRITE_TAC[th]) >>
     qpat_x_assum `s2'.vs_memory = _` (fn th => PURE_REWRITE_TAC[th]) >>
     PURE_REWRITE_TAC[conditional_foldl_eq_filter_foldl,
                      foldl_mstore_eq_zero_write] >>
     irule foldl_zero_write_eq >>
     fs[memzero_coverage_wf_def, s1_zero_writes_def, MAP_MAP_o,
        combinTheory.o_DEF]) >>
  (* Step 5: memzero_inv + mem_eq → state_equiv *)
  metis_tac[memzero_inv_eq_mem_state_equiv]
QED

(* ===== General block bridge for FLAT MAP transforms ===== *)

(* state_equiv with different vs_inst_idx *)
Theorem state_equiv_with_idx[local]:
  !fresh s1 s2 j.
    state_equiv fresh s1 s2 ==>
    state_equiv fresh (s1 with vs_inst_idx := j) (s2 with vs_inst_idx := j)
Proof
  rw[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Unroll exec_block once at a terminator position *)
Theorem exec_block_at_terminator[local]:
  !fuel ctx bb j inst s.
    get_instruction bb j = SOME inst /\
    is_terminator inst.inst_opcode ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    (case step_inst fuel ctx inst (s with vs_inst_idx := j) of
       OK s'' => if s''.vs_halted then Halt s'' else OK s''
     | Halt s' => Halt s'
     | Abort a s' => Abort a s'
     | IntRet rv ss => IntRet rv ss
     | Error e => Error e)
Proof
  rw[Once exec_block_def]
QED

(* lift_result on raw step_inst implies lift_result on wrapped (halted-check)
   terminator form. *)
Theorem lift_result_wrap_terminator[local]:
  !R_ok R_term R_abort r1 r2.
    (∀s1 s2. R_ok s1 s2 ==> s1.vs_halted = s2.vs_halted) /\
    (∀s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    lift_result R_ok R_term R_abort r1 r2 ==>
    lift_result R_ok R_term R_abort
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
  Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def] >>
  `v.vs_halted = v'.vs_halted` by metis_tac[] >>
  Cases_on `v.vs_halted` >> fs[lift_result_def]
QED

(* Wrapped terminator step from state_equiv states (possibly different idx)
   gives lift_result. Composes terminator_exec_block_step_lift with
   step_inst_result_equiv via lift_result_trans_proof. *)
Theorem terminator_step_equiv[local]:
  !fresh fuel ctx inst s1 s2 j1 j2.
    state_equiv fresh s1 s2 /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (case step_inst fuel ctx inst (s1 with vs_inst_idx := j1) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case step_inst fuel ctx inst (s2 with vs_inst_idx := j2) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `valid_state_rel (state_equiv fresh) (execution_equiv fresh)` by
    simp[state_equiv_execution_equiv_valid_state_rel_proof] >>
  (* Step 1: s1 with j1 -> s1 via _rev *)
  qspecl_then [`state_equiv fresh`, `execution_equiv fresh`]
    mp_tac terminator_exec_block_step_lift_rev >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `j1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Step 2: s2 -> s2 with j2 via _fwd *)
  qspecl_then [`state_equiv fresh`, `execution_equiv fresh`]
    mp_tac terminator_exec_block_step_lift >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `inst`, `s2`, `j2`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Step 3: s1 -> s2 via result_equiv on raw step_inst *)
  `result_equiv fresh (step_inst fuel ctx inst s1)
                       (step_inst fuel ctx inst s2)` by
    (irule step_inst_result_equiv >> simp[]) >>
  fs[result_equiv_is_lift_result] >>
  (* Wrap the raw lift_result into the terminator form *)
  `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
     (case step_inst fuel ctx inst s1 of
        OK s'' => if s''.vs_halted then Halt s'' else OK s''
      | Halt s' => Halt s' | Abort a s' => Abort a s'
      | IntRet rv ss => IntRet rv ss | Error e => Error e)
     (case step_inst fuel ctx inst s2 of
        OK s'' => if s''.vs_halted then Halt s'' else OK s''
      | Halt s' => Halt s' | Abort a s' => Abort a s'
      | IntRet rv ss => IntRet rv ss | Error e => Error e)` by (
    irule lift_result_wrap_terminator >>
    rw[state_equiv_def, execution_equiv_def] >> fs[]
  ) >>
  (* Compose: (s1+j1 -> s1) ∘ (s1 -> s2) ∘ (s2 -> s2+j2) via transitivity *)
  `!r1 r2 r3.
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r1 r2 /\
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r2 r3 ==>
     lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh) r1 r3` by
    (match_mp_tac lift_result_trans_proof >>
     metis_tac[state_equiv_trans, execution_equiv_trans]) >>
  metis_tac[]
QED

(* Block bridge for 1:N transforms where both sides start from same state. *)
(* OK case: run_insts succeeds on both sides, state_equiv holds *)
Theorem bridge_ok_case[local]:
  !f non_terms term bb fresh fuel ctx s s1' s2'.
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    term.inst_opcode <> INVOKE /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      non_terms /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP f non_terms)) /\
    f term = [term] /\
    (!x. MEM (Var x) term.inst_operands ==> x NOTIN fresh) /\
    run_insts fuel ctx non_terms s = OK s1' /\
    run_insts fuel ctx (FLAT (MAP f non_terms)) s = OK s2' /\
    state_equiv fresh s1' s2' /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx
        (bb with bb_instructions := FLAT (MAP f bb.bb_instructions)) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `bb' = bb with bb_instructions :=
    FLAT (MAP f bb.bb_instructions)` >>
  `bb'.bb_instructions = FLAT (MAP f non_terms) ++ [term]` by
    (unabbrev_all_tac >> simp[MAP_APPEND, FLAT_APPEND]) >>
  `s1'.vs_inst_idx = 0` by
    (qspecl_then [`fuel`, `ctx`, `non_terms`, `s`, `s1'`]
       mp_tac run_insts_preserves_idx >> simp[]) >>
  `s2'.vs_inst_idx = 0` by
    (qspecl_then [`fuel`, `ctx`, `FLAT (MAP f non_terms)`, `s`, `s2'`]
       mp_tac run_insts_preserves_idx >> simp[]) >>
  qspecl_then [`non_terms`, `fuel`, `ctx`, `bb`, `s`, `0`, `s1'`]
    mp_tac exec_block_skip_prefix >>
  (impl_tac >- (simp[] >> rpt strip_tac >> simp[EL_APPEND1])) >>
  qspecl_then [`FLAT (MAP f non_terms)`, `fuel`, `ctx`, `bb'`, `s`, `0`, `s2'`]
    mp_tac exec_block_skip_prefix >>
  (impl_tac >- (simp[] >> rpt strip_tac >> simp[EL_APPEND1])) >>
  rpt strip_tac >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  fs[] >>
  qpat_x_assum `exec_block _ _ bb s = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `exec_block _ _ bb' s = _` (fn th => REWRITE_TAC [th]) >>
  qspecl_then [`fuel`, `ctx`, `bb`, `LENGTH non_terms`, `term`, `s1'`]
    mp_tac exec_block_at_terminator >>
  (impl_tac >- simp[get_instruction_def, EL_APPEND2]) >>
  qspecl_then [`fuel`, `ctx`, `bb'`, `LENGTH (FLAT (MAP f non_terms))`,
               `term`, `s2'`]
    mp_tac exec_block_at_terminator >>
  (impl_tac >- simp[get_instruction_def, EL_APPEND2]) >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ bb _ = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `exec_block _ _ bb' _ = _` (fn th => REWRITE_TAC [th]) >>
  irule terminator_step_equiv >> simp[]
QED

(* execution_equiv is symmetric (not in shared Props, so proved locally) *)
Theorem execution_equiv_sym[local]:
  !vars s1 s2. execution_equiv vars s1 s2 ==> execution_equiv vars s2 s1
Proof
  simp[execution_equiv_def]
QED

(* Reusable: lift_result symmetry *)
Theorem lift_result_sym[local]:
  !R_ok R_term R_abort r1 r2.
    lift_result R_ok R_term R_abort r1 r2 /\
    (!s1 s2. R_ok s1 s2 ==> R_ok s2 s1) /\
    (!s1 s2. R_term s1 s2 ==> R_term s2 s1) /\
    (!s1 s2. R_abort s1 s2 ==> R_abort s2 s1) ==>
    lift_result R_ok R_term R_abort r2 r1
Proof
  rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def]
QED

(* Non-OK case: run_insts fails on orig, use run_insts_lift_exec_block *)
Theorem bridge_non_ok_case[local]:
  !f non_terms term bb fresh fuel ctx s.
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      non_terms /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP f non_terms)) /\
    f term = [term] /\
    (!s1'. run_insts fuel ctx non_terms s <> OK s1') /\
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (run_insts fuel ctx non_terms s)
      (run_insts fuel ctx (FLAT (MAP f non_terms)) s) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx
        (bb with bb_instructions := FLAT (MAP f bb.bb_instructions)) s)
Proof
  rpt strip_tac
  >> `valid_state_rel (state_equiv fresh) (execution_equiv fresh)` by
       simp[state_equiv_execution_equiv_valid_state_rel_proof]
  >> qabbrev_tac `bb' = bb with bb_instructions :=
       FLAT (MAP f bb.bb_instructions)`
  >> `bb'.bb_instructions = FLAT (MAP f non_terms) ++ [term]` by
       (unabbrev_all_tac >> simp[MAP_APPEND, FLAT_APPEND])
  >> `!s2'. run_insts fuel ctx (FLAT (MAP f non_terms)) s <> OK s2'` by
       (CCONTR_TAC >> fs[] >>
        Cases_on `run_insts fuel ctx non_terms s` >> fs[lift_result_def])
  >> qspecl_then [`state_equiv fresh`, `execution_equiv fresh`,
                   `non_terms`] mp_tac run_insts_lift_exec_block
  >> (impl_tac >- simp[])
  >> disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `0`] mp_tac)
  >> simp[]
  >> (impl_tac >- (simp[] >> rpt strip_tac >> simp[EL_APPEND1]))
  >> strip_tac
  >> qspecl_then [`state_equiv fresh`, `execution_equiv fresh`,
                   `FLAT (MAP f non_terms)`] mp_tac run_insts_lift_exec_block
  >> (impl_tac >- simp[])
  >> disch_then (qspecl_then [`fuel`, `ctx`, `bb'`, `s`, `0`] mp_tac)
  >> simp[]
  >> (impl_tac >- (simp[] >> rpt strip_tac >> simp[EL_APPEND1]))
  >> strip_tac
  >> `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality]
  >> fs[]
  (* Chain: bb ← orig → trans → bb'.
     All three are non-OK, so case-split on result constructors *)
  >> Cases_on `run_insts fuel ctx non_terms s`
  >> Cases_on `exec_block fuel ctx bb s`
  >> Cases_on `run_insts fuel ctx (FLAT (MAP f non_terms)) s`
  >> Cases_on `exec_block fuel ctx bb' s`
  >> fs[lift_result_def]
  >> metis_tac[execution_equiv_sym, execution_equiv_trans]
QED

Theorem flat_map_same_start_block_bridge:
  !f non_terms term bb fresh P.
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    term.inst_opcode <> INVOKE /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      non_terms /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP f non_terms)) /\
    f term = [term] /\
    (!x. MEM (Var x) term.inst_operands ==> x NOTIN fresh) /\
    (!fuel ctx s. P s ==>
       lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
         (run_insts fuel ctx non_terms s)
         (run_insts fuel ctx (FLAT (MAP f non_terms)) s))
    ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ P s ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAP f bb.bb_instructions)) s)
Proof
  rpt strip_tac
  >> `FLAT (MAP f bb.bb_instructions) = FLAT (MAP f non_terms) ++ [term]`
       by simp[MAP_APPEND, FLAT_APPEND]
  >> first_x_assum (qspecl_then [`fuel`, `ctx`, `s`] mp_tac)
  >> (impl_tac >- fs[]) >> strip_tac
  >> reverse (Cases_on `?s1'. run_insts fuel ctx non_terms s = OK s1'`)
  >- (fs[] >>
      qspecl_then [`f`, `non_terms`, `term`, `bb`, `fresh`, `fuel`, `ctx`, `s`]
        mp_tac bridge_non_ok_case >> simp[])
  >> fs[]
  >> Cases_on `run_insts fuel ctx (FLAT (MAP f non_terms)) s`
  >> fs[lift_result_def]
  >> qspecl_then [`f`, `non_terms`, `term`, `bb`, `fresh`, `fuel`, `ctx`,
       `s`, `s1'`, `v`] mp_tac bridge_ok_case
  >> simp[]
QED

(* Zero-store instructions always succeed *)
Theorem zero_store_always_ok[local]:
  !fuel ctx inst s.
    is_zero_store inst /\ inst_wf inst ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rw[is_zero_store_def] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[] >>
  Cases_on `h` >> fs[operand_lit_val_def] >>
  Cases_on `h'` >> fs[operand_lit_val_def] >>
  simp[step_inst_non_invoke, step_inst_base_def, is_terminator_def,
       exec_write2_def, eval_operand_def]
QED

(* Per-instruction error propagation: if s1 errors on a memzero_inst_ok
   instruction, the transformed s2 instructions also error (or worse).
   Key insight: only unchanged non-volatile instructions can error.
   NOP'd/rep instructions are zero-stores that always succeed. *)
Theorem memzero_inst_step_error_sim[local]:
  !nop_set rep_map fresh inst fuel ctx s1 s2.
    memzero_inst_ok nop_set rep_map fresh inst /\
    memzero_inv fresh s1 s2 /\
    (!s1'. step_inst fuel ctx inst s1 <> OK s1')
    ==>
    !s2'. run_insts fuel ctx (apply_memzero_inst nop_set rep_map inst) s2
          <> OK s2'
Proof
  rpt strip_tac >>
  fs[memzero_inst_ok_def] >>
  Cases_on `is_zero_store inst` >>
  gvs[apply_memzero_inst_def, run_insts_def]
  >- (drule_all zero_store_always_ok >> metis_tac[])
  >> `ALOOKUP rep_map inst.inst_id = NONE` by
       (Cases_on `ALOOKUP rep_map inst.inst_id` >> fs[]) >>
  gvs[run_insts_def] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `s2`, `fresh`]
    mp_tac non_vol_step_memzero_result >>
  (impl_tac >- fs[]) >> strip_tac >>
  Cases_on `step_inst fuel ctx inst s2` >> gvs[]
QED

(* If run_insts on prefix fails, run_insts on prefix ++ suffix also fails *)
Theorem run_insts_append_fail[local]:
  !xs ys fuel ctx s.
    (!s'. run_insts fuel ctx xs s <> OK s') ==>
    (!s'. run_insts fuel ctx (xs ++ ys) s <> OK s')
Proof
  rpt strip_tac >>
  fs[run_insts_append] >>
  Cases_on `run_insts fuel ctx xs s` >> gvs[]
QED

(* If s1 fails on memzero_inst_ok instructions, s2 (transformed) also fails.
   Tracked with memzero_inv for induction across different states. *)
Theorem memzero_run_insts_s1_fail_s2_fail[local]:
  !insts nop_set rep_map fresh fuel ctx s1 s2.
    memzero_inv fresh s1 s2 /\
    EVERY (memzero_inst_ok nop_set rep_map fresh) insts /\
    (!s1'. run_insts fuel ctx insts s1 <> OK s1')
    ==>
    !s2'. run_insts fuel ctx
      (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s2 <> OK s2'
Proof
  Induct >- simp[run_insts_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  rename1 `inst :: insts` >>
  fs[run_insts_def] >>
  Cases_on `step_inst fuel ctx inst s1`
  >- ( (* s1 head OK => s1 fails on tail *)
    rename1 `step_inst _ _ inst s1 = OK s1_mid` >>
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `inst`, `fuel`, `ctx`,
      `s1`, `s1_mid`, `s2`] mp_tac memzero_inst_step_sim >>
    (impl_tac >- fs[]) >> strip_tac >>
    rename1 `memzero_inv fresh s1_mid s2_mid` >>
    `!s1'. run_insts fuel ctx insts s1_mid <> OK s1'` by
      (fs[] >> metis_tac[]) >>
    first_x_assum (qspecl_then [`nop_set`, `rep_map`, `fresh`, `fuel`,
      `ctx`, `s1_mid`, `s2_mid`] mp_tac) >>
    (impl_tac >- fs[]) >> strip_tac >>
    simp[FLAT, MAP] >>
    fs[run_insts_append] >>
    Cases_on `run_insts fuel ctx (apply_memzero_inst nop_set rep_map inst) s2` >>
    gvs[])
  >> ( (* s1 head fails => s2 transformed head also fails *)
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `inst`, `fuel`, `ctx`,
      `s1`, `s2`] mp_tac memzero_inst_step_error_sim >>
    (impl_tac >- (fs[] >> Cases_on `step_inst fuel ctx inst s1` >> gvs[])) >>
    strip_tac >>
    simp[FLAT, MAP] >>
    drule_all run_insts_append_fail >> metis_tac[])
QED

(* LAST identity through FLAT MAP: if f preserves the last element and every
   f returns non-empty, then LAST (FLAT (MAP f xs)) = LAST xs. *)
Theorem flat_map_last_identity:
  !f xs.
    xs <> [] /\
    (!x. f x <> []) /\
    f (LAST xs) = [LAST xs] ==>
    LAST (FLAT (MAP f xs)) = LAST xs
Proof
  rpt strip_tac >>
  `FLAT (MAP f xs) =
   FLAT (MAP f (FRONT xs)) ++ f (LAST xs)` by (
    `xs = FRONT xs ++ [LAST xs]`
      by metis_tac[SNOC_LAST_FRONT, SNOC_APPEND] >>
    pop_assum (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV
      (ONCE_REWRITE_CONV [th]))))) >>
    simp[MAP_APPEND, FLAT_APPEND]) >>
  `FLAT (MAP f xs) <> []` by
    (Cases_on `xs` >> fs[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
     Cases_on `f h` >> fs[]) >>
  simp[LAST_APPEND_NOT_NIL]
QED

(* Terminator structure preservation through FLAT MAP transforms.
   Weaker than flat_map_bb_well_formed: only preserves non-empty + LAST + only-last,
   without requiring PHI prefix preservation. Usable for intermediate blocks. *)
Theorem flat_map_term_structure:
  !f bb.
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb.bb_instructions /\
         is_terminator (EL k bb.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb.bb_instructions)) /\
    (!inst. f inst <> []) /\
    (f (LAST bb.bb_instructions) = [LAST bb.bb_instructions]) /\
    (!inst. MEM inst bb.bb_instructions /\
            ~is_terminator inst.inst_opcode ==>
      EVERY (\i. ~is_terminator i.inst_opcode) (f inst)) ==>
    let bb' = bb with bb_instructions :=
                FLAT (MAP f bb.bb_instructions) in
    bb'.bb_instructions <> [] /\
    is_terminator (LAST bb'.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb'.bb_instructions /\
         is_terminator (EL k bb'.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb'.bb_instructions))
Proof
  rw[LET_THM]
  >- ((* Non-empty *)
    Cases_on `bb.bb_instructions` >> fs[] >>
    simp[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
    Cases_on `f h` >> fs[])
  >- ((* LAST preserved *)
    `FLAT (MAP f bb.bb_instructions) =
     FLAT (MAP f (FRONT bb.bb_instructions)) ++
     f (LAST bb.bb_instructions)` by (
      `bb.bb_instructions =
       FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]`
        by metis_tac[SNOC_LAST_FRONT, SNOC_APPEND] >>
      pop_assum (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV
        (ONCE_REWRITE_CONV [th]))))) >>
      simp[MAP_APPEND, FLAT_APPEND]) >>
    `FLAT (MAP f bb.bb_instructions) <> []` by
      (Cases_on `bb.bb_instructions` >> fs[FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM] >>
       Cases_on `f h` >> fs[]) >>
    simp[LAST_APPEND_NOT_NIL])
  >- ((* Only-last terminator *)
    qabbrev_tac `insts = bb.bb_instructions` >>
    qabbrev_tac `result = FLAT (MAP f insts)` >>
    (* Step 1: decompose result = prefix ++ [LAST] *)
    `result = FLAT (MAP f (FRONT insts)) ++ [LAST insts]` by (
      `insts = FRONT insts ++ [LAST insts]`
        by metis_tac[SNOC_LAST_FRONT, SNOC_APPEND] >>
      simp[Abbr `result`] >>
      pop_assum (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (RAND_CONV
        (ONCE_REWRITE_CONV [th]))))) >>
      simp[MAP_APPEND, FLAT_APPEND]) >>
    (* Step 2: FRONT elements are non-terminators (EL-based, no ALL_DISTINCT) *)
    `EVERY (\i. ~is_terminator i.inst_opcode) (FRONT insts)` by (
      simp[EVERY_EL] >> rpt strip_tac >>
      `n < LENGTH insts` by
        (imp_res_tac rich_listTheory.LENGTH_FRONT >> fs[]) >>
      `EL n (FRONT insts) = EL n insts` by
        (irule rich_listTheory.FRONT_EL >> simp[]) >>
      simp[] >> CCONTR_TAC >> fs[] >>
      `n = PRE (LENGTH insts)` by (first_x_assum irule >> simp[]) >>
      imp_res_tac rich_listTheory.LENGTH_FRONT >> fs[]) >>
    (* Step 3: EVERY non-term for FLAT (MAP f (FRONT insts)) *)
    `EVERY (\i. ~is_terminator i.inst_opcode)
       (FLAT (MAP f (FRONT insts)))` suffices_by (
      strip_tac >>
      `LENGTH result = LENGTH (FLAT (MAP f (FRONT insts))) + 1` suffices_by (
        strip_tac >>
        Cases_on `k < LENGTH (FLAT (MAP f (FRONT insts)))`
        >- (fs[EL_APPEND1, EVERY_EL] >>
            first_x_assum (qspec_then `k` mp_tac) >> simp[])
        >- fs[]) >>
      simp[]) >>
    simp[EVERY_FLAT, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
    imp_res_tac MEM_FRONT_NOT_NIL >>
    fs[EVERY_MEM] >> res_tac >> fs[EVERY_MEM])
QED

(* bb_well_formed decomposition from weaker conditions (no PHI prefix needed).
   Used by mm_block_simulates_mode where intermediate blocks may not have
   the PHI prefix property but DO have the terminator structure. *)
Theorem bb_wf_decompose_weak:
  !bb.
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!k. k < LENGTH bb.bb_instructions /\
         is_terminator (EL k bb.bb_instructions).inst_opcode ==>
         k = PRE (LENGTH bb.bb_instructions)) ==>
    let non_terms = FILTER (\i. ~is_terminator i.inst_opcode)
                      bb.bb_instructions in
    let term = LAST bb.bb_instructions in
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode) non_terms
Proof
  rw[LET_THM]
  >- (
    qabbrev_tac `insts = bb.bb_instructions` >>
    `EVERY (\i. ~is_terminator i.inst_opcode) (FRONT insts)` by (
      simp[EVERY_EL] >> rpt strip_tac >>
      `LENGTH (FRONT insts) = PRE (LENGTH insts)` by
        simp[rich_listTheory.FRONT_LENGTH] >>
      `n < PRE (LENGTH insts)` by fs[] >>
      `EL n (FRONT insts) = EL n insts` by
        (irule rich_listTheory.FRONT_EL >> simp[]) >>
      fs[] >> CCONTR_TAC >> fs[] >>
      `n = PRE (LENGTH insts)` by (first_x_assum irule >> simp[]) >>
      fs[]) >>
    `FILTER (\i. ~is_terminator i.inst_opcode) insts = FRONT insts` by (
      `insts = FRONT insts ++ [LAST insts]` by
        metis_tac[SNOC_LAST_FRONT, SNOC_APPEND] >>
      pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[FILTER_APPEND_DISTRIB, FILTER, FILTER_EQ_ID]) >>
    simp[] >> metis_tac[SNOC_LAST_FRONT, SNOC_APPEND])
  >- simp[EVERY_FILTER]
QED

(* bb_well_formed decomposition: non-terminators ++ [terminator] *)
Theorem bb_wf_decompose:
  !bb. bb_well_formed bb ==>
    let non_terms = FILTER (\i. ~is_terminator i.inst_opcode)
                      bb.bb_instructions in
    let term = LAST bb.bb_instructions in
    bb.bb_instructions = non_terms ++ [term] /\
    is_terminator term.inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode) non_terms
Proof
  rpt strip_tac >>
  mp_tac (Q.SPEC `bb` bb_wf_decompose_weak) >>
  fs[bb_well_formed_def]
QED

(* Well-formedness for memzero sub-pass: properties of scan result
   that are trivially satisfied by the pipeline but require scan soundness
   proof to derive formally. *)
Definition memzero_block_wf_def:
  memzero_block_wf dfg bb <=>
    let groups = (scan_block_memzero dfg bb).mz_flushed in
    let nop_set = nop_ids_of_groups dfg Mem2Mem bb.bb_instructions groups in
    let rep_map = rep_map_of_groups bb.bb_instructions groups in
    let non_terms = FILTER (\i. ~is_terminator i.inst_opcode)
                      bb.bb_instructions in
    (* Block structure *)
    bb_well_formed bb /\
    (LAST bb.bb_instructions).inst_opcode <> INVOKE /\
    (!x. MEM (Var x) (LAST bb.bb_instructions).inst_operands ==>
       x NOTIN mm_block_fresh_memzero dfg bb) /\
    (* Terminator not in scan results *)
    ~MEM (LAST bb.bb_instructions).inst_id nop_set /\
    ALOOKUP rep_map (LAST bb.bb_instructions).inst_id = NONE /\
    (* Transformed non-terms are all non-terminator non-INVOKE *)
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (FLAT (MAP (apply_memzero_inst nop_set rep_map) non_terms)) /\
    (* Coverage + length WF for memory convergence *)
    memzero_coverage_wf nop_set rep_map non_terms /\
    (* Dimword conditions on rep entries *)
    EVERY (\inst. !cg. ALOOKUP rep_map inst.inst_id = SOME cg ==>
       cg.cg_dst < dimword (:256) /\ cg.cg_length < dimword (:256))
      non_terms /\
    (* Per-instruction WF for simulation *)
    (!fresh. mm_block_fresh_memzero dfg bb SUBSET fresh ==>
       EVERY (memzero_inst_ok nop_set rep_map fresh) non_terms)
End

(* Precompute each concrete non-aborting base-step clause separately, avoiding
   a single simplifier call over every opcode constructor. *)
local
  val opcode_ops = TypeBase.constructors_of ``:opcode``;
  val nt_nec_na_ops = List.filter (fn op_tm =>
    let val nt = EVAL ``~is_terminator ^op_tm``
        val nec = EVAL ``~is_ext_call_op ^op_tm``
        val na = EVAL ``~is_alloca_op ^op_tm``
    in aconv (rhs (concl nt)) T andalso aconv (rhs (concl nec)) T
       andalso aconv (rhs (concl na)) T end
  ) opcode_ops;
  val abort_ops = [``ASSERT``, ``ASSERT_UNREACHABLE``, ``RETURNDATACOPY``];
  val non_abort_ops = List.filter (fn op_tm =>
    not (List.exists (fn t => aconv t op_tm) abort_ops)) nt_nec_na_ops;
  val base_clauses = map (fn op_tm =>
    SIMP_CONV (srw_ss()) [step_inst_base_def]
      (mk_comb(mk_comb(``step_inst_base``,
        ``inst with inst_opcode := ^op_tm``), ``st:venom_state``))
  ) non_abort_ops;
  val exec_helper_defs = [
    exec_pure1_def, exec_pure2_def, exec_pure3_def,
    exec_read0_def, exec_read1_def, exec_write2_def,
    exec_alloca_def, exec_ext_call_def, exec_create_def,
    exec_delegatecall_def, LET_THM, AllCaseEqs()];
  val direct_clause_pairs = ListPair.zip(non_abort_ops, base_clauses);
  val common_case_tac =
    gvs[is_terminator_def, is_volatile_memory_def, read_effects_def,
        write_effects_def, empty_effects_def,
        is_alloca_op_def, is_ext_call_op_def];
  fun direct_clause_tac op_tm clause =
    (`inst with inst_opcode := ^op_tm = inst`
       by simp[instruction_component_equality] >>
     pop_assum (fn upd => ONCE_REWRITE_TAC [GSYM upd]) >>
     ONCE_REWRITE_TAC [clause] >> simp exec_helper_defs);
  val opcode_case_tacs = map (fn op_tm =>
    case List.find (fn (candidate, _) => aconv candidate op_tm)
           direct_clause_pairs of
      NONE => common_case_tac
    | SOME (_, clause) => common_case_tac >> direct_clause_tac op_tm clause
  ) opcode_ops;
in
  val mm_step_inst_base_no_abort_cases = opcode_case_tacs;
end

Theorem step_inst_base_non_volatile_no_abort[local]:
  !inst s a s'.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> ASSERT /\
    inst.inst_opcode <> ASSERT_UNREACHABLE /\
    ~is_volatile_memory inst /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    step_inst_base inst s <> Abort a s'
Proof
  rpt gen_tac >> disch_then strip_assume_tac >>
  (Cases_on `inst.inst_opcode` THENL mm_step_inst_base_no_abort_cases)
QED

(* Small result-shape facts keep consumers from unfolding the full executor. *)
Triviality mm_exec_helpers_no_halt_intret[simp]:
  (!f inst s s'. exec_pure1 f inst s <> Halt s') /\
  (!f inst s vs s'. exec_pure1 f inst s <> IntRet vs s') /\
  (!f inst s s'. exec_pure2 f inst s <> Halt s') /\
  (!f inst s vs s'. exec_pure2 f inst s <> IntRet vs s') /\
  (!f inst s s'. exec_pure3 f inst s <> Halt s') /\
  (!f inst s vs s'. exec_pure3 f inst s <> IntRet vs s') /\
  (!f inst s s'. exec_read0 f inst s <> Halt s') /\
  (!f inst s vs s'. exec_read0 f inst s <> IntRet vs s') /\
  (!f inst s s'. exec_read1 f inst s <> Halt s') /\
  (!f inst s vs s'. exec_read1 f inst s <> IntRet vs s') /\
  (!f inst s s'. exec_write2 f inst s <> Halt s') /\
  (!f inst s vs s'. exec_write2 f inst s <> IntRet vs s') /\
  (!inst s sz s'. exec_alloca inst s sz <> Halt s') /\
  (!inst s sz vs s'. exec_alloca inst s sz <> IntRet vs s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def, exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality mm_exec_call_helpers_no_halt_intret[simp]:
  (!inst s g a v ao as_ ro rs is_s s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Halt s') /\
  (!inst s g a v ao as_ ro rs is_s vs s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> IntRet vs s') /\
  (!inst s g a ao as_ ro rs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Halt s') /\
  (!inst s g a ao as_ ro rs vs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> IntRet vs s') /\
  (!inst s v off sz salt s'.
     exec_create inst s v off sz salt <> Halt s') /\
  (!inst s v off sz salt vs s'.
     exec_create inst s v off sz salt <> IntRet vs s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Theorem step_inst_base_non_term_no_halt[local]:
  !inst s s'. step_inst_base inst s = Halt s' ==>
    is_terminator inst.inst_opcode
Proof
  rw[step_inst_base_def] >> gvs[AllCaseEqs(), is_terminator_def]
QED

Theorem step_inst_base_non_term_no_intret[local]:
  !inst s vs s'. step_inst_base inst s = IntRet vs s' ==>
    is_terminator inst.inst_opcode
Proof
  rw[step_inst_base_def] >> gvs[AllCaseEqs(), is_terminator_def]
QED

Theorem step_inst_base_non_term_only_ok_error_abort[local]:
  !inst s. ~is_terminator inst.inst_opcode ==>
    (?s'. step_inst_base inst s = OK s') \/
    (?e. step_inst_base inst s = Error e) \/
    (?a s'. step_inst_base inst s = Abort a s')
Proof
  rpt strip_tac >> Cases_on `step_inst_base inst s` >>
  metis_tac[step_inst_base_non_term_no_halt,
            step_inst_base_non_term_no_intret]
QED

(* Non-terminator, non-INVOKE: step_inst can't produce Halt or IntRet *)
Theorem step_inst_non_term_non_invoke_only_ok_error_abort[local]:
  !fuel ctx inst s.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e) \/
    (?a s'. step_inst fuel ctx inst s = Abort a s')
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_non_term_only_ok_error_abort]
QED


(* Non-terminator, non-INVOKE, non-ASSERT, non-ASSERT_UNREACHABLE,
   non-volatile-memory, non-alloca, non-ext_call: step_inst cannot Abort. *)
Theorem step_inst_non_volatile_no_abort[local]:
  !fuel ctx inst s a s'.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ASSERT /\
    inst.inst_opcode <> ASSERT_UNREACHABLE /\
    ~is_volatile_memory inst /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    step_inst fuel ctx inst s <> Abort a s'
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_non_volatile_no_abort]
QED

(* memzero_inst_ok instructions only produce OK or Error.
   Zero-stores always OK. Unchanged instructions: trichotomy gives OK/Error/Abort,
   then step_inst_non_volatile_no_abort eliminates Abort. *)
Theorem memzero_inst_ok_only_ok_or_error[local]:
  !nop_set rep_map fresh inst fuel ctx s.
    memzero_inst_ok nop_set rep_map fresh inst ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[memzero_inst_ok_def] >> rpt strip_tac >>
  Cases_on `MEM inst.inst_id nop_set` >> res_tac >> fs[] >>
  TRY (drule_all zero_store_always_ok >> metis_tac[]) >>
  Cases_on `ALOOKUP rep_map inst.inst_id` >> fs[] >>
  TRY (
    qspecl_then [`fuel`, `ctx`, `inst`, `s`]
      mp_tac step_inst_non_term_non_invoke_only_ok_error_abort >>
    (impl_tac >- fs[]) >> strip_tac >> fs[] >>
    CCONTR_TAC >> fs[] >>
    qspecl_then [`fuel`, `ctx`, `inst`, `s`, `a`, `s'`]
      mp_tac step_inst_non_volatile_no_abort >>
    simp[] >> NO_TAC) >>
  Cases_on `x.cg_length = 32` >> res_tac >> fs[] >>
  drule_all zero_store_always_ok >> metis_tac[]
QED

(* Lift to run_insts: memzero_inst_ok instructions only produce OK or Error *)
Theorem run_insts_memzero_only_ok_or_error[local]:
  !insts nop_set rep_map fresh fuel ctx s.
    EVERY (memzero_inst_ok nop_set rep_map fresh) insts ==>
    (?s'. run_insts fuel ctx insts s = OK s') \/
    (?e. run_insts fuel ctx insts s = Error e)
Proof
  Induct >> simp[run_insts_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `h`, `fuel`, `ctx`, `s`]
    mp_tac memzero_inst_ok_only_ok_or_error >>
  (impl_tac >- fs[]) >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`nop_set`, `rep_map`, `fresh`, `fuel`, `ctx`, `s'`] mp_tac) >>
  (impl_tac >- fs[]) >> metis_tac[]
QED

(* Per-instruction: apply_memzero_inst outputs only produce OK or Error *)
Theorem apply_memzero_inst_run_only_ok_or_error[local]:
  !nop_set rep_map fresh inst fuel ctx s.
    memzero_inst_ok nop_set rep_map fresh inst ==>
    (?s'. run_insts fuel ctx (apply_memzero_inst nop_set rep_map inst) s = OK s') \/
    (?e. run_insts fuel ctx (apply_memzero_inst nop_set rep_map inst) s = Error e)
Proof
  rpt strip_tac >> fs[memzero_inst_ok_def, apply_memzero_inst_def] >>
  Cases_on `MEM inst.inst_id nop_set`
  >- ( (* NOP: mk_nop_from always succeeds *)
    simp[run_insts_def, mk_nop_from_def, step_inst_non_invoke,
         step_inst_base_def, is_terminator_def, exec_read0_def])
  >> Cases_on `ALOOKUP rep_map inst.inst_id`
  >- ( (* Unchanged: same instruction → OK or Error by memzero_inst_ok *)
    fs[] >>
    simp[run_insts_def] >>
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `inst`, `fuel`, `ctx`, `s`]
      mp_tac memzero_inst_ok_only_ok_or_error >>
    (impl_tac >- fs[memzero_inst_ok_def]) >> strip_tac >> gvs[])
  >> (
    rename1 `ALOOKUP _ _ = SOME cg` >>
    Cases_on `cg.cg_length = 32`
    >- ( (* 32B: mk_zero_store_inst is a zero-store, always OK *)
      fs[] >>
      simp[run_insts_def] >>
      `is_zero_store inst /\ inst_wf inst` by fs[] >>
      drule_all zero_store_always_ok >> strip_tac >>
      simp[mk_zero_store_inst_def, step_inst_non_invoke, step_inst_base_def,
           is_terminator_def, exec_write2_def, eval_operand_def,
           is_zero_store_def, operand_lit_val_def] >>
      Cases_on `inst.inst_operands` >> fs[is_zero_store_def, operand_lit_val_def] >>
      Cases_on `t` >> fs[is_zero_store_def] >>
      Cases_on `h` >> fs[operand_lit_val_def] >>
      metis_tac[])
    >> ( (* >32B: calldatasize + calldatacopy *)
      fs[] >>
      simp[run_insts_def, LET_THM] >>
      simp[mk_calldatasize_inst_def, step_inst_non_invoke, step_inst_base_def,
           is_terminator_def, exec_read0_def, eval_operand_def, update_var_def] >>
      simp[mk_memzero_calldatacopy_def, step_inst_non_invoke, step_inst_base_def,
           is_terminator_def, exec_write2_def, eval_operand_def,
           lookup_var_def, FLOOKUP_UPDATE]))
QED

(* Lift: expanded instructions (FLAT MAP apply_memzero_inst) only produce OK or Error *)
Theorem run_insts_expanded_only_ok_or_error[local]:
  !insts nop_set rep_map fresh fuel ctx s.
    EVERY (memzero_inst_ok nop_set rep_map fresh) insts ==>
    (?s'. run_insts fuel ctx
      (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s = OK s') \/
    (?e. run_insts fuel ctx
      (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s = Error e)
Proof
  Induct >> simp[run_insts_def] >>
  rpt strip_tac >> fs[EVERY_DEF, FLAT, MAP] >>
  simp[run_insts_append] >>
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `h`, `fuel`, `ctx`, `s`]
    mp_tac apply_memzero_inst_run_only_ok_or_error >>
  (impl_tac >- fs[]) >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`nop_set`, `rep_map`, `fresh`, `fuel`, `ctx`, `s'`] mp_tac) >>
  (impl_tac >- fs[]) >> metis_tac[]
QED

(* For memzero_inst_ok instructions starting from the same state,
   run_insts on original and expanded both only produce OK or Error.
   Combined: lift_result holds for any same-start execution. *)
Theorem memzero_run_insts_lift_result[local]:
  !nop_set rep_map fresh insts fuel ctx s.
    EVERY (memzero_inst_ok nop_set rep_map fresh) insts /\
    memzero_coverage_wf nop_set rep_map insts /\
    EVERY (\inst. !cg. ALOOKUP rep_map inst.inst_id = SOME cg ==>
       cg.cg_dst < dimword (:256) /\ cg.cg_length < dimword (:256)) insts /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (run_insts fuel ctx insts s)
      (run_insts fuel ctx
        (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s)
Proof
  rpt strip_tac >>
  (* Case split: does original run_insts succeed? *)
  reverse (Cases_on `?s1'. run_insts fuel ctx insts s = OK s1'`)
  >- ( (* non-OK case: both sides are Error *)
    fs[] >>
    (* s1 is non-OK, and only OK/Error possible, so s1 is Error *)
    `?e1. run_insts fuel ctx insts s = Error e1` by (
      qspecl_then [`insts`, `nop_set`, `rep_map`, `fresh`, `fuel`, `ctx`, `s`]
        mp_tac run_insts_memzero_only_ok_or_error >>
      (impl_tac >- fs[]) >> metis_tac[]) >>
    (* s2 is also non-OK (s1_fail_s2_fail) *)
    qspecl_then [`insts`, `nop_set`, `rep_map`, `fresh`,
      `fuel`, `ctx`, `s`, `s`] mp_tac memzero_run_insts_s1_fail_s2_fail >>
    (impl_tac >- fs[memzero_inv_refl]) >> strip_tac >>
    (* s2 only produces OK/Error, so s2 is Error *)
    `?e2. run_insts fuel ctx
        (FLAT (MAP (apply_memzero_inst nop_set rep_map) insts)) s = Error e2` by (
      qspecl_then [`insts`, `nop_set`, `rep_map`, `fresh`, `fuel`, `ctx`, `s`]
        mp_tac run_insts_expanded_only_ok_or_error >>
      (impl_tac >- fs[]) >> metis_tac[]) >>
    gvs[lift_result_def])
  >> ( (* OK case: use sim + convergence *)
    fs[] >>
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `insts`,
      `fuel`, `ctx`, `s`, `s`] mp_tac memzero_run_insts_sim >>
    (impl_tac >- fs[memzero_inv_refl]) >>
    strip_tac >> gvs[] >>
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `insts`,
      `fuel`, `ctx`, `s`, `s1'`, `s2'`]
      mp_tac memzero_run_insts_state_equiv >>
    (impl_tac >- fs[]) >> strip_tac >>
    simp[lift_result_def])
QED

(* Block sim for memzero sub-pass.
   The calldata dimword condition is necessary for >32B groups where
   calldatacopy uses w2n(n2w(LENGTH cc_calldata)). Trivially satisfied:
   dimword(:256) = 2^256, calldata bounded by EVM gas in practice. *)
Theorem mm_block_simulates_memzero:
  !dfg bb fresh.
    mm_block_fresh_memzero dfg bb SUBSET fresh /\
    EVERY inst_wf bb.bb_instructions /\
    memzero_block_wf dfg bb /\
    (!x. MEM (Var x) (LAST bb.bb_instructions).inst_operands ==>
       x NOTIN fresh) ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx (transform_block_memzero dfg bb) s)
Proof
  rw[memzero_block_wf_def, transform_block_memzero_def, LET_THM] >>
  rpt strip_tac >>
  qabbrev_tac `nop_set = nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
    (scan_block_memzero dfg bb).mz_flushed` >>
  qabbrev_tac `rep_map = rep_map_of_groups bb.bb_instructions
    (scan_block_memzero dfg bb).mz_flushed` >>
  qabbrev_tac `non_terms = FILTER (\i. ~is_terminator i.inst_opcode)
    bb.bb_instructions` >>
  qabbrev_tac `term = LAST bb.bb_instructions` >>
  `bb.bb_instructions = non_terms ++ [term] /\
   is_terminator term.inst_opcode /\
   EVERY (\i. ~is_terminator i.inst_opcode) non_terms` by (
    imp_res_tac bb_wf_decompose >>
    gvs[LET_THM, Abbr`non_terms`, Abbr`term`]) >>
  `EVERY (memzero_inst_ok nop_set rep_map fresh) non_terms` by (
    first_x_assum (qspec_then `fresh` mp_tac) >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
     non_terms` by (
    irule EVERY_MONOTONIC >>
    qexists_tac `memzero_inst_ok nop_set rep_map fresh` >>
    rw[memzero_inst_ok_def]) >>
  `apply_memzero_inst nop_set rep_map term = [term]` by (
    rw[apply_memzero_inst_def] >> fs[]) >>
  `!x. MEM (Var x) term.inst_operands ==> x NOTIN fresh` by fs[] >>
  qspecl_then [`apply_memzero_inst nop_set rep_map`, `non_terms`, `term`,
    `bb`, `fresh`,
    `\s'. LENGTH s'.vs_call_ctx.cc_calldata < dimword (:256)`]
    mp_tac flat_map_same_start_block_bridge >>
  simp[] >> disch_then irule >> simp[] >>
  rpt strip_tac >> irule memzero_run_insts_lift_result >> fs[]
QED

(* ===== Mode block simulation proof ===== *)

Theorem nop_mload_always_ok[local]:
  !inst fuel ctx s.
    inst_wf inst /\
    EVERY (\op. ?v. op = Lit v) inst.inst_operands /\
    inst.inst_opcode = MLOAD ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  fs[step_inst_non_invoke, inst_wf_def] >>
  Cases_on `inst.inst_operands` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `inst.inst_outputs` >> fs[] >>
  Cases_on `t` >> gvs[] >>
  simp[step_inst_base_def, exec_read1_def, eval_operand_def]
QED

Theorem nop_calldataload_always_ok[local]:
  !inst fuel ctx s.
    inst_wf inst /\
    EVERY (\op. ?v. op = Lit v) inst.inst_operands /\
    inst.inst_opcode = CALLDATALOAD ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  fs[step_inst_non_invoke, inst_wf_def] >>
  Cases_on `inst.inst_operands` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `inst.inst_outputs` >> fs[] >>
  Cases_on `t` >> gvs[] >>
  simp[step_inst_base_def, exec_read1_def, eval_operand_def]
QED

Theorem nop_dload_always_ok[local]:
  !inst fuel ctx s.
    inst_wf inst /\
    EVERY (\op. ?v. op = Lit v) inst.inst_operands /\
    inst.inst_opcode = DLOAD ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  fs[step_inst_non_invoke, inst_wf_def] >>
  Cases_on `inst.inst_operands` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `inst.inst_outputs` >> fs[] >>
  Cases_on `t` >> gvs[] >>
  simp[step_inst_base_def, exec_read1_def, eval_operand_def]
QED

Theorem nop_mstore_always_ok[local]:
  !inst fuel ctx s.
    inst_wf inst /\
    EVERY (\op. ?v. op = Lit v) inst.inst_operands /\
    inst.inst_opcode = MSTORE ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  fs[step_inst_non_invoke, inst_wf_def] >>
  Cases_on `inst.inst_operands` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `t'` >> fs[EVERY_DEF] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  simp[step_inst_base_def, exec_write2_def, eval_operand_def, mstore_def]
QED

Theorem nop_mcopy_always_ok[local]:
  !inst fuel ctx s.
    inst_wf inst /\
    EVERY (\op. ?v. op = Lit v) inst.inst_operands /\
    inst.inst_opcode = MCOPY ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  fs[step_inst_non_invoke, inst_wf_def] >>
  Cases_on `inst.inst_operands` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `t'` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  simp[step_inst_base_def, exec_write2_def, eval_operand_def, mcopy_def, LET_THM]
QED

Theorem nop_calldatacopy_always_ok[local]:
  !inst fuel ctx s.
    inst_wf inst /\
    EVERY (\op. ?v. op = Lit v) inst.inst_operands /\
    inst.inst_opcode = CALLDATACOPY ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  fs[step_inst_non_invoke, inst_wf_def] >>
  Cases_on `inst.inst_operands` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `t'` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  simp[step_inst_base_def, eval_operand_def, LET_THM]
QED


Theorem nop_dloadbytes_always_ok[local]:
  !inst fuel ctx s.
    inst_wf inst /\
    EVERY (\op. ?v. op = Lit v) inst.inst_operands /\
    inst.inst_opcode = DLOADBYTES ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  fs[step_inst_non_invoke, inst_wf_def] >>
  Cases_on `inst.inst_operands` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `t'` >> fs[EVERY_DEF] >>
  Cases_on `t` >> fs[EVERY_DEF] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  simp[step_inst_base_def, eval_operand_def, LET_THM]
QED
(* NOP'd instructions with literal operands always succeed (return OK).
   Key: eval_operand (Lit v) s = SOME v for any s. *)
Theorem nop_inst_always_ok[local]:
  !inst fuel ctx s.
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    EVERY (\op. ?v. op = Lit v) inst.inst_operands /\
    (inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} \/
     inst.inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}) ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >>
  gvs[] >>
  FIRST
    [irule nop_mload_always_ok >> fs[] >> NO_TAC,
     irule nop_calldataload_always_ok >> fs[] >> NO_TAC,
     irule nop_dload_always_ok >> fs[] >> NO_TAC,
     irule nop_mstore_always_ok >> fs[] >> NO_TAC,
     irule nop_mcopy_always_ok >> fs[] >> NO_TAC,
     irule nop_calldatacopy_always_ok >> fs[] >> NO_TAC,
     irule nop_dloadbytes_always_ok >> fs[] >> NO_TAC]
QED

(* Corollary: NOP'd or rep instructions from mode_inst_ok always succeed *)
Theorem mode_inst_ok_nop_or_rep_always_ok[local]:
  !nop_set rep_map fresh inst fuel ctx s.
    mode_inst_ok nop_set rep_map fresh inst /\
    (MEM inst.inst_id nop_set \/ ALOOKUP rep_map inst.inst_id <> NONE) ==>
    ?s'. step_inst fuel ctx inst s = OK s'
Proof
  rpt strip_tac >> fs[mode_inst_ok_def]
  >- (
    Cases_on `inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD}` >- (
      irule nop_inst_always_ok >> fs[]
    ) >> (
      irule nop_inst_always_ok >> res_tac >> fs[]))
  >> (
    Cases_on `ALOOKUP rep_map inst.inst_id` >> gvs[] >>
    res_tac >>
    irule nop_inst_always_ok >> fs[])
QED

(*   NOP'd/rep instructions are memory ops with literal operands (always OK).
   Identity instructions: non-volatile → no Abort; non-term non-INVOKE → OK/Error/Abort;
   combined: OK or Error. *)
Theorem mode_inst_ok_only_ok_or_error[local]:
  !nop_set rep_map fresh inst fuel ctx s.
    mode_inst_ok nop_set rep_map fresh inst ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[mode_inst_ok_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >>
  Cases_on `MEM inst.inst_id nop_set` >- (
    Cases_on `inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD}`
    >| [suspend "nop_load", suspend "nop_write"]
  ) >>
  Cases_on `ALOOKUP rep_map inst.inst_id`
  >| [suspend "identity", suspend "representative"]
QED

Resume mode_inst_ok_only_ok_or_error[nop_load]:
  fs[] >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  fs[step_inst_non_invoke, inst_wf_def] >>
  simp[step_inst_base_def, exec_read1_def] >>
  BasicProvers.every_case_tac
QED

Resume mode_inst_ok_only_ok_or_error[nop_write]:
  disj1_tac >>
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `inst`, `fuel`, `ctx`, `s`]
    mp_tac mode_inst_ok_nop_or_rep_always_ok >>
  (impl_tac >- fs[mode_inst_ok_def]) >>
  simp[]
QED

Resume mode_inst_ok_only_ok_or_error[identity]:
  qspecl_then [`fuel`, `ctx`, `inst`, `s`]
    mp_tac step_inst_non_term_non_invoke_only_ok_error_abort >>
  (impl_tac >- fs[]) >> strip_tac >> fs[] >>
  CCONTR_TAC >> fs[] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `a`, `s'`]
    mp_tac step_inst_non_volatile_no_abort >> simp[]
QED

Resume mode_inst_ok_only_ok_or_error[representative]:
  disj1_tac >>
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `inst`, `fuel`, `ctx`, `s`]
    mp_tac mode_inst_ok_nop_or_rep_always_ok >>
  (impl_tac >- fs[mode_inst_ok_def]) >>
  simp[]
QED

Finalise mode_inst_ok_only_ok_or_error;

(* Per-instruction error propagation for mode: if s1 errors on a mode_inst_ok
   instruction, the transformed s2 instructions also error.
   Key: NOP'd instructions always succeed (memory ops with literal operands).
   Rep instructions always succeed. Only identity instructions can error,
   and they run identically from memzero_inv states (non-volatile). *)
Theorem mode_inst_step_error_sim[local]:
  !nop_set rep_map fresh mode inst fuel ctx s1 s2.
    mode_inst_ok nop_set rep_map fresh inst /\
    memzero_inv fresh s1 s2 /\
    (!s1'. step_inst fuel ctx inst s1 <> OK s1')
    ==>
    !s2'. run_insts fuel ctx
      (apply_groups_inst mode nop_set rep_map inst) s2 <> OK s2'
Proof
  rpt strip_tac >>
  Cases_on `MEM inst.inst_id nop_set`
  >- (imp_res_tac mode_inst_ok_nop_or_rep_always_ok >> metis_tac[])
  >> (
    Cases_on `ALOOKUP rep_map inst.inst_id`
    >- ( (* Identity: non-volatile => same result on both sides *)
      fs[mode_inst_ok_def] >>
      gvs[apply_groups_inst_def, run_insts_def] >>
      qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `s2`, `fresh`]
        mp_tac non_vol_step_memzero_result >>
      (impl_tac >- fs[]) >> strip_tac >>
      Cases_on `step_inst fuel ctx inst s2` >> gvs[])
    >> (
      `?s'. step_inst fuel ctx inst s1 = OK s'` by (
        irule mode_inst_ok_nop_or_rep_always_ok >>
        qexistsl_tac [`fresh`, `nop_set`, `rep_map`] >> fs[]) >>
      metis_tac[]))
QED

(* List-level error propagation for mode transform *)
Theorem mode_run_insts_s1_fail_s2_fail[local]:
  !insts nop_set rep_map fresh mode fuel ctx s1 s2.
    memzero_inv fresh s1 s2 /\
    EVERY (mode_inst_ok nop_set rep_map fresh) insts /\
    (!s1'. run_insts fuel ctx insts s1 <> OK s1')
    ==>
    !s2'. run_insts fuel ctx
      (FLAT (MAP (apply_groups_inst mode nop_set rep_map) insts)) s2 <> OK s2'
Proof
  Induct >- simp[run_insts_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  rename1 `inst :: insts` >>
  fs[run_insts_def] >>
  Cases_on `step_inst fuel ctx inst s1`
  >- ( (* s1 head OK => s1 fails on tail *)
    rename1 `step_inst _ _ inst s1 = OK s1_mid` >>
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `mode`, `inst`, `fuel`, `ctx`,
      `s1`, `s1_mid`, `s2`] mp_tac mode_inst_step_sim >>
    (impl_tac >- fs[]) >> strip_tac >>
    rename1 `memzero_inv fresh s1_mid s2_mid` >>
    `!s1'. run_insts fuel ctx insts s1_mid <> OK s1'` by
      (fs[] >> metis_tac[]) >>
    first_x_assum (qspecl_then [`nop_set`, `rep_map`, `fresh`, `mode`, `fuel`,
      `ctx`, `s1_mid`, `s2_mid`] mp_tac) >>
    (impl_tac >- fs[]) >> strip_tac >>
    simp[FLAT, MAP] >>
    fs[run_insts_append] >>
    Cases_on `run_insts fuel ctx (apply_groups_inst mode nop_set rep_map inst) s2` >>
    gvs[])
  >> ( (* s1 head fails => s2 transformed head also fails *)
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `mode`, `inst`, `fuel`, `ctx`,
      `s1`, `s2`] mp_tac mode_inst_step_error_sim >>
    (impl_tac >- (fs[] >> Cases_on `step_inst fuel ctx inst s1` >> gvs[])) >>
    strip_tac >>
    simp[FLAT, MAP] >>
    drule_all run_insts_append_fail >> metis_tac[])
QED

(* Lift to run_insts: mode_inst_ok instructions only produce OK or Error *)
Theorem run_insts_mode_only_ok_or_error[local]:
  !insts nop_set rep_map fresh fuel ctx s.
    EVERY (mode_inst_ok nop_set rep_map fresh) insts ==>
    (?s'. run_insts fuel ctx insts s = OK s') \/
    (?e. run_insts fuel ctx insts s = Error e)
Proof
  Induct >> simp[run_insts_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `h`, `fuel`, `ctx`, `s`]
    mp_tac mode_inst_ok_only_ok_or_error >>
  (impl_tac >- fs[]) >> strip_tac >> fs[] >>
  simp[run_insts_def] >>
  first_x_assum (qspecl_then [`nop_set`, `rep_map`, `fresh`, `fuel`, `ctx`, `s'`]
    mp_tac) >>
  (impl_tac >- fs[]) >> metis_tac[]
QED

(* apply_groups_inst per-instruction only produces OK or Error *)
Theorem apply_groups_inst_run_only_ok_or_error[local]:
  !nop_set rep_map fresh mode inst fuel ctx s.
    mode_inst_ok nop_set rep_map fresh inst ==>
    (?s'. run_insts fuel ctx (apply_groups_inst mode nop_set rep_map inst) s = OK s') \/
    (?e. run_insts fuel ctx (apply_groups_inst mode nop_set rep_map inst) s = Error e)
Proof
  rpt strip_tac >>
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `inst`, `fuel`, `ctx`, `s`]
    mp_tac mode_inst_ok_only_ok_or_error >>
  (impl_tac >- fs[]) >> strip_tac
  >- (
    (* OK: mode_inst_step_sim gives transformed also OK *)
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `mode`, `inst`, `fuel`, `ctx`,
      `s`, `s'`, `s`] mp_tac mode_inst_step_sim >>
    (impl_tac >- fs[memzero_inv_refl]) >> strip_tac >> metis_tac[])
  >> (
    (* Error: 3 cases *)
    Cases_on `MEM inst.inst_id nop_set`
    >- ( (* NOP'd: always OK — contradicts Error *)
      `?s'. step_inst fuel ctx inst s = OK s'` by (
        irule mode_inst_ok_nop_or_rep_always_ok >>
        qexistsl_tac [`fresh`, `nop_set`, `rep_map`] >> fs[]) >>
      gvs[])
    >> (
      Cases_on `ALOOKUP rep_map inst.inst_id`
      >- ( (* Identity: run_insts [inst] = Error *)
        fs[mode_inst_ok_def] >>
        gvs[apply_groups_inst_def, run_insts_def])
      >> ( (* Rep: always OK — contradicts Error *)
        `?s'. step_inst fuel ctx inst s = OK s'` by (
          irule mode_inst_ok_nop_or_rep_always_ok >>
          qexistsl_tac [`fresh`, `nop_set`, `rep_map`] >> fs[]) >>
        gvs[])))
QED

(* Expanded (FLAT MAP) mode instructions only produce OK or Error *)
Theorem run_insts_expanded_mode_only_ok_or_error[local]:
  !insts nop_set rep_map fresh mode fuel ctx s.
    EVERY (mode_inst_ok nop_set rep_map fresh) insts ==>
    (?s'. run_insts fuel ctx
      (FLAT (MAP (apply_groups_inst mode nop_set rep_map) insts)) s = OK s') \/
    (?e. run_insts fuel ctx
      (FLAT (MAP (apply_groups_inst mode nop_set rep_map) insts)) s = Error e)
Proof
  Induct >> simp[run_insts_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  simp[run_insts_append] >>
  qspecl_then [`nop_set`, `rep_map`, `fresh`, `mode`, `h`, `fuel`, `ctx`, `s`]
    mp_tac apply_groups_inst_run_only_ok_or_error >>
  (impl_tac >- fs[]) >> strip_tac >> fs[] >>
  simp[run_insts_append] >>
  first_x_assum (qspecl_then [`nop_set`, `rep_map`, `fresh`, `mode`, `fuel`, `ctx`, `s'`]
    mp_tac) >>
  (impl_tac >- fs[]) >> metis_tac[]
QED

(* State convergence for mode: memzero_inv + memory convergence → state_equiv.
   Memory convergence is provided as a hypothesis from mode_block_wf,
   which captures the scanner's group coverage property. *)
Theorem mode_run_insts_state_equiv[local]:
  !nop_set rep_map fresh mode insts fuel ctx s s1' s2'.
    EVERY (mode_inst_ok nop_set rep_map fresh) insts /\
    run_insts fuel ctx insts s = OK s1' /\
    run_insts fuel ctx
      (FLAT (MAP (apply_groups_inst mode nop_set rep_map) insts)) s = OK s2' /\
    memzero_inv fresh s1' s2' /\
    s1'.vs_memory = s2'.vs_memory
    ==>
    state_equiv fresh s1' s2'
Proof
  metis_tac[memzero_inv_eq_mem_state_equiv]
QED

(* Mode lift_result: combines sim, error propagation, and convergence.
   Requires memory convergence hypothesis from mode_block_wf. *)
Theorem mode_run_insts_lift_result:
  !nop_set rep_map fresh mode insts fuel ctx s.
    EVERY (mode_inst_ok nop_set rep_map fresh) insts /\
    (!fuel ctx s s1' s2'.
       run_insts fuel ctx insts s = OK s1' /\
       run_insts fuel ctx
         (FLAT (MAP (apply_groups_inst mode nop_set rep_map) insts))
         s = OK s2'
       ==> s1'.vs_memory = s2'.vs_memory)
    ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (run_insts fuel ctx insts s)
      (run_insts fuel ctx
        (FLAT (MAP (apply_groups_inst mode nop_set rep_map) insts)) s)
Proof
  rpt strip_tac >>
  reverse (Cases_on `?s1'. run_insts fuel ctx insts s = OK s1'`)
  >- ( (* non-OK case *)
    fs[] >>
    `?e1. run_insts fuel ctx insts s = Error e1` by (
      qspecl_then [`insts`, `nop_set`, `rep_map`, `fresh`, `fuel`, `ctx`, `s`]
        mp_tac run_insts_mode_only_ok_or_error >>
      (impl_tac >- fs[]) >> metis_tac[]) >>
    qspecl_then [`insts`, `nop_set`, `rep_map`, `fresh`, `mode`,
      `fuel`, `ctx`, `s`, `s`] mp_tac mode_run_insts_s1_fail_s2_fail >>
    (impl_tac >- fs[memzero_inv_refl]) >> strip_tac >>
    `?e2. run_insts fuel ctx
        (FLAT (MAP (apply_groups_inst mode nop_set rep_map) insts)) s = Error e2` by (
      qspecl_then [`insts`, `nop_set`, `rep_map`, `fresh`, `mode`, `fuel`, `ctx`, `s`]
        mp_tac run_insts_expanded_mode_only_ok_or_error >>
      (impl_tac >- fs[]) >> metis_tac[]) >>
    gvs[lift_result_def])
  >> ( (* OK case *)
    fs[] >>
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `mode`, `insts`,
      `fuel`, `ctx`, `s`, `s`] mp_tac mode_run_insts_sim >>
    (impl_tac >- fs[memzero_inv_refl]) >>
    strip_tac >> gvs[] >>
    qspecl_then [`nop_set`, `rep_map`, `fresh`, `mode`, `insts`,
      `fuel`, `ctx`, `s`, `s1'`, `s2'`]
      mp_tac mode_run_insts_state_equiv >>
    (impl_tac >- (
      fs[] >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s1'`, `s2'`] mp_tac) >>
      fs[])) >>
    strip_tac >>
    simp[lift_result_def])
QED


(* Helper: transform_function uses function_map_transform *)
Theorem transform_function_eq:
  !fn. transform_function fn =
    function_map_transform (transform_block (dfg_build_function fn)) fn
Proof
  rw[transform_function_def, function_map_transform_def]
QED
