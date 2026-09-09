(*
 * SSA Renamed Instruction Simulation
 *
 * Proves step_inst_base_renamed_sim: stepping a renamed instruction
 * (same opcode, renamed operands/outputs via sigma) on ssa_sim-related
 * states produces ssa_sim-related results.
 *
 * Uses ssaRenamedSimLib for per-opcode step_inst_base reduction.
 *)

Theory ssaRenamedSim
Ancestors
  ssaSimDefs venomExecSemantics venomInst venomState opcodeClass
  list rich_list finite_map pred_set
Libs
  ssaRenamedSimLib

(* ==========================================================================
   exec_* Category Helpers for renamed instructions
   
   Pattern: unfold exec helper, use eval_operand_renamed for operand
   agreement, use ssa_sim_update_var for output agreement.
   ========================================================================== *)

(* Common tactic for exec helpers that produce one output variable *)
(* After unfolding: case split, eval_operand agreement, ssa_sim_update_var *)

Triviality exec_pure1_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_pure1 f inst1 s1 = OK s1' ==>
    ?s2'. exec_pure1 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_pure1_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_pure2_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_pure2 f inst1 s1 = OK s1' ==>
    ?s2'. exec_pure2 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_pure2_def] >>
  Cases_on `inst1.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `eval_operand h s1` >> gvs[] >>
  Cases_on `eval_operand h' s1` >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  Cases_on `inst1.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `inst2.inst_outputs` >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_pure3_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_pure3 f inst1 s1 = OK s1' ==>
    ?s2'. exec_pure3 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_pure3_def] >>
  Cases_on `inst1.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `eval_operand h s1` >> gvs[] >>
  Cases_on `eval_operand h' s1` >> gvs[] >>
  Cases_on `eval_operand h'' s1` >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  Cases_on `inst1.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `inst2.inst_outputs` >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_read0_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    f s1 = f s2 /\
    exec_read0 f inst1 s1 = OK s1' ==>
    ?s2'. exec_read0 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_read0_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_read1_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    (!v. f v s1 = f v s2) /\
    exec_read1 f inst1 s1 = OK s1' ==>
    ?s2'. exec_read1 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_read1_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_mload_renamed:
  !inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_read1 (\addr s. mload (w2n addr) s) inst1 s1 = OK s1' ==>
    ?s2'. exec_read1 (\addr s. mload (w2n addr) s) inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rpt gen_tac >> strip_tac >>
  irule exec_read1_renamed >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `s1` >> gvs[ssa_sim_def, mload_def]
QED

(* exec_write2: no output variable, modifies state *)
Triviality exec_write2_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    (!v1 v2. ssa_sim sigma (f v1 v2 s1) (f v1 v2 s2)) /\
    exec_write2 f inst1 s1 = OK s1' ==>
    ?s2'. exec_write2 f inst2 s2 = OK s2' /\
          ssa_sim sigma s1' s2'
Proof
  rw[exec_write2_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[]
QED

(* Helper: ssa_sim implies all non-var state fields agree *)
Triviality ssa_sim_fields:
  !sigma s1 s2. ssa_sim sigma s1 s2 ==>
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    (s1.vs_halted <=> s2.vs_halted) /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb
Proof
  rw[ssa_sim_def]
QED

(* ==========================================================================
   External call helpers
   
   Under ssa_sim, all non-var state fields are equal, so:
   - make_venom_*_state produces identical EVM states
   - extract_venom_result produces ssa_sim-related output states
   ========================================================================== *)

(* Under ssa_sim, make_venom_call_state is identical *)
Triviality make_venom_call_state_ssa_sim:
  !sigma s1 s2 target gas value calldata code is_static.
    ssa_sim sigma s1 s2 ==>
    make_venom_call_state s1 target gas value calldata code is_static =
    make_venom_call_state s2 target gas value calldata code is_static
Proof
  rw[ssa_sim_def, make_venom_call_state_def, LET_THM, venom_to_tx_params_def]
QED

Triviality make_venom_delegatecall_state_ssa_sim:
  !sigma s1 s2 target gas calldata code is_static.
    ssa_sim sigma s1 s2 ==>
    make_venom_delegatecall_state s1 target gas calldata code is_static =
    make_venom_delegatecall_state s2 target gas calldata code is_static
Proof
  rw[ssa_sim_def, make_venom_delegatecall_state_def, LET_THM,
     venom_to_tx_params_def]
QED

Triviality make_venom_create_state_ssa_sim:
  !sigma s1 s2 new_address gas value init_code.
    ssa_sim sigma s1 s2 ==>
    make_venom_create_state s1 new_address gas value init_code =
    make_venom_create_state s2 new_address gas value init_code
Proof
  rw[ssa_sim_def, make_venom_create_state_def, LET_THM,
     venom_to_tx_params_def]
QED

(* extract_venom_result preserves ssa_sim: if the run_result is the same
   and input states are ssa_sim-related, output states are too. *)
Triviality extract_venom_result_ssa_sim:
  !sigma s1 s2 output_val retOff retSize run_result output s1'.
    ssa_sim sigma s1 s2 /\
    extract_venom_result s1 output_val retOff retSize run_result =
      SOME (output, s1') ==>
    ?s2'. extract_venom_result s2 output_val retOff retSize run_result =
            SOME (output, s2') /\
          ssa_sim sigma s1' s2'
Proof
  rw[extract_venom_result_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac ssa_sim_fields >>
  simp[ssa_sim_def, lookup_var_def,
       write_memory_with_expansion_def, LET_THM] >>
  gvs[ssa_sim_def, lookup_var_def]
QED

(* exec_ext_call simulation *)
Triviality exec_ext_call_renamed:
  !sigma inst1 inst2 s1 s2 s1' gas addr_w value ao as_ ro rs is_static.
    ssa_sim sigma s1 s2 /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_ext_call inst1 s1 gas addr_w value ao as_ ro rs is_static = OK s1' ==>
    ?s2'. exec_ext_call inst2 s2 gas addr_w value ao as_ ro rs is_static = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_ext_call_def, LET_THM] >>
  imp_res_tac ssa_sim_fields >> gvs[read_memory_def] >>
  `make_venom_call_state s1 (w2w addr_w) (w2n gas) (w2n value)
     (TAKE (w2n as_) (DROP (w2n ao) s2.vs_memory ++ REPLICATE (w2n as_) 0w))
     (lookup_account (w2w addr_w) s2.vs_accounts).code is_static =
   make_venom_call_state s2 (w2w addr_w) (w2n gas) (w2n value)
     (TAKE (w2n as_) (DROP (w2n ao) s2.vs_memory ++ REPLICATE (w2n as_) 0w))
     (lookup_account (w2w addr_w) s2.vs_accounts).code is_static` by
    metis_tac[make_venom_call_state_ssa_sim] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule_all extract_venom_result_ssa_sim >> strip_tac >> gvs[] >>
  irule ssa_sim_update_var >> gvs[] >>
  gvs[extract_venom_result_def, AllCaseEqs(), LET_THM, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* exec_delegatecall simulation *)
Triviality exec_delegatecall_renamed:
  !sigma inst1 inst2 s1 s2 s1' gas addr_w ao as_ ro rs.
    ssa_sim sigma s1 s2 /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_delegatecall inst1 s1 gas addr_w ao as_ ro rs = OK s1' ==>
    ?s2'. exec_delegatecall inst2 s2 gas addr_w ao as_ ro rs = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_delegatecall_def, LET_THM] >>
  imp_res_tac ssa_sim_fields >> gvs[read_memory_def] >>
  `make_venom_delegatecall_state s1 (w2w addr_w) (w2n gas)
     (TAKE (w2n as_) (DROP (w2n ao) s2.vs_memory ++ REPLICATE (w2n as_) 0w))
     (lookup_account (w2w addr_w) s2.vs_accounts).code
     s2.vs_call_ctx.cc_static =
   make_venom_delegatecall_state s2 (w2w addr_w) (w2n gas)
     (TAKE (w2n as_) (DROP (w2n ao) s2.vs_memory ++ REPLICATE (w2n as_) 0w))
     (lookup_account (w2w addr_w) s2.vs_accounts).code
     s2.vs_call_ctx.cc_static` by
    metis_tac[make_venom_delegatecall_state_ssa_sim] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule_all extract_venom_result_ssa_sim >> strip_tac >> gvs[] >>
  irule ssa_sim_update_var >> gvs[] >>
  gvs[extract_venom_result_def, AllCaseEqs(), LET_THM, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* exec_create simulation *)
Triviality exec_create_renamed:
  !sigma inst1 inst2 s1 s2 s1' value offset sz salt_opt.
    ssa_sim sigma s1 s2 /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (!x. lookup_var x s1 <> NONE /\ x <> HD inst1.inst_outputs ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_create inst1 s1 value offset sz salt_opt = OK s1' ==>
    ?s2'. exec_create inst2 s2 value offset sz salt_opt = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_create_def, LET_THM] >>
  imp_res_tac ssa_sim_fields >> gvs[read_memory_def] >>
  `make_venom_create_state s1
     (case salt_opt of
        NONE => address_for_create s2.vs_call_ctx.cc_address
          (lookup_account s2.vs_call_ctx.cc_address s2.vs_accounts).nonce
      | SOME salt => address_for_create2 s2.vs_call_ctx.cc_address salt
          (TAKE (w2n sz) (DROP (w2n offset) s2.vs_memory ++ REPLICATE (w2n sz) 0w)))
     (s2.vs_call_ctx.cc_gas - s2.vs_call_ctx.cc_gas DIV 64)
     (w2n value) (TAKE (w2n sz) (DROP (w2n offset) s2.vs_memory ++ REPLICATE (w2n sz) 0w)) =
   make_venom_create_state s2
     (case salt_opt of
        NONE => address_for_create s2.vs_call_ctx.cc_address
          (lookup_account s2.vs_call_ctx.cc_address s2.vs_accounts).nonce
      | SOME salt => address_for_create2 s2.vs_call_ctx.cc_address salt
          (TAKE (w2n sz) (DROP (w2n offset) s2.vs_memory ++ REPLICATE (w2n sz) 0w)))
     (s2.vs_call_ctx.cc_gas - s2.vs_call_ctx.cc_gas DIV 64)
     (w2n value) (TAKE (w2n sz) (DROP (w2n offset) s2.vs_memory ++ REPLICATE (w2n sz) 0w))` by (
    Cases_on `salt_opt` >> simp[] >>
    metis_tac[make_venom_create_state_ssa_sim]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule_all extract_venom_result_ssa_sim >> strip_tac >> gvs[] >>
  irule ssa_sim_update_var >> gvs[] >>
  gvs[extract_venom_result_def, AllCaseEqs(), LET_THM, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Under ssa_sim, vs_alloca_next is equal *)
Triviality vs_alloca_next_ssa_sim:
  !sigma s1 s2. ssa_sim sigma s1 s2 ==>
    s1.vs_alloca_next = s2.vs_alloca_next
Proof
  rw[ssa_sim_def]
QED

(* ssa_sim preserved by identical vs_allocas + vs_alloca_next update *)
Triviality ssa_sim_allocas_update:
  !sigma s1 s2 X Y.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (s1 with <| vs_allocas := X; vs_alloca_next := Y |>)
                  (s2 with <| vs_allocas := X; vs_alloca_next := Y |>)
Proof
  rw[ssa_sim_def, lookup_var_def]
QED

(* One-output opcodes expose the legacy HD-shaped freshness fact consumed by
   the existing execution-category helpers. *)
Triviality output_fresh_one:
  !sigma inst1 inst2 s1.
    output_fresh sigma inst1 inst2 s1 /\
    bound_output_count inst1.inst_opcode = 1 ==>
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs)
Proof
  rw[output_fresh_def] >>
  first_x_assum (qspecl_then [`0`, `x`] mp_tac) >>
  gvs[EL, HD] >> disch_then irule >>
  Cases_on `inst1.inst_outputs` >> gvs[]
QED

Triviality output_sigma_fresh_one:
  !sigma inst1 inst2 s1.
    output_fresh sigma inst1 inst2 s1 /\
    bound_output_count inst1.inst_opcode = 1 ==>
    output_sigma inst1.inst_opcode inst1.inst_outputs inst2.inst_outputs sigma =
      (HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma
Proof
  rw[output_fresh_def] >> irule output_sigma_one >>
  gvs[] >>
  Cases_on `inst1.inst_outputs` >> Cases_on `inst2.inst_outputs` >> gvs[]
QED

(* ==========================================================================
   Main theorem: step_inst_base_renamed_sim
   Uses STEP_BASE_REDUCE_TAC from ssaRenamedSimLib to avoid expanding
   the monolithic step_inst_base_def across many goals.
   ========================================================================== *)

(* Two ordered variable updates, in the exact shape used by BUMP. *)
Triviality ssa_sim_update_var2:
  !sigma s1 s2 ptr next h h' v1 v2.
    ssa_sim sigma s1 s2 /\ h <> h' /\
    (!i x. i < 2 /\ lookup_var x s1 <> NONE /\
           x <> EL i [ptr; next] ==>
           sigma x <> EL i [h; h']) ==>
    ssa_sim ((next =+ h') ((ptr =+ h) sigma))
      (update_var next v2 (update_var ptr v1 s1))
      (update_var h' v2 (update_var h v1 s2))
Proof
  rpt strip_tac >>
  `ssa_sim
     (FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma
        (ZIP ([ptr; next], [h; h'])))
     (FOLDL (\st (nm,vl). update_var nm vl st) s1
        (ZIP ([ptr; next], [v1; v2])))
     (FOLDL (\st (nm,vl). update_var nm vl st) s2
        (ZIP ([h; h'], [v1; v2])))` by
    (irule foldl_update_var_ssa_sim >> simp[]) >>
  gvs[]
QED

Theorem step_inst_base_renamed_sim:
  !sigma inst1 inst2 s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    output_fresh sigma inst1 inst2 s1 /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    inst1.inst_opcode <> PHI /\
    inst1.inst_opcode <> ASSIGN /\
    step_inst_base inst1 s1 = OK s1' ==>
    ?s2'. step_inst_base inst2 s2 = OK s2' /\
          ssa_sim (output_sigma inst1.inst_opcode
                     inst1.inst_outputs inst2.inst_outputs sigma)
                  s1' s2'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[inst_renamed_def] >>
  Cases_on `inst1.inst_opcode` >>
  gvs[is_terminator_def, bound_output_count_def, opcode_has_output_def] >>
  imp_res_tac output_fresh_one >>
  imp_res_tac output_sigma_fresh_one >>
  gvs[output_fresh_def, bound_output_count_def, opcode_has_output_def] >>
  simp[output_sigma_zero, bound_output_count_def, opcode_has_output_def] >>
  gvs (List.take (step_base_reduces, 10)) >>
  gvs (List.take (List.drop (step_base_reduces, 10), 10)) >>
  gvs (List.take (List.drop (step_base_reduces, 20), 10)) >>
  gvs (List.take (List.drop (step_base_reduces, 30), 10)) >>
  gvs (List.take (List.drop (step_base_reduces, 40), 10)) >>
  gvs (List.take (List.drop (step_base_reduces, 50), 10)) >>
  gvs (List.take (List.drop (step_base_reduces, 60), 10)) >>
  gvs (List.take (List.drop (step_base_reduces, 70), 10)) >>
  gvs (List.take (List.drop (step_base_reduces, 80), 10)) >>
  gvs (List.drop (step_base_reduces, 90)) >>
  (* Phase 1: pure opcodes — closed by drule_all + simp[opcode_has_output_def] *)
  TRY (drule_all exec_pure2_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  TRY (drule_all exec_pure1_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  TRY (drule_all exec_pure3_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  (* Phase 2: remaining goals — get field equalities, unfold defs *)
  imp_res_tac ssa_sim_fields >>
  imp_res_tac vs_alloca_next_ssa_sim >>
  TRY (simp[opcode_has_output_def] >>
       irule exec_read0_renamed >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexists_tac `s1` >> gvs[] >> NO_TAC) >>
  TRY (simp[opcode_has_output_def] >>
       irule exec_read1_renamed >>
       conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexists_tac `s1` >>
       gvs[mload_def, sload_def, tload_def,
           contract_storage_def, contract_transient_def] >> NO_TAC) >>
  TRY (simp[opcode_has_output_def] >>
       irule exec_write2_renamed >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexists_tac `s1` >>
       gvs[mstore_def, istore_def, mstore8_def, sstore_def, tstore_def,
           contract_storage_def, contract_transient_def,
           ssa_sim_def] >> NO_TAC) >>
  gvs[exec_read0_def] >>
  gvs[exec_read1_def] >>
  gvs[exec_write2_def] >>
  gvs[exec_alloca_def] >>
  gvs[LET_THM] >>
  gvs[AllCaseEqs()] >>
  gvs[renamed_operand_def] >>
  TRY (imp_res_tac eval_operand_renamed >> gvs[]) >>
  TRY (imp_res_tac eval_operands_renamed >> gvs[]) >>
  (* Phase 3: ext calls — drule_all + simp[opcode_has_output_def] *)
  TRY (drule_all exec_ext_call_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  TRY (drule_all exec_delegatecall_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  TRY (drule_all exec_create_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  (* Phase 4: normalize mapped operands before exposing singleton outputs. *)
  gvs[EL_MAP, GSYM MAP_DROP] >>
  (* Phase 5: use output lengths to expose singleton outputs. *)
  gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  (* Resolve opcode_has_output for remaining opcodes *)
  gvs[opcode_has_output_def] >>
  (* Phase 6a: ALLOCA — needs combined allocas + var update *)
  TRY (irule ssa_sim_update_var >> gvs[lookup_var_def] >>
       irule ssa_sim_allocas_update >> gvs[] >> NO_TAC) >>
  (* Phase 6b: output-producing opcodes *)
  TRY (gvs[mload_def, sload_def, tload_def, contract_storage_def,
           contract_transient_def] >>
       irule ssa_sim_update_var >> gvs[lookup_var_def] >> NO_TAC) >>
  (* Phase 7: LOG needs Cases_on rest to simplify HD (MAP f rest) *)
  TRY (Cases_on `rest` >> gvs[]) >>
  (* DALLOCA updates the synchronized free-memory pointer and one output. *)
  TRY (irule ssa_sim_fmp_update_var >> gvs[] >> NO_TAC) >>
  (* Metadata reads only update one corresponding fresh variable. *)
  TRY (irule ssa_sim_update_var >> gvs[lookup_var_def] >> NO_TAC) >>
  (* Dedicated two-output BUMP simulation at the ssa_sim abstraction boundary. *)
  TRY (irule ssa_sim_update_var2 >> gvs[] >> NO_TAC) >>
  (* Phase 8: state-modifying / trivial — sigma unchanged (opcode_has_output = F) *)
  gvs[mcopy_def, write_memory_with_expansion_def] >>
  gvs[mload_def, mstore_def, istore_def, mstore8_def] >>
  gvs[sload_def, sstore_def, contract_storage_def] >>
  gvs[tload_def, tstore_def, contract_transient_def] >>
  gvs[ssa_sim_def] >>
  (* Finish residual synchronized metadata reads after record normalization. *)
  TRY (rpt strip_tac >>
       gvs[FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM] >> NO_TAC) >>
  gvs[update_var_def, lookup_var_def] >>
  (* Pointwise variable-map obligations for one-output metadata/FMP updates. *)
  TRY (rpt strip_tac >> Cases_on `x = out` >>
       gvs[FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM] >> NO_TAC) >>
  (* BUMP binds two outputs in order; indexed freshness discharges both map updates. *)
  TRY (Cases_on `next_out = ptr_out` >>
       gvs[FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM] >>
       rpt strip_tac >>
       Cases_on `x = ptr_out` >>
       gvs[FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM] >>
       Cases_on `x = next_out` >>
       gvs[FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM] >>
       qpat_assum `!i x. _` (qspecl_then [`0`, `x`] mp_tac) >>
       qpat_assum `!i x. _` (qspecl_then [`1`, `x`] mp_tac) >>
       simp[] >> NO_TAC) >>
  gvs[GSYM MAP_APPEND, rich_listTheory.MAP_HD] >>
  TRY (qmatch_goalsub_abbrev_tac `s2.vs_logs ++ [log_entry] = _` >>
       qexists_tac `s2 with vs_logs := s2.vs_logs ++ [log_entry]` >>
       simp[Abbr`log_entry`] >>
       qexists_tac `off` >>
       `MAP (renamed_operand sigma) l1 ++
          [renamed_operand sigma h; renamed_operand sigma h'] =
        MAP (renamed_operand sigma) (l1 ++ [h; h'])` by simp[] >>
       ASM_REWRITE_TAC[] >>
       simp[rich_listTheory.MAP_HD, ssa_sim_def, lookup_var_def] >> NO_TAC)
QED

(* ==========================================================================
   Terminator simulation: step_terminator_ssa_sim
   
   Like step_inst_base_renamed_sim but for terminators. Returns
   ssa_result_equiv since terminators produce mixed result types
   (OK for jumps, Halt for stop/return, Abort for revert, IntRet for ret).
   
   Assumes original doesn't error (all operands defined). Error case is
   handled separately at the run_block level.
   ========================================================================== *)

(* extract_labels is invariant under MAP (renamed_operand sigma) *)
Triviality extract_labels_renamed:
  !ops sigma.
    extract_labels (MAP (renamed_operand sigma) ops) = extract_labels ops
Proof
  Induct >> rw[extract_labels_def, renamed_operand_def, MAP] >>
  Cases_on `h` >> rw[renamed_operand_def, extract_labels_def]
QED

(* Common setup for terminator simulation: strip, expand inst_renamed,
   get ssa_sim field equalities, reduce step_inst_base per opcode. *)
val term_setup_tac =
  rpt gen_tac >> strip_tac >>
  gvs[inst_renamed_def] >>
  imp_res_tac ssa_sim_fields;

(* After setup + step_base_reduces for a specific opcode:
   1. Split inst1.inst_operands (determines BOTH sides since MAP preserves structure)
   2. gvs to simplify renamed_operand + eliminate Error branches
   3. Split eval_operand results, bridge with eval_operand_renamed
   4. Close remaining goals *)
(* resolve_cases_tac: like every_case_tac but lighter.
   Splits conclusion-side case expressions only (via TOP_CASE_TAC),
   then uses gvs to simplify and eliminate Error/contradiction branches.
   The ssa_result_equiv_def + renamed_operand_def in gvs ensure that after
   both sides resolve to constructors, the result matches. *)
val term_resolve_pre_tac =
  gvs[renamed_operand_def, extract_labels_renamed];

val term_resolve_case_tac =
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[ssa_result_equiv_def, renamed_operand_def, extract_labels_renamed,
      execution_equiv_UNIV, halt_state_def, set_returndata_def,
      revert_state_def] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[ssa_result_equiv_def, renamed_operand_def, extract_labels_renamed,
      execution_equiv_UNIV, halt_state_def, set_returndata_def,
      revert_state_def] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[ssa_result_equiv_def, renamed_operand_def, extract_labels_renamed,
      execution_equiv_UNIV, halt_state_def, set_returndata_def,
      revert_state_def] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[ssa_result_equiv_def, renamed_operand_def, extract_labels_renamed,
      execution_equiv_UNIV, halt_state_def, set_returndata_def,
      revert_state_def];

val term_resolve_post_tac =
  TRY (imp_res_tac eval_operand_renamed >> gvs[]) >>
  TRY (imp_res_tac eval_operands_renamed >> gvs[execution_equiv_UNIV]) >>
  TRY (qexists_tac `sigma` >> irule jump_to_ssa_sim >> simp[]) >>
  gvs[ssa_result_equiv_def, execution_equiv_UNIV, halt_state_def,
      set_returndata_def, revert_state_def, ssa_sim_def];

val term_resolve_tac =
  term_resolve_pre_tac >>
  term_resolve_case_tac >> term_resolve_case_tac >>
  term_resolve_case_tac >> term_resolve_case_tac >> term_resolve_post_tac;

(* Split into per-terminator trivialities to avoid every_case_tac on 7+ goals *)
Triviality step_term_jmp:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = JMP /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_pre_tac >>
  term_resolve_case_tac >> term_resolve_case_tac >>
  term_resolve_case_tac >> term_resolve_case_tac >> term_resolve_post_tac
QED

Triviality step_term_jnz:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = JNZ /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_pre_tac >>
  term_resolve_case_tac >> term_resolve_case_tac >>
  term_resolve_case_tac >> term_resolve_case_tac >> term_resolve_post_tac
QED

Triviality step_term_djmp:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = DJMP /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_ret:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = RET /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_return:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = RETURN /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_revert:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = REVERT /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_selfdestruct:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = SELFDESTRUCT /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_stop:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = STOP /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_sink:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = SINK /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_invalid:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = INVALID /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_retfmp:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = RETFMP /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality mcopy_ssa_sim:
  !sigma dst src sz s1 s2.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (mcopy dst src sz s1) (mcopy dst src sz s2)
Proof
  rw[ssa_sim_def, mcopy_def, write_memory_with_expansion_def, lookup_var_def]
QED

Triviality pack_dret_dynamic_ssa_sim:
  !sigma cursor pairs s1 s2 p1 c1 s1' p2 c2 s2'.
    ssa_sim sigma s1 s2 /\
    pack_dret_dynamic cursor pairs s1 = (p1,c1,s1') /\
    pack_dret_dynamic cursor pairs s2 = (p2,c2,s2') ==>
    p1 = p2 /\ c1 = c2 /\ ssa_sim sigma s1' s2'
Proof
  Induct_on `pairs` >- gvs[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Ntimes pack_dret_dynamic_def 2] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[mcopy_ssa_sim]
QED

Triviality parse_dret_shape_renamed:
  !sigma inst1 inst2.
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands ==>
    parse_dret_shape inst2 = parse_dret_shape inst1
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst1.inst_operands` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def] >>
  Cases_on `h` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def, renamed_operand_def]
QED

Triviality step_term_dret:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = DRET /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >>
  `parse_dret_shape inst2 = parse_dret_shape inst1` by
    metis_tac[parse_dret_shape_renamed] >>
  gvs step_base_reduces >> term_resolve_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  `ssa_sim sigma s1 s2` by gvs[ssa_sim_def] >>
  drule_all pack_dret_dynamic_ssa_sim >> strip_tac >>
  gvs[ssa_result_equiv_def, execution_equiv_UNIV, ssa_sim_def]
QED

val step_term_lemmas = [step_term_jmp, step_term_jnz, step_term_djmp,
  step_term_ret, step_term_return, step_term_revert, step_term_selfdestruct,
  step_term_stop, step_term_sink, step_term_invalid];

Theorem step_terminator_ssa_sim:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst1.inst_opcode` >> gvs[is_terminator_def] >>
  TRY (drule_all step_term_jmp >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_jnz >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_djmp >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_ret >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_return >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_revert >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_selfdestruct >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_stop >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_sink >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_retfmp >> simp[] >> NO_TAC) >>
  TRY (drule_all step_term_dret >> simp[] >> NO_TAC) >>
  drule_all step_term_invalid >> simp[]
QED

(* For terminators returning OK, the input sigma is preserved.
   Only JMP/JNZ/DJMP return OK (via jump_to); all others return
   Halt/Abort/IntRet/Error. jump_to_ssa_sim preserves sigma. *)
Theorem step_terminator_ok_preserves_sim:
  !sigma inst1 inst2 s1 s2 v v'.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    step_inst_base inst1 s1 = OK v /\
    step_inst_base inst2 s2 = OK v' ==>
    ssa_sim sigma v v'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[inst_renamed_def] >>
  imp_res_tac ssa_sim_fields >>
  Cases_on `inst1.inst_opcode` >> gvs[is_terminator_def] >>
  gvs step_base_reduces >>
  gvs[renamed_operand_def, extract_labels_renamed, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  TRY (imp_res_tac eval_operand_renamed >> gvs[AllCaseEqs()]) >>
  TRY (irule jump_to_ssa_sim >> simp[])
QED

(* For non-terminator, non-INVOKE: if step_inst_base aborts on side 1,
   the renamed instruction also aborts with same reason + execution_equiv.
   Only ASSERT, ASSERT_UNREACHABLE, RETURNDATACOPY can abort among
   non-terminators — all depend on operand values (same by ssa_sim). *)
Theorem step_base_abort_sim:
  !sigma inst1 inst2 s1 s2 a s1'.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    step_inst_base inst1 s1 = Abort a s1' ==>
    ?s2'. step_inst_base inst2 s2 = Abort a s2' /\
          execution_equiv UNIV s1' s2'
Proof
  rpt gen_tac >> strip_tac >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[inst_renamed_def, is_terminator_def] >>
  imp_res_tac ssa_sim_fields >>
  gvs step_base_reduces >>
  gvs[exec_write2_def, AllCaseEqs(), LET_THM, renamed_operand_def] >>
  TRY (imp_res_tac eval_operand_renamed >> gvs[]) >>
  TRY (imp_res_tac eval_operands_renamed >> gvs[]) >>
  irule ssa_sim_implies_exec_equiv_UNIV >>
  gvs[ssa_sim_def, halt_state_def, revert_state_def, set_returndata_def,
      lookup_var_def] >>
  metis_tac[]
QED
