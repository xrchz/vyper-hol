(*
 * DFT Commutation Helpers
 *
 * Infrastructure for proving that independent instructions commute.
 * The key abstraction: step_inst_base (and step_inst for INVOKE)
 * commutes with update_var on variables not in the instruction's
 * operands or outputs. Combined with update_var commutativity on
 * disjoint keys, this gives the full independent_commute theorem.
 *
 * TOP-LEVEL:
 *   step_inst_frame        — frame lemma for step_inst (non-INVOKE)
 *   step_inst_invoke_frame  — frame lemma for INVOKE case
 *   step_inst_ok_frame      — unified frame lemma for OK results
 *   step_inst_base_frame    — frame lemma for step_inst_base
 *   map_result_state_def    — result-level map for threading state transforms
 *   resolve_phi_MEM         — resolve_phi returns a member of the operand list
 *)

Theory dftCommutation
Ancestors
  venomState venomExecSemantics venomExecProps venomEffects venomInst
  venomInstProofs finite_map list pair
Libs
  BasicProvers

(* ================================================================
   Basic variable infrastructure
   ================================================================ *)

(* eval_operand ignores update_var at unrelated keys *)
Theorem eval_operand_update_var:
  !op x v s. (!y. op = Var y ==> x <> y) ==>
  eval_operand op (update_var x v s) = eval_operand op s
Proof
  Cases_on `op` >>
  rw[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* eval_operands ignores update_var at unrelated keys *)
Theorem eval_operands_update_var:
  !ops x v s. (!y. MEM (Var y) ops ==> x <> y) ==>
  eval_operands ops (update_var x v s) = eval_operands ops s
Proof
  Induct >> rw[eval_operands_def] >>
  Cases_on `h` >> fs[eval_operand_def, update_var_def, lookup_var_def,
                      FLOOKUP_UPDATE]
QED

(* update_var on disjoint keys commutes *)
Theorem update_var_commutes:
  !x1 v1 x2 v2 s. x1 <> x2 ==>
  update_var x1 v1 (update_var x2 v2 s) =
  update_var x2 v2 (update_var x1 v1 s)
Proof
  rw[update_var_def] >>
  simp[venom_state_component_equality, FUPDATE_COMMUTES]
QED

(* FOLDL update_var commutes with unrelated update_var *)
Theorem foldl_update_var_commute:
  !kvs s x v. ~MEM x (MAP FST kvs) ==>
  FOLDL (\s' (k,val). update_var k val s') (update_var x v s) kvs =
  update_var x v (FOLDL (\s' (k,val). update_var k val s') s kvs)
Proof
  Induct >> rw[] >>
  PairCases_on `h` >> fs[MEM_MAP, FORALL_PROD] >>
  first_x_assum (qspecl_then [`update_var h0 h1 s`, `x`, `v`] mp_tac) >>
  rw[update_var_commutes]
QED

(* ================================================================
   update_var commutes with all state-modifying operations
   (because update_var only touches vs_vars)
   ================================================================ *)

Theorem update_var_mstore_commute:
  !x v off val s.
  update_var x v (mstore off val s) = mstore off val (update_var x v s)
Proof
  rw[update_var_def, mstore_def, venom_state_component_equality]
QED

Theorem update_var_istore_commute:
  !x v off val s.
  update_var x v (istore off val s) = istore off val (update_var x v s)
Proof
  rw[update_var_def, istore_def, mstore_def, venom_state_component_equality]
QED

Theorem update_var_mstore8_commute:
  !x v off val s.
  update_var x v (mstore8 off val s) = mstore8 off val (update_var x v s)
Proof
  rw[update_var_def, mstore8_def, venom_state_component_equality]
QED

Theorem update_var_sstore_commute:
  !x v k val s.
  update_var x v (sstore k val s) = sstore k val (update_var x v s)
Proof
  rw[update_var_def, sstore_def, venom_state_component_equality]
QED

Theorem update_var_tstore_commute:
  !x v k val s.
  update_var x v (tstore k val s) = tstore k val (update_var x v s)
Proof
  rw[update_var_def, tstore_def, venom_state_component_equality]
QED

Theorem update_var_write_memory_commute:
  !x v off bytes s.
  update_var x v (write_memory_with_expansion off bytes s) =
  write_memory_with_expansion off bytes (update_var x v s)
Proof
  rw[update_var_def, write_memory_with_expansion_def,
     venom_state_component_equality]
QED

Theorem update_var_mcopy_commute:
  !x v dst src sz s.
  update_var x v (mcopy dst src sz s) =
  mcopy dst src sz (update_var x v s)
Proof
  rw[update_var_def, mcopy_def, write_memory_with_expansion_def,
     venom_state_component_equality]
QED

Theorem pack_dret_dynamic_update_var[local]:
  !cursor pairs s x v.
    pack_dret_dynamic cursor pairs (update_var x v s) =
    let (ptrs, final_cursor, s') = pack_dret_dynamic cursor pairs s in
      (ptrs, final_cursor, update_var x v s')
Proof
  Induct_on `pairs`
  >- simp[pack_dret_dynamic_def]
  >> Cases_on `h`
  >> rpt gen_tac
  >> Cases_on
       `pack_dret_dynamic (cursor + n2w (ceil32 (w2n r))) pairs
          (mcopy (w2n cursor) (w2n q) (w2n r) s)`
  >> Cases_on `r''`
  >> gvs[Ntimes pack_dret_dynamic_def 2,
         GSYM update_var_mcopy_commute]
QED

Theorem update_var_halt_state_commute:
  !x v s.
  update_var x v (halt_state s) = halt_state (update_var x v s)
Proof
  rw[update_var_def, halt_state_def, venom_state_component_equality]
QED

Theorem update_var_revert_state_commute:
  !x v s.
  update_var x v (revert_state s) = revert_state (update_var x v s)
Proof
  rw[update_var_def, revert_state_def, venom_state_component_equality]
QED

Theorem update_var_set_returndata_commute:
  !x v rd s.
  update_var x v (set_returndata rd s) = set_returndata rd (update_var x v s)
Proof
  rw[update_var_def, set_returndata_def, venom_state_component_equality]
QED

Theorem update_var_jump_to_commute:
  !x v lbl s.
  update_var x v (jump_to lbl s) = jump_to lbl (update_var x v s)
Proof
  rw[update_var_def, jump_to_def, venom_state_component_equality]
QED

(* update_var commutes with arbitrary record field updates on non-vs_vars fields *)
Theorem update_var_with_immutables_commute:
  !x v imm s.
  update_var x v (s with vs_immutables := imm) =
  (update_var x v s) with vs_immutables := imm
Proof
  rw[update_var_def, venom_state_component_equality]
QED

Theorem update_var_with_logs_commute:
  !x v logs s.
  update_var x v (s with vs_logs := logs) =
  (update_var x v s) with vs_logs := logs
Proof
  rw[update_var_def, venom_state_component_equality]
QED

Theorem update_var_with_accounts_commute:
  !x v accts s.
  update_var x v (s with vs_accounts := accts) =
  (update_var x v s) with vs_accounts := accts
Proof
  rw[update_var_def, venom_state_component_equality]
QED

Theorem update_var_with_returndata_commute:
  !x v rd s.
  update_var x v (s with vs_returndata := rd) =
  (update_var x v s) with vs_returndata := rd
Proof
  rw[update_var_def, venom_state_component_equality]
QED

Theorem update_var_with_memory_commute:
  !x v mem s.
  update_var x v (s with vs_memory := mem) =
  (update_var x v s) with vs_memory := mem
Proof
  rw[update_var_def, venom_state_component_equality]
QED

Theorem update_var_with_transient_commute:
  !x v tr s.
  update_var x v (s with vs_transient := tr) =
  (update_var x v s) with vs_transient := tr
Proof
  rw[update_var_def, venom_state_component_equality]
QED

Theorem update_var_with_allocas_commute:
  !x v al s.
  update_var x v (s with vs_allocas := al) =
  (update_var x v s) with vs_allocas := al
Proof
  rw[update_var_def, venom_state_component_equality]
QED

Theorem update_var_with_alloca_next_commute:
  !x v n s.
  update_var x v (s with vs_alloca_next := n) =
  (update_var x v s) with vs_alloca_next := n
Proof
  rw[update_var_def, venom_state_component_equality]
QED

(* General: update_var commutes with multi-field record update *)
Theorem update_var_with_multi_commute:
  !x v s rd accts logs mem tr.
  update_var x v (s with <| vs_returndata := rd; vs_accounts := accts;
                             vs_logs := logs; vs_memory := mem;
                             vs_transient := tr |>) =
  (update_var x v s) with <| vs_returndata := rd; vs_accounts := accts;
                              vs_logs := logs; vs_memory := mem;
                              vs_transient := tr |>
Proof
  rw[update_var_def, venom_state_component_equality]
QED

(* ================================================================
   INVOKE pipeline commutes with unrelated update_var
   ================================================================ *)

Theorem setup_callee_update_var:
  !fn args s x v.
  setup_callee fn args (update_var x v s) = setup_callee fn args s
Proof
  rw[setup_callee_def, update_var_def, venom_state_component_equality]
QED

Theorem merge_callee_update_var:
  !s callee_s x v.
  merge_callee_state (update_var x v s) callee_s =
  update_var x v (merge_callee_state s callee_s)
Proof
  rw[merge_callee_state_def, update_var_def, venom_state_component_equality]
QED


Theorem adopt_return_fmp_update_var[local]:
  !ir x v s.
    adopt_return_fmp ir (update_var x v s) =
    update_var x v (adopt_return_fmp ir s)
Proof
  rpt strip_tac >>
  Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, update_var_def]
QED
Theorem bind_outputs_update_var:
  !outs vals s x v. ~MEM x outs ==>
  bind_outputs outs vals (update_var x v s) =
  OPTION_MAP (update_var x v) (bind_outputs outs vals s)
Proof
  rw[bind_outputs_def] >> rw[] >>
  rw[foldl_update_var_commute, MAP_ZIP]
QED

(* ================================================================
   Non-variable state fields are unchanged by update_var
   (needed to show state-reading ops are unaffected)
   ================================================================ *)

Theorem update_var_fields[simp]:
  (update_var x v s).vs_memory = s.vs_memory /\
  (update_var x v s).vs_transient = s.vs_transient /\
  (update_var x v s).vs_accounts = s.vs_accounts /\
  (update_var x v s).vs_returndata = s.vs_returndata /\
  (update_var x v s).vs_logs = s.vs_logs /\
  (update_var x v s).vs_immutables = s.vs_immutables /\
  (update_var x v s).vs_data_section = s.vs_data_section /\
  (update_var x v s).vs_labels = s.vs_labels /\
  (update_var x v s).vs_code = s.vs_code /\
  (update_var x v s).vs_params = s.vs_params /\
  (update_var x v s).vs_call_ctx = s.vs_call_ctx /\
  (update_var x v s).vs_tx_ctx = s.vs_tx_ctx /\
  (update_var x v s).vs_block_ctx = s.vs_block_ctx /\
  (update_var x v s).vs_prev_bb = s.vs_prev_bb /\
  (update_var x v s).vs_current_bb = s.vs_current_bb /\
  (update_var x v s).vs_inst_idx = s.vs_inst_idx /\
  (update_var x v s).vs_halted = s.vs_halted /\
  (update_var x v s).vs_prev_hashes = s.vs_prev_hashes /\
  (update_var x v s).vs_allocas = s.vs_allocas /\
  (update_var x v s).vs_alloca_next = s.vs_alloca_next
Proof
  rw[update_var_def]
QED

(* ================================================================
   Per-helper frame lemmas: each exec helper commutes with update_var
   ================================================================ *)

(* Result-level map for applying a state transform to exec_result values *)
Definition map_result_state_def:
  map_result_state f (OK s) = OK (f s) /\
  map_result_state f (Halt s) = Halt (f s) /\
  map_result_state f (Abort a s) = Abort a (f s) /\
  map_result_state f (IntRet vals s) = IntRet vals (f s) /\
  map_result_state f (Error e) = Error e
End

(* Key strategy: rewrite eval_operand through update_var FIRST,
   then the two sides become syntactically equal modulo update_var wrapping *)
Theorem exec_pure1_frame[local]:
  !f inst s x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  ~MEM x inst.inst_outputs ==>
  exec_pure1 f inst (update_var x v s) =
  map_result_state (update_var x v) (exec_pure1 f inst s)
Proof
  rw[exec_pure1_def] >>
  Cases_on `inst.inst_operands` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def, MEM, eval_operand_update_var] >>
  Cases_on `eval_operand h s` >> gvs[map_result_state_def] >>
  Cases_on `inst.inst_outputs` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def, MEM, update_var_commutes]
QED

Theorem exec_pure2_frame[local]:
  !f inst s x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  ~MEM x inst.inst_outputs ==>
  exec_pure2 f inst (update_var x v s) =
  map_result_state (update_var x v) (exec_pure2 f inst s)
Proof
  rw[exec_pure2_def] >>
  Cases_on `inst.inst_operands` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def] >>
  Cases_on `t'` >> gvs[map_result_state_def, MEM, eval_operand_update_var] >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h' s` >>
  gvs[map_result_state_def] >>
  Cases_on `inst.inst_outputs` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def, MEM, update_var_commutes]
QED

Theorem exec_pure3_frame[local]:
  !f inst s x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  ~MEM x inst.inst_outputs ==>
  exec_pure3 f inst (update_var x v s) =
  map_result_state (update_var x v) (exec_pure3 f inst s)
Proof
  rw[exec_pure3_def] >>
  Cases_on `inst.inst_operands` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def] >>
  Cases_on `t'` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def, MEM, eval_operand_update_var] >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h' s` >>
  Cases_on `eval_operand h'' s` >> gvs[map_result_state_def] >>
  Cases_on `inst.inst_outputs` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def, MEM, update_var_commutes]
QED

Theorem exec_read0_frame[local]:
  !f inst s x v.
  (!s0. f (update_var x v s0) = f s0) /\
  ~MEM x inst.inst_outputs ==>
  exec_read0 f inst (update_var x v s) =
  map_result_state (update_var x v) (exec_read0 f inst s)
Proof
  rw[exec_read0_def] >>
  Cases_on `inst.inst_outputs` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def, MEM, update_var_commutes]
QED

Theorem exec_read1_frame[local]:
  !f inst s x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  (!w s0. f w (update_var x v s0) = f w s0) /\
  ~MEM x inst.inst_outputs ==>
  exec_read1 f inst (update_var x v s) =
  map_result_state (update_var x v) (exec_read1 f inst s)
Proof
  rw[exec_read1_def] >>
  Cases_on `inst.inst_operands` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def, MEM, eval_operand_update_var] >>
  Cases_on `eval_operand h s` >> gvs[map_result_state_def] >>
  Cases_on `inst.inst_outputs` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def, MEM, update_var_commutes]
QED

Theorem exec_write2_frame[local]:
  !f inst s x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  (!v1 v2 s0. f v1 v2 (update_var x v s0) = update_var x v (f v1 v2 s0)) ==>
  exec_write2 f inst (update_var x v s) =
  map_result_state (update_var x v) (exec_write2 f inst s)
Proof
  rw[exec_write2_def] >>
  Cases_on `inst.inst_operands` >> gvs[map_result_state_def] >>
  Cases_on `t` >> gvs[map_result_state_def] >>
  Cases_on `t'` >> gvs[map_result_state_def, MEM, eval_operand_update_var] >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h' s` >>
  gvs[map_result_state_def]
QED

(* ================================================================
   step_inst_base frame lemma: update_var on unrelated variables
   threads through step_inst_base
   ================================================================ *)

(* ML tactic for step_inst_base_frame: process 92 opcodes.
   Strategy: unfold step_inst_base_def once on each side, case-split the opcode,
   then for helper cases use per-helper frame lemmas, for custom cases use
   eval_operand_update_var + commute lemmas + case splitting. *)

(* Frame lemmas for the exec_* helpers *)
val helper_frames = [
  exec_pure1_frame, exec_pure2_frame, exec_pure3_frame,
  exec_read0_frame, exec_read1_frame, exec_write2_frame
];

(* Rewrites for threading update_var through state operations *)
val update_var_rwts = [
  update_var_fields, update_var_commutes,
  update_var_mstore_commute, update_var_istore_commute,
  update_var_mstore8_commute, update_var_sstore_commute,
  update_var_tstore_commute, update_var_write_memory_commute,
  update_var_mcopy_commute, update_var_halt_state_commute,
  update_var_revert_state_commute, update_var_set_returndata_commute,
  update_var_jump_to_commute,
  update_var_with_immutables_commute, update_var_with_logs_commute,
  update_var_with_accounts_commute, update_var_with_returndata_commute,
  update_var_with_memory_commute, update_var_with_transient_commute,
  update_var_with_allocas_commute, update_var_with_alloca_next_commute,
  update_var_with_multi_commute
];

(* update_var is transparent to state-reading functions.
   These are needed to discharge exec_read0/1_frame hypotheses. *)
Theorem update_var_transparent[simp,local]:
  mload off (update_var x v s) = mload off s /\
  sload key (update_var x v s) = sload key s /\
  tload key (update_var x v s) = tload key s /\
  contract_storage (update_var x v s) = contract_storage s
Proof
  rw[mload_def, sload_def, tload_def, contract_storage_def,
     contract_transient_def, update_var_def]
QED

Theorem write_mem_expand_update_var[local]:
  (write_memory_with_expansion off bytes (update_var x v s)).vs_memory =
    (write_memory_with_expansion off bytes s).vs_memory
Proof
  rw[write_memory_with_expansion_def, update_var_def]
QED

(* resolve_phi returns an element of the operand list *)
Theorem resolve_phi_MEM:
  !prev ops op. resolve_phi prev ops = SOME op ==> MEM op ops
Proof
  recInduct resolve_phi_ind >>
  rw[resolve_phi_def] >> gvs[] >>
  res_tac >> gvs[]
QED

val helper_hyp_rwts = [update_var_transparent];

(* Wrapper: eval_operand on EL i t is unchanged by update_var when x not in t *)
Theorem eval_operand_update_var_el[local]:
  !t i x v s. ~MEM (Var x) t /\ i < LENGTH t ==>
    eval_operand (EL i t) (update_var x v s) = eval_operand (EL i t) s
Proof
  rpt strip_tac >> irule eval_operand_update_var >>
  rw[] >> CCONTR_TAC >> gvs[] >>
  `MEM (EL i t) t` by metis_tac[MEM_EL] >> gvs[]
QED


(* Wrapper: eval_operand on HD t is unchanged when x not in t *)
Theorem eval_operand_update_var_hd[local]:
  !t x v s. ~MEM (Var x) t /\ 0 < LENGTH t ==>
    eval_operand (HD t) (update_var x v s) = eval_operand (HD t) s
Proof
  Cases >> rw[] >> irule eval_operand_update_var >>
  rw[] >> CCONTR_TAC >> gvs[]
QED

(* Wrapper: eval_operands on DROP n t is unchanged when x not in t *)
Theorem eval_operands_update_var_drop[local]:
  !t n x v s. ~MEM (Var x) t ==>
    eval_operands (DROP n t) (update_var x v s) = eval_operands (DROP n t) s
Proof
  rpt strip_tac >> irule eval_operands_update_var >>
  rw[] >> CCONTR_TAC >> gvs[] >>
  metis_tac[rich_listTheory.MEM_DROP_IMP]
QED

(* Core rewrites for eval_operand and map_result_state *)
val core_rwts = [
  eval_operand_update_var,
  eval_operand_update_var_el, eval_operand_update_var_hd,
  eval_operands_update_var, eval_operands_update_var_drop,
  map_result_state_def
];

(* Definitions to unfold for custom (non-helper) cases *)
val custom_defs = [
  exec_ext_call_def, exec_delegatecall_def,
  exec_create_def, exec_alloca_def,
  extract_venom_result_def,
  make_venom_call_state_def, make_venom_delegatecall_state_def,
  make_venom_create_state_def,
  venom_to_tx_params_def, eval_operands_def,
  read_memory_def
];

val all_rwts = helper_frames @ update_var_rwts @ helper_hyp_rwts @ core_rwts;

(* Frame lemma for extract_venom_result: update_var threads through *)
Theorem extract_venom_result_update_var[local]:
  !s outf retOff retSize rr x v.
  extract_venom_result (update_var x v s) outf retOff retSize rr =
  OPTION_MAP (\(output, s'). (output, update_var x v s'))
    (extract_venom_result s outf retOff retSize rr)
Proof
  rw[extract_venom_result_def] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  rw[update_var_def, write_memory_with_expansion_def,
     venom_state_component_equality] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[]
QED

(* Shared proof for ext_call/delegatecall/create frame lemmas.
   Strategy: unfold the ext_call def, show make_*_state is unchanged
   by update_var (only reads non-var fields), then apply
   extract_venom_result_update_var and handle the OPTION_MAP. *)
fun ext_call_frame_proof defs =
  rpt strip_tac >>
  (* Unfold ext_call but NOT update_var — keep it abstract for rewriting *)
  simp(defs @ [read_memory_def, venom_to_tx_params_def, update_var_fields]) >>
  (* extract_venom_result_update_var fires here *)
  simp[extract_venom_result_update_var, optionTheory.OPTION_MAP_DEF,
       pairTheory.UNCURRY] >>
  (* Case split on extract_venom_result *)
  BasicProvers.TOP_CASE_TAC >> gvs[map_result_state_def] >>
  (* Decompose the pair z *)
  Cases_on `z` >> gvs[map_result_state_def] >>
  (* Case split on inst_outputs *)
  BasicProvers.TOP_CASE_TAC >> gvs[map_result_state_def] >>
  BasicProvers.TOP_CASE_TAC >> gvs[map_result_state_def, update_var_commutes];

(* Frame lemma for exec_ext_call *)
Theorem exec_ext_call_frame[local]:
  !inst s gas addr value ao as_ ro rs is_static x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  ~MEM x inst.inst_outputs ==>
  exec_ext_call inst (update_var x v s) gas addr value ao as_ ro rs is_static =
  map_result_state (update_var x v)
    (exec_ext_call inst s gas addr value ao as_ ro rs is_static)
Proof
  ext_call_frame_proof [exec_ext_call_def, make_venom_call_state_def]
QED

(* Frame lemma for exec_delegatecall *)
Theorem exec_delegatecall_frame[local]:
  !inst s gas addr ao as_ ro rs x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  ~MEM x inst.inst_outputs ==>
  exec_delegatecall inst (update_var x v s) gas addr ao as_ ro rs =
  map_result_state (update_var x v)
    (exec_delegatecall inst s gas addr ao as_ ro rs)
Proof
  ext_call_frame_proof [exec_delegatecall_def, make_venom_delegatecall_state_def]
QED

(* Frame lemma for exec_create *)
Theorem exec_create_frame[local]:
  !inst s value offset sz salt_opt x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  ~MEM x inst.inst_outputs ==>
  exec_create inst (update_var x v s) value offset sz salt_opt =
  map_result_state (update_var x v)
    (exec_create inst s value offset sz salt_opt)
Proof
  ext_call_frame_proof [exec_create_def, make_venom_create_state_def]
QED

val ext_call_frames = [
  exec_ext_call_frame, exec_delegatecall_frame, exec_create_frame
];

val all_rwts2 = all_rwts @ ext_call_frames;

(* Per-opcode tactic: helper frames + ext_call frames + custom defs.
   Uses TRY/NO_TAC safety net to prevent partial application. *)
(* PHI-specific: resolve_phi result's eval_operand ignores update_var *)
Theorem resolve_phi_eval_operand_update_var[local]:
  !prev ops val_op x v s.
    resolve_phi prev ops = SOME val_op /\
    ~MEM (Var x) ops ==>
    eval_operand val_op (update_var x v s) = eval_operand val_op s
Proof
  rpt strip_tac >>
  irule eval_operand_update_var >> rw[] >>
  CCONTR_TAC >> gvs[] >>
  imp_res_tac resolve_phi_MEM >> gvs[]
QED

val base_frame_tac =
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  gvs all_rwts2 >>
  TRY (gvs(all_rwts2 @ custom_defs) >>
       rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >>
                          gvs(all_rwts2 @ custom_defs))));

Theorem step_inst_base_frame:
  !inst s x v.
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  ~MEM x inst.inst_outputs ==>
  step_inst_base inst (update_var x v s) =
  map_result_state (update_var x v) (step_inst_base inst s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode`
  >- base_frame_tac (* ADD *)
  >- base_frame_tac (* SUB *)
  >- base_frame_tac (* MUL *)
  >- base_frame_tac (* Div *)
  >- base_frame_tac (* SDIV *)
  >- base_frame_tac (* Mod *)
  >- base_frame_tac (* SMOD *)
  >- base_frame_tac (* Exp *)
  >- base_frame_tac (* ADDMOD *)
  >- base_frame_tac (* MULMOD *)
  >- base_frame_tac (* EQ *)
  >- base_frame_tac (* LT *)
  >- base_frame_tac (* GT *)
  >- base_frame_tac (* SLT *)
  >- base_frame_tac (* SGT *)
  >- base_frame_tac (* ISZERO *)
  >- base_frame_tac (* AND *)
  >- base_frame_tac (* OR *)
  >- base_frame_tac (* XOR *)
  >- base_frame_tac (* NOT *)
  >- base_frame_tac (* SHL *)
  >- base_frame_tac (* SHR *)
  >- base_frame_tac (* SAR *)
  >- base_frame_tac (* SIGNEXTEND *)
  >- base_frame_tac (* BYTE *)
  >- base_frame_tac (* MLOAD *)
  >- base_frame_tac (* MSTORE *)
  >- base_frame_tac (* MSTORE8 *)
  >- base_frame_tac (* MCOPY *)
  >- base_frame_tac (* MEMTOP *)
  >- base_frame_tac (* SLOAD *)
  >- base_frame_tac (* SSTORE *)
  >- base_frame_tac (* TLOAD *)
  >- base_frame_tac (* TSTORE *)
  >- base_frame_tac (* ILOAD *)
  >- base_frame_tac (* ISTORE *)
  >- base_frame_tac (* JMP *)
  >- base_frame_tac (* JNZ *)
  >- base_frame_tac (* DJMP *)
  >- base_frame_tac (* RET *)
  >- base_frame_tac (* RETURN *)
  >- base_frame_tac (* REVERT *)
  >- base_frame_tac (* STOP *)
  >- base_frame_tac (* SINK *)
  >- (base_frame_tac >>
      imp_res_tac resolve_phi_eval_operand_update_var >>
      gvs all_rwts2) (* PHI *)
  >- base_frame_tac (* PARAM *)
  >- base_frame_tac (* ASSIGN *)
  >- base_frame_tac (* NOP *)
  >- base_frame_tac (* ALLOCA *)
  >- (base_frame_tac >>
      gvs[update_var_def, venom_state_component_equality]) (* DALLOCA *)
  >- (base_frame_tac >>
      gvs[pack_dret_dynamic_update_var, update_var_def,
          venom_state_component_equality] >>
      rpt (pairarg_tac >>
           gvs[map_result_state_def, update_var_def,
               venom_state_component_equality]) >>
      gvs[map_result_state_def, update_var_def,
          venom_state_component_equality]) (* DRET *)
  >- (base_frame_tac >> gvs[update_var_def]) (* GETFMP *)
  >- (base_frame_tac >>
      gvs[update_var_def, venom_state_component_equality]) (* SETFMP *)
  >- (base_frame_tac >> gvs[update_var_def]) (* RETFMP *)
  >- (base_frame_tac >> gvs[update_var_def]) (* INITIAL_FMP *)
  >- base_frame_tac (* BUMP *)
  >- base_frame_tac (* INVOKE *)
  >- base_frame_tac (* FMP_PARAM *)
  >- (base_frame_tac >> gvs[update_var_def]) (* RETPC_PARAM *)
  >- base_frame_tac (* CALLER *)
  >- base_frame_tac (* CALLVALUE *)
  >- base_frame_tac (* CALLDATALOAD *)
  >- base_frame_tac (* CALLDATASIZE *)
  >- base_frame_tac (* CALLDATACOPY *)
  >- base_frame_tac (* ADDRESS *)
  >- base_frame_tac (* ORIGIN *)
  >- base_frame_tac (* GASPRICE *)
  >- base_frame_tac (* GAS *)
  >- base_frame_tac (* GASLIMIT *)
  >- base_frame_tac (* COINBASE *)
  >- base_frame_tac (* TIMESTAMP *)
  >- base_frame_tac (* NUMBER *)
  >- base_frame_tac (* PREVRANDAO *)
  >- base_frame_tac (* CHAINID *)
  >- base_frame_tac (* SELFBALANCE *)
  >- base_frame_tac (* BALANCE *)
  >- base_frame_tac (* BLOCKHASH *)
  >- base_frame_tac (* BASEFEE *)
  >- base_frame_tac (* CODESIZE *)
  >- base_frame_tac (* CODECOPY *)
  >- base_frame_tac (* EXTCODESIZE *)
  >- base_frame_tac (* EXTCODEHASH *)
  >- base_frame_tac (* EXTCODECOPY *)
  >- base_frame_tac (* RETURNDATASIZE *)
  >- base_frame_tac (* RETURNDATACOPY *)
  >- base_frame_tac (* BLOBHASH *)
  >- base_frame_tac (* BLOBBASEFEE *)
  >- base_frame_tac (* SHA3 *)
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      gvs all_rwts2 >>
      rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> gvs all_rwts2)))
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      gvs all_rwts2 >>
      rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> gvs all_rwts2)))
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      gvs all_rwts2 >>
      rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> gvs all_rwts2)))
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      gvs all_rwts2 >>
      rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> gvs all_rwts2)))
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      gvs all_rwts2 >>
      rpt (CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> gvs all_rwts2)))
  >- base_frame_tac (* LOG *)
  >- base_frame_tac (* SELFDESTRUCT *)
  >- base_frame_tac (* INVALID *)
  >- base_frame_tac (* ASSERT *)
  >- base_frame_tac (* ASSERT_UNREACHABLE *)
  >- base_frame_tac (* DLOAD *)
  >- base_frame_tac (* DLOADBYTES *)
  >- base_frame_tac (* OFFSET *)
QED

(* step_inst_frame: update_var x v commutes through step_inst for non-INVOKE.
   INVOKE has a different frame property (see step_inst_invoke_frame).
   Works for all non-INVOKE opcodes including ALLOCA (update_var only touches
   vs_vars, which step_inst_base doesn't depend on for ALLOCA). *)
Theorem step_inst_frame:
  !fuel ctx inst s x v.
    (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
    ~MEM x inst.inst_outputs /\
    inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst (update_var x v s) =
    map_result_state (update_var x v) (step_inst fuel ctx inst s)
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_frame]
QED

(* step_inst_invoke_frame: for INVOKE, update_var threads through OK results.
   Non-OK results (Halt/Abort) return the callee state unchanged. *)
Theorem step_inst_invoke_frame:
  !fuel ctx inst s x v.
    (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
    ~MEM x inst.inst_outputs /\
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst (update_var x v s) =
    (case step_inst fuel ctx inst s of
       OK s' => OK (update_var x v s')
     | Halt s' => Halt s'
     | Abort a s' => Abort a s'
     | IntRet vals s' => IntRet vals s'
     | Error e => Error e)
Proof
  rpt strip_tac >>
  simp[step_inst_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `decode_invoke inst = SOME p` >>
  PairCases_on `p` >> simp[] >>
  `inst.inst_operands = Label p0 :: p1`
    by (gvs[decode_invoke_def] >>
        Cases_on `inst.inst_operands` >> gvs[] >>
        Cases_on `h` >> gvs[]) >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  `eval_operands p1 (update_var x v s) = eval_operands p1 s`
    by (irule eval_operands_update_var >> rw[] >> gvs[MEM]) >>
  simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  simp[setup_callee_update_var] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  simp[merge_callee_update_var, adopt_return_fmp_update_var,
       bind_outputs_update_var] >>
  Cases_on
    `bind_outputs inst.inst_outputs i.iret_values
       (adopt_return_fmp i (merge_callee_state s v'))` >>
  gvs[]
QED


(* step_inst_ok_frame: unified frame lemma for OK results.
   Works for all opcodes (including INVOKE and ALLOCA) when step_inst returns OK.
   update_var only touches vs_vars; step_inst_base_frame handles non-INVOKE
   (including ALLOCA), step_inst_invoke_frame handles INVOKE. *)
Theorem step_inst_ok_frame:
  !fuel ctx inst s s' x v.
    step_inst fuel ctx inst s = OK s' /\
    (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
    ~MEM x inst.inst_outputs ==>
    step_inst fuel ctx inst (update_var x v s) = OK (update_var x v s')
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (imp_res_tac step_inst_invoke_frame >> gvs[])
  >- (gvs[step_inst_non_invoke, step_inst_base_frame, map_result_state_def])
QED
