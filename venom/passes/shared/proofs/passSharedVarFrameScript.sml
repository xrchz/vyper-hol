(*
 * Pass Shared Variable Frame Properties
 *
 * Variable-frame theorems for instruction execution: unreferenced variable
 * updates pass through step_inst_base and step_inst.
 *
 * TOP-LEVEL EXPORTS:
 *   step_inst_base_var_frame_full — var update passes through step_inst_base
 *   step_inst_var_frame_full — var update passes through step_inst
 *)

Theory passSharedVarFrame
Ancestors
  passSharedDefs venomExecSemantics venomState venomInst venomEffects venomInstProps
  opcodeClass dftCommutation

(* ===================================================================== *)
(* ===== Variable/State Helpers ======================================== *)
(* ===================================================================== *)

Theorem update_var_commutes[local]:
  !x y vx vy s. x <> y ==>
    update_var x vx (update_var y vy s) =
    update_var y vy (update_var x vx s)
Proof
  simp[update_var_def, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem eval_operand_update_other[local]:
  !op y v s.
    ~MEM y (operand_vars [op]) ==>
    eval_operand op (update_var y v s) = eval_operand op s
Proof
  Cases >> rw[eval_operand_def, operand_vars_def, operand_var_def,
              lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem eval_operand_update_other_list[local]:
  !ops x v s.
    ~MEM x (operand_vars ops) ==>
    !op. MEM op ops ==>
    eval_operand op (update_var x v s) = eval_operand op s
Proof
  Induct >> rw[operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_vars_def] >>
  Cases_on `op = h` >> gvs[] >>
  TRY (Cases_on `h` >> gvs[operand_var_def, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  metis_tac[]
QED

Theorem eval_operands_update_var[local]:
  !ops x v s.
    ~MEM x (operand_vars ops) ==>
    eval_operands ops (update_var x v s) = eval_operands ops s
Proof
  Induct >> rw[eval_operands_def, operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_vars_def] >>
  `~MEM x (operand_vars [h])` by
    (rw[operand_vars_def] >> Cases_on `operand_var h` >> gvs[]) >>
  imp_res_tac eval_operand_update_other >> gvs[]
QED

Theorem resolve_phi_mem[local]:
  !prev ops val_op.
    resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  recInduct resolve_phi_ind >> rw[resolve_phi_def] >> gvs[AllCaseEqs()]
QED

val operand_vars_drop = prove(
  ``!ops x n. ~MEM x (operand_vars ops) ==>
              ~MEM x (operand_vars (DROP n ops))``,
  Induct >> rw[operand_vars_def] >>
  Cases_on `n` >> gvs[] >>
  Cases_on `operand_var h` >> gvs[operand_vars_def]);

(* ===================================================================== *)
(* ===== Non-terminator result type elimination ======================== *)
(* ===================================================================== *)

val step_base_result_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])));

Triviality exec_result_helpers_not_intret[simp]:
  (!f inst s vs s'. exec_pure1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure2 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure3 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read0 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_write2 f inst s <> IntRet vs s') /\
  (!inst s alloc_size vs s'. exec_alloca inst s alloc_size <> IntRet vs s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_not_intret[simp]:
  (!inst s g a v ao as_ ro rs is_s vs s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> IntRet vs s') /\
  (!inst s g a ao as_ ro rs vs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> IntRet vs s') /\
  (!inst s v off sz salt vs s'.
     exec_create inst s v off sz salt <> IntRet vs s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_no_halt_abort[simp]:
  (!inst s g a v ao as_ ro rs is_s s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Halt s') /\
  (!inst s g a v ao as_ ro rs is_s ab s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Abort ab s') /\
  (!inst s g a ao as_ ro rs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Halt s') /\
  (!inst s g a ao as_ ro rs ab s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Abort ab s') /\
  (!inst s v off sz salt s'.
     exec_create inst s v off sz salt <> Halt s') /\
  (!inst s v off sz salt ab s'.
     exec_create inst s v off sz salt <> Abort ab s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Theorem step_inst_base_no_halt[local]:
  !inst s s'.
    step_inst_base inst s = Halt s' ==>
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  drule step_inst_base_halt_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem step_inst_base_no_intret[local]:
  !inst s vs s'.
    step_inst_base inst s = IntRet vs s' ==>
    is_terminator inst.inst_opcode
Proof
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def]
QED

(* ===================================================================== *)
(* ===== External call update_var lemmas =============================== *)
(* ===================================================================== *)

val exec_ext_call_update_var = prove(
  ``!inst x w s g a v ao as_ ro rs is_s.
    ~MEM x inst.inst_outputs ==>
    exec_ext_call inst (update_var x w s) g a v ao as_ ro rs is_s =
    case exec_ext_call inst s g a v ao as_ ro rs is_s of
      OK s' => OK (update_var x w s')
    | Error e => Error e
    | Abort ab s' => Abort ab (update_var x w s')
    | Halt s' => Halt (update_var x w s')
    | IntRet vs s' => IntRet vs (update_var x w s')``,
  rw[exec_ext_call_def, read_memory_def, update_var_def,
     make_venom_call_state_def, venom_to_tx_params_def,
     extract_venom_result_def, write_memory_with_expansion_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[finite_mapTheory.FUPDATE_COMMUTES]);

val exec_delegatecall_update_var = prove(
  ``!inst x w s g a ao as_ ro rs.
    ~MEM x inst.inst_outputs ==>
    exec_delegatecall inst (update_var x w s) g a ao as_ ro rs =
    case exec_delegatecall inst s g a ao as_ ro rs of
      OK s' => OK (update_var x w s')
    | Error e => Error e
    | Abort ab s' => Abort ab (update_var x w s')
    | Halt s' => Halt (update_var x w s')
    | IntRet vs s' => IntRet vs (update_var x w s')``,
  rw[exec_delegatecall_def, read_memory_def, update_var_def,
     make_venom_delegatecall_state_def, venom_to_tx_params_def,
     extract_venom_result_def, write_memory_with_expansion_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[finite_mapTheory.FUPDATE_COMMUTES]);

val exec_create_update_var = prove(
  ``!inst x w s v off sz salt.
    ~MEM x inst.inst_outputs ==>
    exec_create inst (update_var x w s) v off sz salt =
    case exec_create inst s v off sz salt of
      OK s' => OK (update_var x w s')
    | Error e => Error e
    | Abort ab s' => Abort ab (update_var x w s')
    | Halt s' => Halt (update_var x w s')
    | IntRet vs s' => IntRet vs (update_var x w s')``,
  rw[exec_create_def, update_var_def,
     make_venom_create_state_def, venom_to_tx_params_def,
     extract_venom_result_def, write_memory_with_expansion_def,
     read_memory_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[finite_mapTheory.FUPDATE_COMMUTES]);

val wmwe_update_var = prove(
  ``!x w off dat s.
    write_memory_with_expansion off dat (update_var x w s) =
    update_var x w (write_memory_with_expansion off dat s)``,
  rw[write_memory_with_expansion_def, update_var_def]);

Triviality mcopy_update_var[local]:
  !x w dst src sz st.
    mcopy dst src sz (update_var x w st) =
    update_var x w (mcopy dst src sz st)
Proof
  simp[mcopy_def, wmwe_update_var, update_var_def]
QED

val exec_call_var_thms =
  [exec_ext_call_update_var, exec_delegatecall_update_var,
   exec_create_update_var, wmwe_update_var, mcopy_update_var];

Definition var_frame_result_def:
  var_frame_result x w (OK st) = OK (update_var x w st) /\
  var_frame_result x w (Abort a st) = Abort a (update_var x w st) /\
  var_frame_result x w (Error e) = Error e /\
  var_frame_result x w (Halt st) = Halt st /\
  var_frame_result x w (IntRet vals st) = IntRet vals st
End

Triviality exec_pure1_var_frame[local]:
  !f inst x w st.
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs ==>
    exec_pure1 f inst (update_var x w st) =
    var_frame_result x w (exec_pure1 f inst st)
Proof
  rpt strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op (update_var x w st) = eval_operand op st`
    by metis_tac[eval_operand_update_other_list] >>
  rw[exec_pure1_def, var_frame_result_def] >>
  Cases_on `inst.inst_operands` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def] >>
  Cases_on `eval_operand h st` >> gvs[var_frame_result_def] >>
  Cases_on `inst.inst_outputs` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def, update_var_def,
                         finite_mapTheory.FUPDATE_COMMUTES]
QED

Triviality exec_pure2_var_frame[local]:
  !f inst x w st.
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs ==>
    exec_pure2 f inst (update_var x w st) =
    var_frame_result x w (exec_pure2 f inst st)
Proof
  rpt strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op (update_var x w st) = eval_operand op st`
    by metis_tac[eval_operand_update_other_list] >>
  rw[exec_pure2_def, var_frame_result_def] >>
  Cases_on `inst.inst_operands` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def] >>
  Cases_on `t'` >> gvs[var_frame_result_def] >>
  Cases_on `eval_operand h st` >>
  Cases_on `eval_operand h' st` >> gvs[var_frame_result_def] >>
  Cases_on `inst.inst_outputs` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def, update_var_def,
                         finite_mapTheory.FUPDATE_COMMUTES]
QED

Triviality exec_pure3_var_frame[local]:
  !f inst x w st.
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs ==>
    exec_pure3 f inst (update_var x w st) =
    var_frame_result x w (exec_pure3 f inst st)
Proof
  rpt strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op (update_var x w st) = eval_operand op st`
    by metis_tac[eval_operand_update_other_list] >>
  rw[exec_pure3_def, var_frame_result_def] >>
  Cases_on `inst.inst_operands` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def] >>
  Cases_on `t'` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def] >>
  Cases_on `eval_operand h st` >>
  Cases_on `eval_operand h' st` >>
  Cases_on `eval_operand h'' st` >> gvs[var_frame_result_def] >>
  Cases_on `inst.inst_outputs` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def, update_var_def,
                         finite_mapTheory.FUPDATE_COMMUTES]
QED

Triviality exec_read0_var_frame[local]:
  !f inst x w st.
    (!s0. f (update_var x w s0) = f s0) /\
    ~MEM x inst.inst_outputs ==>
    exec_read0 f inst (update_var x w st) =
    var_frame_result x w (exec_read0 f inst st)
Proof
  rw[exec_read0_def, var_frame_result_def] >>
  Cases_on `inst.inst_outputs` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def, update_var_def,
                         finite_mapTheory.FUPDATE_COMMUTES]
QED

Triviality exec_read1_var_frame[local]:
  !f inst x w st.
    (!a s0. f a (update_var x w s0) = f a s0) /\
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs ==>
    exec_read1 f inst (update_var x w st) =
    var_frame_result x w (exec_read1 f inst st)
Proof
  rpt strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op (update_var x w st) = eval_operand op st`
    by metis_tac[eval_operand_update_other_list] >>
  rw[exec_read1_def, var_frame_result_def] >>
  Cases_on `inst.inst_operands` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def] >>
  Cases_on `eval_operand h st` >> gvs[var_frame_result_def] >>
  Cases_on `inst.inst_outputs` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def, update_var_def,
                         finite_mapTheory.FUPDATE_COMMUTES]
QED

Triviality exec_write2_var_frame[local]:
  !f inst x w st.
    (!a b s0. f a b (update_var x w s0) = update_var x w (f a b s0)) /\
    ~MEM x (operand_vars inst.inst_operands) ==>
    exec_write2 f inst (update_var x w st) =
    var_frame_result x w (exec_write2 f inst st)
Proof
  rpt strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op (update_var x w st) = eval_operand op st`
    by metis_tac[eval_operand_update_other_list] >>
  rw[exec_write2_def, var_frame_result_def] >>
  Cases_on `inst.inst_operands` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def] >>
  Cases_on `t'` >> gvs[var_frame_result_def] >>
  Cases_on `eval_operand h st` >>
  Cases_on `eval_operand h' st` >> gvs[var_frame_result_def]
QED

Triviality exec_alloca_var_frame[local]:
  !inst x w st alloc_size.
    ~MEM x inst.inst_outputs ==>
    exec_alloca inst (update_var x w st) alloc_size =
    var_frame_result x w (exec_alloca inst st alloc_size)
Proof
  rw[exec_alloca_def, var_frame_result_def] >>
  Cases_on `inst.inst_outputs` >> gvs[var_frame_result_def] >>
  Cases_on `t` >> gvs[var_frame_result_def] >>
  Cases_on `FLOOKUP st.vs_allocas inst.inst_id` >>
  gvs[var_frame_result_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE,
      finite_mapTheory.FUPDATE_COMMUTES] >>
  Cases_on `x'` >> gvs[var_frame_result_def, update_var_def,
                         finite_mapTheory.FUPDATE_COMMUTES]
QED

Triviality exec_ext_call_var_frame[local]:
  !inst x w s g a v ao as_ ro rs is_s.
    ~MEM x inst.inst_outputs ==>
    exec_ext_call inst (update_var x w s) g a v ao as_ ro rs is_s =
    var_frame_result x w (exec_ext_call inst s g a v ao as_ ro rs is_s)
Proof
  rpt strip_tac >>
  simp[exec_ext_call_update_var] >>
  Cases_on `exec_ext_call inst s g a v ao as_ ro rs is_s` >>
  gvs[var_frame_result_def]
QED

Triviality exec_delegatecall_var_frame[local]:
  !inst x w s g a ao as_ ro rs.
    ~MEM x inst.inst_outputs ==>
    exec_delegatecall inst (update_var x w s) g a ao as_ ro rs =
    var_frame_result x w (exec_delegatecall inst s g a ao as_ ro rs)
Proof
  rpt strip_tac >>
  simp[exec_delegatecall_update_var] >>
  Cases_on `exec_delegatecall inst s g a ao as_ ro rs` >>
  gvs[var_frame_result_def]
QED

Triviality exec_create_var_frame[local]:
  !inst x w s v off sz salt.
    ~MEM x inst.inst_outputs ==>
    exec_create inst (update_var x w s) v off sz salt =
    var_frame_result x w (exec_create inst s v off sz salt)
Proof
  rpt strip_tac >>
  simp[exec_create_update_var] >>
  Cases_on `exec_create inst s v off sz salt` >>
  gvs[var_frame_result_def]
QED

val exec_frame_thms =
  [exec_pure1_var_frame, exec_pure2_var_frame, exec_pure3_var_frame,
   exec_read0_var_frame, exec_read1_var_frame, exec_write2_var_frame,
   exec_alloca_var_frame, exec_ext_call_var_frame,
   exec_delegatecall_var_frame, exec_create_var_frame];

Triviality mem_var_operand_vars[local]:
  !ops x. MEM (Var x) ops ==> MEM x (operand_vars ops)
Proof
  Induct >> rw[operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_var_def]
QED

(* ===================================================================== *)
(* ===== step_inst_base_var_frame_full ================================= *)
(* ===================================================================== *)

(* Full var-frame for step_inst_base: all result types.
   Directly proved without intermediate OK-only lemma.
   Strategy: case split on result type, then handle each. *)
Theorem step_inst_base_var_frame_result[local]:
  !inst x w st.
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs /\
    ~is_terminator inst.inst_opcode ==>
    step_inst_base inst (update_var x w st) =
    var_frame_result x w (step_inst_base inst st)
Proof
  rpt strip_tac >>
  `!y. MEM (Var y) inst.inst_operands ==> x <> y` by
    metis_tac[mem_var_operand_vars] >>
  `step_inst_base inst (update_var x w st) =
   dftCommutation$map_result_state (update_var x w)
     (step_inst_base inst st)` by
    (irule dftCommutationTheory.step_inst_base_frame >> gvs[]) >>
  Cases_on `step_inst_base inst st` >>
  gvs[dftCommutationTheory.map_result_state_def, var_frame_result_def] >>
  imp_res_tac step_inst_base_no_halt >>
  imp_res_tac step_inst_base_no_intret >>
  gvs[]
QED

Theorem step_inst_base_var_frame_full:
  !inst x w st.
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs /\
    ~is_terminator inst.inst_opcode ==>
    step_inst_base inst (update_var x w st) =
    case step_inst_base inst st of
      OK st' => OK (update_var x w st')
    | Abort a st' => Abort a (update_var x w st')
    | Error e => Error e
    | Halt st' => Halt st'
    | IntRet vs st' => IntRet vs st'
Proof
  rpt strip_tac >>
  drule_all step_inst_base_var_frame_result >>
  Cases_on `step_inst_base inst st` >> gvs[var_frame_result_def] >>
  metis_tac[step_inst_base_no_halt, step_inst_base_no_intret]
QED

(* ===================================================================== *)
(* ===== INVOKE helpers ================================================ *)
(* ===================================================================== *)

Theorem setup_callee_update_var[local]:
  !fn args x w s.
    setup_callee fn args (update_var x w s) = setup_callee fn args s
Proof
  rw[setup_callee_def, update_var_def]
QED

Theorem merge_callee_update_var[local]:
  !x w caller callee.
    merge_callee_state (update_var x w caller) callee =
    update_var x w (merge_callee_state caller callee)
Proof
  rw[merge_callee_state_def, update_var_def]
QED

Theorem foldl_update_var_comm[local]:
  !pairs x w s.
    ~MEM x (MAP FST pairs) ==>
    FOLDL (\s' (out,val). update_var out val s') (update_var x w s) pairs =
    update_var x w (FOLDL (\s' (out,val). update_var out val s') s pairs)
Proof
  Induct >> rw[] >>
  Cases_on `h` >> gvs[] >>
  first_x_assum (qspecl_then [`x`, `w`, `update_var q r s`] mp_tac) >>
  rw[update_var_commutes]
QED

Theorem bind_outputs_update_var[local]:
  !outs vals x w s.
    ~MEM x outs /\ LENGTH outs = LENGTH vals ==>
    bind_outputs outs vals (update_var x w s) =
    OPTION_MAP (update_var x w) (bind_outputs outs vals s)
Proof
  rw[bind_outputs_def] >>
  irule foldl_update_var_comm >>
  `MAP FST (ZIP (outs,vals)) = outs` suffices_by gvs[] >>
  irule (cj 1 listTheory.MAP_ZIP) >> gvs[]
QED


Triviality adopt_return_fmp_update_var[local]:
  !ir x w s.
    adopt_return_fmp ir (update_var x w s) =
    update_var x w (adopt_return_fmp ir s)
Proof
  rpt strip_tac >>
  Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, update_var_def]
QED
(* ===================================================================== *)
(* ===== step_inst_var_frame_full ====================================== *)
(* ===================================================================== *)

Theorem step_inst_var_frame_full:
  !fuel ctx inst x w st.
    ~MEM x (operand_vars inst.inst_operands) /\
    ~MEM x inst.inst_outputs /\
    ~is_terminator inst.inst_opcode ==>
    step_inst fuel ctx inst (update_var x w st) =
    case step_inst fuel ctx inst st of
      OK st' => OK (update_var x w st')
    | Abort a st' =>
        if inst.inst_opcode = INVOKE then Abort a st'
        else Abort a (update_var x w st')
    | Error e => Error e
    | Halt st' => Halt st'
    | IntRet vs st' => IntRet vs st'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  (* INVOKE *)
  >- (simp[step_inst_def] >>
      `!op. MEM op inst.inst_operands ==>
            eval_operand op (update_var x w st) = eval_operand op st`
        by metis_tac[eval_operand_update_other_list] >>
      Cases_on `decode_invoke inst` >> gvs[] >>
      Cases_on `x'` >> gvs[] >>
      rename1 `SOME (callee_name, arg_ops)` >>
      `inst.inst_operands = Label callee_name :: arg_ops`
        by gvs[decode_invoke_def, AllCaseEqs()] >>
      `~MEM x (operand_vars arg_ops)` by
        gvs[operand_vars_def, operand_var_def] >>
      `eval_operands arg_ops (update_var x w st) =
       eval_operands arg_ops st`
        by (irule eval_operands_update_var >> gvs[]) >>
      Cases_on `lookup_function callee_name ctx.ctx_functions` >> gvs[] >>
      rename1 `SOME callee_fn` >>
      Cases_on `eval_operands arg_ops st` >> gvs[] >>
      rename1 `SOME args` >>
      gvs[setup_callee_update_var] >>
      Cases_on `setup_callee callee_fn args st` >> gvs[] >>
      rename1 `SOME callee_s` >>
      Cases_on `run_blocks fuel ctx callee_fn callee_s` >> gvs[] >>
      rename1 `IntRet vals callee_s'` >>
      gvs[merge_callee_update_var] >>
      Cases_on `LENGTH inst.inst_outputs = LENGTH vals.iret_values`
      >- (`bind_outputs inst.inst_outputs vals.iret_values
             (adopt_return_fmp vals
               (update_var x w (merge_callee_state st callee_s'))) =
           OPTION_MAP (update_var x w)
             (bind_outputs inst.inst_outputs vals.iret_values
               (adopt_return_fmp vals
                 (merge_callee_state st callee_s')))`
            by (rewrite_tac[adopt_return_fmp_update_var] >>
                irule bind_outputs_update_var >> gvs[]) >>
          Cases_on `bind_outputs inst.inst_outputs vals.iret_values
                      (adopt_return_fmp vals
                        (merge_callee_state st callee_s'))` >> gvs[])
      >> gvs[bind_outputs_def])
  (* Non-INVOKE: step_inst = step_inst_base *)
  >> (drule_all step_inst_base_var_frame_full >>
      simp[step_inst_non_invoke])
QED

val _ = export_theory();
