(*
 * Prefix Operation Simulation
 *
 * Stack plan ops other than SOEmit ("prefix ops") produce asm
 * instructions that preserve accounts/transient/returndata/logs.
 *
 * Key exports:
 *   exec_prefix_step_preserves — single asm_step preserves 4 fields
 *   asm_steps_side_preserves   — multi-step composition
 *   venom_asm_rel_implies_terminal, venom_asm_terminal_rel_intro
 *   halt_state_fields[simp]
 *)


Theory prefixSim
Ancestors
  asmSem planExec codegenRel asmIR stackOpAsmSim stackOpSim blockSimHelpers list rich_list arithmetic
Libs
  BasicProvers

(* ===== Prefix op definition ===== *)

Definition is_prefix_op_def:
  is_prefix_op (SOPush op) = T /\
  is_prefix_op (SOPop n) = T /\
  is_prefix_op (SOSwap n) = T /\
  is_prefix_op (SODup n) = T /\
  is_prefix_op (SOPoke n op) = T /\
  is_prefix_op (SOSpill off) = T /\
  is_prefix_op (SORestore off) = T /\
  is_prefix_op (SOEmit name) = F /\
  is_prefix_op SOInitialFmp = T /\
  is_prefix_op (SOLabel lbl) = T /\
  is_prefix_op (SOPushLabel lbl) = T /\
  is_prefix_op (SOPushOfst lbl off) = T
End

(* ===== Shared tactic infrastructure ===== *)

val dispatch_ss = [asm_step_def, asm_step_op_def,
  asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
  asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
  asm_step_copy_def, asm_step_context_def,
  dup_table_def, swap_table_def, log_table_def];

(* ===== Main prefix preservation theorem ===== *)

val side_fields = ``
  st'.as_accounts = st.as_accounts /\
  st'.as_transient = st.as_transient /\
  st'.as_returndata = st.as_returndata /\
  st'.as_logs = st.as_logs``;

val all_handler_defs = dispatch_ss @
  [asm_pop_def, asm_mstore_def, asm_mload_def,
   asm_dup_def, asm_swap_def, LET_THM, asm_next_def];

val prefix_swap_tac =
  rw(dispatch_ss @ [asm_swap_def, LET_THM, asm_next_def]) >>
  gvs[];

val prefix_dup_tac =
  rw(dispatch_ss @ [asm_dup_def, asm_next_def]) >>
  gvs[];

Theorem prefix_push_preserves[local]:
  !bs lo o2pc st st'.
    asm_step lo o2pc (AsmPush bs) st = AsmOK st' ==> ^side_fields
Proof
  simp[asm_step_def, asm_next_def]
QED

Theorem prefix_label_preserves[local]:
  !n lo o2pc st st'.
    asm_step lo o2pc (AsmLabel n) st = AsmOK st' ==> ^side_fields
Proof
  simp[asm_step_def, asm_next_def]
QED

Theorem prefix_pushlabel_preserves[local]:
  !l lo o2pc st st'.
    asm_step lo o2pc (AsmPushLabel l) st = AsmOK st' ==> ^side_fields
Proof
  rpt gen_tac \\ simp[asm_step_def, asm_next_def] \\
  every_case_tac \\ strip_tac \\ gvs[]
QED

Theorem prefix_pushofst_preserves[local]:
  !l n lo o2pc st st'.
    asm_step lo o2pc (AsmPushOfst l n) st = AsmOK st' ==> ^side_fields
Proof
  rpt gen_tac \\ simp[asm_step_def, asm_next_def] \\
  every_case_tac \\ strip_tac \\ gvs[]
QED

Theorem prefix_pop_preserves[local]:
  !lo o2pc st st'.
    asm_step lo o2pc (AsmOp "POP") st = AsmOK st' ==> ^side_fields
Proof
  rpt strip_tac \\
  fs(all_handler_defs) \\
  every_case_tac \\ gvs[]
QED

Theorem prefix_mstore_preserves[local]:
  !lo o2pc st st'.
    asm_step lo o2pc (AsmOp "MSTORE") st = AsmOK st' ==> ^side_fields
Proof
  rpt strip_tac \\
  qpat_x_assum `asm_step _ _ _ _ = AsmOK _` mp_tac \\
  PURE_ONCE_REWRITE_TAC[asm_step_def] \\
  simp_tac std_ss [] \\
  PURE_ONCE_REWRITE_TAC[asm_step_op_def] \\
  simp[asm_step_arith_def] \\
  simp[asm_step_compare_def] \\
  simp[asm_step_bitwise_def] \\
  simp[asm_step_memory_def] \\
  simp[asm_mstore_def, LET_THM, asm_next_def] \\
  every_case_tac \\ rpt strip_tac \\ gvs[]
QED

Theorem prefix_mload_preserves[local]:
  !lo o2pc st st'.
    asm_step lo o2pc (AsmOp "MLOAD") st = AsmOK st' ==> ^side_fields
Proof
  rpt strip_tac \\
  fs(all_handler_defs) \\
  every_case_tac \\ gvs[]
QED

Theorem prefix_swap_preserves[local]:
  !n lo o2pc st st'.
    asm_step lo o2pc (AsmOp (swap_name n)) st = AsmOK st' ==> ^side_fields
Proof
  rpt gen_tac \\
  PURE_ONCE_REWRITE_TAC[swap_name_def] \\
  rpt IF_CASES_TAC
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
  >- prefix_swap_tac
QED

Theorem prefix_dup_preserves[local]:
  !n lo o2pc st st'.
    asm_step lo o2pc (AsmOp (dup_name n)) st = AsmOK st' ==> ^side_fields
Proof
  rpt gen_tac \\
  PURE_ONCE_REWRITE_TAC[dup_name_def] \\
  rpt IF_CASES_TAC
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
  >- prefix_dup_tac
QED

Theorem exec_prefix_step_preserves:
  !initial_fmp op inst lo o2pc (st:asm_state) st'.
    is_prefix_op op /\
    MEM inst (exec_stack_op initial_fmp op) /\
    asm_step lo o2pc inst st = AsmOK st' ==> ^side_fields
Proof
  Cases_on `op`
  \\ simp[is_prefix_op_def, exec_stack_op_def, MEM_REPLICATE]
  \\ rpt gen_tac \\ strip_tac
  (* SOPush: sub-case on operand type *)
  >- (Cases_on `o'` \\ gvs[exec_stack_op_def] \\
      metis_tac[prefix_push_preserves, prefix_pushlabel_preserves])
  (* SOPop *)        >- metis_tac[prefix_pop_preserves]
  (* SOSwap *)       >- metis_tac[prefix_swap_preserves]
  (* SODup *)        >- metis_tac[prefix_dup_preserves]
  (* SOSpill-Push *) >- (gvs[] \\ metis_tac[prefix_push_preserves])
  (* SOSpill-MSt *)  >- (gvs[] \\ metis_tac[prefix_mstore_preserves])
  (* SORestore-Push*)>- (gvs[] \\ metis_tac[prefix_push_preserves])
  (* SORestore-ML *) >- (gvs[] \\ metis_tac[prefix_mload_preserves])
  (* SOInitialFmp *)  >- (gvs[] \\ metis_tac[prefix_push_preserves])
  (* SOLabel *)      >- metis_tac[prefix_label_preserves]
  (* SOPushLabel *)  >- metis_tac[prefix_pushlabel_preserves]
  (* SOPushOfst *)   >- metis_tac[prefix_pushofst_preserves]
QED

(* ===== Multi-step field preservation ===== *)

Theorem asm_steps_first_side_preserves[local]:
  !n lo o2pc prog (st:asm_state) s1.
    (!i si si'.
       i < SUC n /\
       asm_steps lo o2pc prog i st = AsmOK si /\
       asm_step lo o2pc (EL si.as_pc prog) si = AsmOK si' ==>
       si'.as_accounts = si.as_accounts /\
       si'.as_transient = si.as_transient /\
       si'.as_returndata = si.as_returndata /\
       si'.as_logs = si.as_logs) /\
    asm_step lo o2pc (EL st.as_pc prog) st = AsmOK s1 ==>
    s1.as_accounts = st.as_accounts /\
    s1.as_transient = st.as_transient /\
    s1.as_returndata = st.as_returndata /\
    s1.as_logs = st.as_logs
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`0`, `st`, `s1`] mp_tac) >>
  simp[asm_steps_zero]
QED

Theorem asm_steps_side_preserves:
  !n lo o2pc prog (st:asm_state) st'.
    asm_steps lo o2pc prog n st = AsmOK st' /\
    (!i si si'.
       i < n /\
       asm_steps lo o2pc prog i st = AsmOK si /\
       asm_step lo o2pc (EL si.as_pc prog) si = AsmOK si' ==>
       si'.as_accounts = si.as_accounts /\
       si'.as_transient = si.as_transient /\
       si'.as_returndata = si.as_returndata /\
       si'.as_logs = si.as_logs) ==>
    st'.as_accounts = st.as_accounts /\
    st'.as_transient = st.as_transient /\
    st'.as_returndata = st.as_returndata /\
    st'.as_logs = st.as_logs
Proof
  Induct_on `n` >- simp[asm_steps_def]
  \\ PURE_ONCE_REWRITE_TAC[asm_steps_def]
  \\ rpt gen_tac \\ strip_tac
  \\ reverse (Cases_on `st.as_pc < LENGTH prog`) >- fs[]
  \\ reverse (Cases_on `asm_step lo o2pc (EL st.as_pc prog) st`) >- fs[]
  >- fs[]
  >- fs[]
  >- fs[]
  \\ rename1 `AsmOK s1`
  \\ `s1.as_accounts = st.as_accounts /\
      s1.as_transient = st.as_transient /\
      s1.as_returndata = st.as_returndata /\
      s1.as_logs = st.as_logs`
       by (mp_tac (Q.SPECL [`n`, `lo`, `o2pc`, `prog`, `st`, `s1`]
             asm_steps_first_side_preserves) \\
           impl_tac >- (
             conj_tac >-
               qpat_x_assum `!i si si'. i < SUC n /\ _ ==> _` ACCEPT_TAC \\
             first_assum ACCEPT_TAC) \\
           strip_tac \\ ASM_REWRITE_TAC[])
  \\ first_x_assum (qspecl_then [`lo`, `o2pc`, `prog`, `s1`, `st'`] mp_tac)
  \\ impl_tac
  >- (conj_tac >- gvs[]
      \\ rpt strip_tac
      \\ qpat_assum `!i si si'. _` (qspec_then `SUC i` mp_tac)
      \\ simp[asm_steps_def])
  \\ simp[]
QED

(* ===== venom_asm_rel / terminal_rel ===== *)

Theorem venom_asm_rel_implies_terminal:
  !lo ps vs (as1:asm_state).
    venom_asm_rel lo ps vs as1 ==>
    venom_asm_terminal_rel vs as1
Proof
  simp[venom_asm_rel_def, venom_asm_terminal_rel_def]
QED

Theorem venom_asm_terminal_rel_intro:
  !vs (as1:asm_state).
    as1.as_accounts = vs.vs_accounts /\
    as1.as_transient = vs.vs_transient /\
    as1.as_returndata = vs.vs_returndata /\
    as1.as_logs = vs.vs_logs ==>
    venom_asm_terminal_rel vs as1
Proof
  simp[venom_asm_terminal_rel_def]
QED

Theorem halt_state_fields[simp]:
  (halt_state vs).vs_accounts = vs.vs_accounts /\
  (halt_state vs).vs_transient = vs.vs_transient /\
  (halt_state vs).vs_returndata = vs.vs_returndata /\
  (halt_state vs).vs_logs = vs.vs_logs
Proof
  EVAL_TAC
QED
