(*
 * Equivalence Definitions
 *
 * State-level and result-level equivalence relations.
 * Properties/theorems are in props/stateEquivPropsScript.sml.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * State Equivalence Hierarchy (weakest to strongest):
 *
 *   1. observable_equiv         : Only externally visible effects
 *   2. execution_equiv vars     : All state except control flow, modulo vars
 *   3. state_equiv vars         : Full state comparison, modulo vars
 *
 * Satisfies: state_equiv ⊆ execution_equiv ⊆ observable_equiv
 *
 * For full equivalence (no variable exceptions), use state_equiv {}.
 * For passes that introduce fresh variables (PHI insertion), use
 * state_equiv fresh_vars / execution_equiv fresh_vars to exclude them.
 *
 * Result Equivalence:
 *
 *   revert_equiv               : Only returndata (what survives EVM abort rollback)
 *   lift_result R_ok R_term R_abort : Generic combinator — lift three state
 *                                 relations through exec_result (R_ok for OK,
 *                                 R_term for Halt/IntRet, R_abort for Abort,
 *                                 T for Error)
 *   result_equiv vars           : Canonical instantiation —
 *                                 lift_result (state_equiv vars)
 *                                   (execution_equiv vars) revert_equiv
 *
 * TOP-LEVEL DEFINITIONS:
 *   - observable_equiv : Only externally visible effects
 *   - execution_equiv  : State equiv ignoring control flow fields
 *   - state_equiv      : Full state equivalence with variable exceptions
 *   - revert_equiv     : Only returndata (abort rollback)
 *   - lift_result      : Generic triple-relation lift through exec_result
 *   - result_equiv     : Canonical result equivalence (lift_result alias)
 *)

Theory stateEquiv
Ancestors
  finite_map pred_set
  venomState venomExecSemantics

(* ==========================================================================
   Level 1: Observable Equivalence (Weakest)
   ========================================================================== *)

(*
 * PURPOSE: Capture only what the external world can observe after execution.
 * This is the weakest equivalence - everything else is internal detail.
 *
 * FIELDS COMPARED:
 *   - vs_accounts  : Account states (including persistent storage)
 *   - vs_returndata: Return value or revert reason
 *   - vs_halted    : Whether execution halted
 *   - vs_transient : Transient storage (persists across successful subcalls,
 *                    rolled back on revert, cleared at tx boundary)
 *   - vs_immutables: Immutable storage (written by ISTORE in constructor,
 *                    baked into deployed bytecode, read-only at runtime)
 *
 * USE FOR: Proving that two executions have the same external effect,
 * regardless of how they got there.
 * NOTE: Revert/halt distinction lives in abort_type, not the state.
 *)
Definition observable_equiv_def:
  observable_equiv s1 s2 <=>
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_immutables = s2.vs_immutables
End

(* ==========================================================================
   Level 2: Execution Equivalence (Intermediate)
   ========================================================================== *)

(*
 * PURPOSE: State equivalence ignoring control flow fields. Appropriate
 * for terminal states (Halt/Revert) where control flow is irrelevant.
 *
 * FIELDS COMPARED: All except control flow (vs_current_bb, vs_inst_idx, vs_prev_bb)
 *
 * USE FOR: Comparing terminal states, proving control-flow optimizations correct
 *)
Definition execution_equiv_def:
  execution_equiv vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    (* OMIT: vs_current_bb, vs_inst_idx, vs_prev_bb *)
    s1.vs_halted = s2.vs_halted /\
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
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next
End

(* ==========================================================================
   Level 3: Full State Equivalence (Strongest)
   ========================================================================== *)

(*
 * PURPOSE: Full state equivalence ignoring only the specified variables.
 * This is the strongest equivalence, requiring all fields to match.
 *
 * For full equivalence with no exceptions, use state_equiv {}.
 *
 * USE FOR: Step-by-step simulation, same-path optimizations, PHI-related proofs
 *)
Definition state_equiv_def:
  state_equiv vars s1 s2 <=>
    execution_equiv vars s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb
End

(* ==========================================================================
   Result Equivalence
   ========================================================================== *)

(* What survives EVM rollback on abort — only returndata.
   REVERT: returndata preserved. ExHalt: returndata cleared to [].
   All other state (memory, storage, logs, vars) is rolled back. *)
Definition revert_equiv_def:
  revert_equiv s1 s2 <=> s1.vs_returndata = s2.vs_returndata
End

(* Generic combinator: lift three state relations through exec_result.
   R_ok for OK (continuation — needs control flow for next step).
   R_term for Halt/IntRet (terminal — state commits, full equiv needed).
   R_abort for Abort (rolled back — only returndata observable).
   Error results are always equivalent (messages may differ). *)
(* EVM semantics: on Abort/Halt, all state changes are rolled back.
   Only the result constructor matters, not the internal state.
   R_term is retained for IntRet (caller uses returned value + state). *)
Definition lift_result_def:
  lift_result R_ok R_term R_abort (OK s1) (OK s2) = R_ok s1 s2 /\
  lift_result R_ok R_term R_abort (Halt s1) (Halt s2) = R_term s1 s2 /\
  lift_result R_ok R_term R_abort (Abort a1 s1) (Abort a2 s2) =
    ((a1 = a2) /\ R_abort s1 s2) /\
  lift_result R_ok R_term R_abort (IntRet v1 s1) (IntRet v2 s2) =
    (R_term s1 s2 /\ (v1 = v2)) /\
  lift_result R_ok R_term R_abort (Error e1) (Error e2) = T /\
  lift_result R_ok R_term R_abort _ _ = F
End

(* Canonical instantiation: state_equiv for OK, execution_equiv for terminal.
   Abort also uses execution_equiv (stronger than needed, but proof-compatible).
   DFT uses lift_result with revert_equiv directly for Abort.
   Equivalence with lift_result proven in stateEquivProps. *)
Definition result_equiv_def:
  result_equiv vars (OK s1) (OK s2) = state_equiv vars s1 s2 /\
  result_equiv vars (Halt s1) (Halt s2) = execution_equiv vars s1 s2 /\
  result_equiv vars (Abort a1 s1) (Abort a2 s2) =
    ((a1 = a2) /\ execution_equiv vars s1 s2) /\
  result_equiv vars (IntRet v1 s1) (IntRet v2 s2) =
    (execution_equiv vars s1 s2 /\ (v1 = v2)) /\
  result_equiv vars (Error e1) (Error e2) = T /\
  result_equiv vars _ _ = F
End
