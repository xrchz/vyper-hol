(*
 * Pass Simulation Framework — Definitions
 *
 * Generic block→function lifting for pass correctness proofs,
 * parameterized by dual state relations (R_ok, R_term).
 *
 * R_ok governs OK results (execution continues — needs control flow match).
 * R_term governs Halt/IntRet results (terminal, state commits).
 * R_abort governs Abort results (rolled back — only returndata observable).
 *
 * Instantiations:
 *   result_equiv vars = lift_result (state_equiv vars) (execution_equiv vars) revert_equiv
 *   uniform R         = lift_result R R R
 *
 * TOP-LEVEL:
 *   block_map_transform      — MAP f over block instructions
 *   function_map_transform   — MAP bt over function blocks
 *   inst_simulates           — per-instruction simulation predicate
 *   block_simulates          — whole-block simulation predicate
 *   terminates               — execution terminates (not Error)
 *   pass_correct             — combined termination + result equivalence (R_ok, R_term)
 *)

Theory passSimulationDefs
Ancestors
  stateEquiv venomExecSemantics venomInst

(* ===== Transform definitions ===== *)

(* Level 1: 1:1 instruction mapping *)
Definition block_map_transform_def:
  block_map_transform f bb =
    bb with bb_instructions := MAP f bb.bb_instructions
End

(* Function transform: apply block transform to all blocks *)
Definition function_map_transform_def:
  function_map_transform bt fn =
    fn with fn_blocks := MAP bt fn.fn_blocks
End

Theorem function_map_transform_identity_metadata_eq:
  !bt fn. fn_identity_metadata_eq (function_map_transform bt fn) fn
Proof
  simp[function_map_transform_def, fn_identity_metadata_eq_def]
QED

Theorem function_map_transform_static_input_eq:
  !bt fn. fn_static_input_eq (function_map_transform bt fn) fn
Proof
  simp[function_map_transform_def, fn_static_input_eq_def]
QED

Theorem function_map_transform_static_layout_eq:
  !bt fn. fn_static_layout_eq (function_map_transform bt fn) fn
Proof
  simp[function_map_transform_def, fn_static_layout_eq_def]
QED

Theorem function_map_transform_fmp_convention_eq:
  !bt fn. fn_fmp_convention_eq (function_map_transform bt fn) fn
Proof
  simp[function_map_transform_def, fn_fmp_convention_eq_def]
QED

(* ===== Simulation predicates ===== *)

(* Level 1: per-instruction simulation.
   f preserves lift_result for every instruction and state,
   and preserves the is_terminator property.
   Uses step_inst (not step_inst_base) so INVOKE-modifying transforms
   can also be expressed. For non-INVOKE passes, the INVOKE case is
   trivial when f preserves INVOKE instructions. *)
Definition inst_simulates_def:
  inst_simulates R_ok R_term f <=>
    (!fuel ctx inst s.
       lift_result R_ok R_term R_term
         (step_inst fuel ctx inst s) (step_inst fuel ctx (f inst) s)) /\
    (!inst. is_terminator inst.inst_opcode =
            is_terminator (f inst).inst_opcode)
End

(* Level 2: whole-block simulation.
   Running the transformed block gives a related result. *)
Definition block_simulates_def:
  block_simulates R_ok R_term bt <=>
    !fuel ctx bb s.
      lift_result R_ok R_term R_term (exec_block fuel ctx bb s)
                               (exec_block fuel ctx (bt bb) s)
End

(* ===== Pass correctness predicates ===== *)

(* Execution terminates (not Error). *)
Definition terminates_def:
  terminates r <=> case r of Error _ => F | _ => T
End

(* Two executions (parameterized by fuel) are pass-correct:
   1. Termination equivalence: original terminates iff transformed terminates
   2. Result equivalence: when both terminate, results are related

   Parameterized by R_ok (OK/continuation relation) and R_term
   (Halt/Revert/terminal relation).  Passes that only introduce
   fresh variables instantiate with state_equiv/execution_equiv.
   Passes with custom relations (e.g. lower_dload) use their own.

   Usage: pass_correct (state_equiv vars) (execution_equiv vars)
            (\fuel. run_blocks fuel ctx fn s)
            (\fuel. run_blocks fuel ctx fn' s) *)
(* Sequential composition of state relations.
   rel_seq R1 R2 s1 s3 holds when there exists an intermediate s2
   with R1 s1 s2 and R2 s2 s3.  Identity element: (=). *)
Definition rel_seq_def:
  rel_seq (R1 : 'a -> 'a -> bool) R2 s1 s3 <=> ?s2. R1 s1 s2 /\ R2 s2 s3
End

Definition pass_correct_def:
  pass_correct R_ok R_term R_abort exec1 exec2 <=>
    ((?fuel. terminates (exec1 fuel)) <=> (?fuel'. terminates (exec2 fuel'))) /\
    (!fuel fuel'.
       terminates (exec1 fuel) /\ terminates (exec2 fuel') ==>
       lift_result R_ok R_term R_abort (exec1 fuel) (exec2 fuel'))
End
