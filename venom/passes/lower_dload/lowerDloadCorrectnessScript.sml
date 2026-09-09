(*
 * Lower DLOAD Pass -- Legacy Semantic-Model Correctness Statement
 *
 * This theory concerns the arithmetic-ID lower_dload_function model only.
 * It does not certify the configured supply-aware transform or O1 composition.
 * Within that legacy model, expanding dload/dloadbytes to
 * alloca+offset+codecopy+mload preserves non-memory state given a valid layout.
 *
 * For OK (continuation) states: ld_ok holds (memory prefix-compatible).
 * For terminal (Halt/Abort) states: ld_equiv holds (no memory guarantee).
 *)

Theory lowerDloadCorrectness
Ancestors
  lowerDloadSim venomWf

(* Legacy/model-only theorem: its statement and proof intentionally remain about
   lower_dload_function and do not apply to lower_dload_configured. *)
Theorem lower_dload_function_correct:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ code_layout_valid s /\
    ld_no_mem_read fn /\ ld_dload_safe fn /\
    ld_no_original_alloca fn /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       x NOTIN ld_fresh_vars_fn fn) /\
    s.vs_inst_idx = 0 ==>
    lift_result
      (ld_ok (ld_exempt_vars_fn fn))
      (ld_equiv (ld_exempt_vars_fn fn))
      (ld_equiv (ld_exempt_vars_fn fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (lower_dload_function fn) s)
Proof
  ACCEPT_TAC lowerDloadSimTheory.lower_dload_function_correct_proof
QED

(* ===== Obligations ===== *)

(* Cheated: SSA preservation requires showing lower_dload_inst
   does not introduce duplicate variable definitions. Blocked on
   ssa_form infrastructure for 1:N instruction expansion. *)
Theorem lower_dload_preserves_ssa_form:
  !fn. ssa_form fn ==> ssa_form (lower_dload_function fn)
Proof
  cheat
QED

(* Cheated: wf preservation requires showing expanded blocks
   still have exactly one terminator at the end. Blocked on
   bb_well_formed lemmas for FLAT o MAP expansion. *)
Theorem lower_dload_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (lower_dload_function fn)
Proof
  cheat
QED
