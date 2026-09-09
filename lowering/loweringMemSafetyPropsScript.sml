(*
 * Lowering Memory Safety — Properties
 *
 * Top-level theorems only. Internal proof helpers remain in
 * loweringMemSafetyProofsTheory.
 *)

Theory loweringMemSafetyProps
Ancestors
  loweringMemSafetyProofs loweringMemSafetyDefs allocaRemapDefs

(* ===== Type-safety interface ===== *)

Theorem value_type_fits_alloca:
  ∀cenv tenv ty tv v.
    evaluate_type tenv ty = SOME tv ∧
    value_has_type tv v ∧ well_formed_type_value tv
  ⇒ value_within_alloca_size cenv ty v
Proof
  ACCEPT_TAC loweringMemSafetyProofsTheory.value_type_fits_alloca
QED

(* ===== Alloca uniqueness ===== *)

Theorem alloca_regions_same:
  ∀s a1 a2 b1 sz1 b2 sz2 x.
    allocas_non_overlapping s ∧
    FLOOKUP s.vs_allocas a1 = SOME (b1,sz1) ∧
    FLOOKUP s.vs_allocas a2 = SOME (b2,sz2) ∧
    b1 ≤ x ∧ x < b1 + sz1 ∧ b2 ≤ x ∧ x < b2 + sz2
    ⇒ a1 = a2 ∧ b1 = b2 ∧ sz1 = sz2
Proof
  ACCEPT_TAC loweringMemSafetyProofsTheory.alloca_regions_same
QED

(* ===== Execution safety preservation ===== *)

Theorem reachable_preserves_safety:
  ∀fn roots s s'.
    step_preserves_safety fn roots ∧
    alloca_safe_access fn roots s ∧
    ptrs_in_alloca_bounds fn roots s ∧
    reachable_by_execution fn s s'
    ⇒ alloca_safe_access fn roots s' ∧ ptrs_in_alloca_bounds fn roots s'
Proof
  ACCEPT_TAC loweringMemSafetyProofsTheory.reachable_preserves_safety
QED

(* ===== TOP-LEVEL THEOREM ===== *)

Theorem lowering_memory_safe:
  ∀selectors ext_fns int_fns fb_fn (dispatch:dispatch_strategy)
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    fn cenv s0 s.
    MEM fn (FST (run_lowering_pair_compat selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label)).ctx_functions ∧
    cenv_matches_fn cenv fn ∧
    alloca_inv s0 ∧
    state_matches_fn fn s0 ∧
    well_typed_lowering cenv ∧
    (∀aid off asz.
       FLOOKUP s0.vs_allocas aid = SOME (off,asz) ⇒
       off + asz ≤ LENGTH s0.vs_memory ∧ off + asz < dimword (:256)) ∧
    reachable_by_execution fn s0 s
    ⇒ ptrs_in_alloca_bounds fn (alloca_roots fn) s ∧
      alloca_safe_access fn (alloca_roots fn) s
Proof
  ACCEPT_TAC loweringMemSafetyProofsTheory.lowering_memory_safe
QED
