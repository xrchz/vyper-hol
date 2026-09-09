(*
 * Stack Model
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * HOL4 formalization of Python's stack_model.py.
 * The stack is a list of operands: HD = bottom, LAST = TOS.
 * Distance from TOS: 0 = TOS, 1 = one below, etc.
 *
 * TOP-LEVEL:
 *   stack_push, stack_pop, stack_peek, stack_poke,
 *   stack_swap, stack_dup, stack_get_depth, stack_get_phi_depth
 *
 * Helper:
 *   stack_find — generic search from head of list, used by get_depth/get_phi_depth
 *)

Theory stackModel
Ancestors
  rich_list list

(* =========================================================================
   Stack Operations
   ========================================================================= *)

(* Push: append to end (TOS = last element) *)
Definition stack_push_def:
  stack_push op stk = SNOC op stk
End

(* Pop n items from TOS *)
Definition stack_pop_def:
  stack_pop n stk = TAKE (LENGTH stk - n) stk
End

(* Peek at distance from TOS (0 = TOS) *)
Definition stack_peek_def:
  stack_peek dist stk =
    EL (LENGTH stk - 1 - dist) stk
End

(* Poke: update element at distance from TOS *)
Definition stack_poke_def:
  stack_poke dist op stk =
    LUPDATE op (LENGTH stk - 1 - dist) stk
End

(* Swap TOS with element at distance dist (dist > 0) *)
Definition stack_swap_def:
  stack_swap dist stk =
    let top_idx = LENGTH stk - 1 in
    let tgt_idx = LENGTH stk - 1 - dist in
    let top_val = EL top_idx stk in
    let tgt_val = EL tgt_idx stk in
    LUPDATE top_val tgt_idx (LUPDATE tgt_val top_idx stk)
End

(* Dup: copy element at distance to TOS *)
Definition stack_dup_def:
  stack_dup dist stk =
    SNOC (stack_peek dist stk) stk
End

(* =========================================================================
   Depth Search
   ========================================================================= *)

(* Find first matching operand from TOS, return distance.
   Searches reversed list (TOS first). Returns NONE if not found. *)
Definition stack_find_def:
  stack_find p [] = NONE ∧
  stack_find p (x :: xs) =
    if p x then SOME (0 : num)
    else case stack_find p xs of
      SOME d => SOME (d + 1)
    | NONE => NONE
End

(* Get depth (distance from TOS) of an operand.
   Python: get_depth returns 0 for TOS, -1 for one below, etc.
   HOL4: returns SOME dist or NONE, where 0 = TOS, 1 = one below.
   Searches REVERSE to scan from TOS first (matches Python's
   enumerate(reversed(...)) and returns first/shallowest match). *)
Definition stack_get_depth_def:
  stack_get_depth op stk = stack_find (λx. x = op) (REVERSE stk)
End

Theorem stack_find_props[local]:
  ∀p xs d. stack_find p xs = SOME d ⇒ d < LENGTH xs ∧ p (EL d xs)
Proof
  gen_tac >> Induct >> simp[stack_find_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  Cases_on `stack_find p xs` >> simp[] >>
  strip_tac >> gvs[] >>
  `PRE (x + 1) = x` by decide_tac >> simp[EL_CONS]
QED

Theorem stack_find_NONE_EVERY[local]:
  ∀p xs. stack_find p xs = NONE ⇔ EVERY (λx. ¬p x) xs
Proof
  gen_tac >> Induct >> simp[stack_find_def] >>
  Cases_on `p h` >> simp[] >>
  Cases_on `stack_find p xs`
  >- simp[] >>
  simp[] >> drule stack_find_props >> strip_tac >>
  simp[EXISTS_MEM] >> qexists `EL x xs` >> simp[MEM_EL] >>
  qexists `x` >> simp[]
QED

Theorem stack_find_NONE[local]:
  ∀p xs. stack_find p xs = NONE ⇔
  ∀d. d < LENGTH xs ⇒ ¬p (EL d xs)
Proof
  simp[stack_find_NONE_EVERY, EVERY_EL]
QED

Theorem stack_peek_eq_EL_REVERSE[local]:
  d < LENGTH stk ⇒ stack_peek d stk = EL d (REVERSE stk)
Proof
  strip_tac >> simp[stack_peek_def, EL_REVERSE] >>
  `PRE (LENGTH stk - d) = LENGTH stk - 1 - d` by decide_tac >>
  simp[]
QED

Theorem stack_get_depth_props:
  stack_get_depth op stk = SOME d ⇒
  d < LENGTH stk ∧ stack_peek d stk = op
Proof
  strip_tac >> fs[stack_get_depth_def] >>
  drule stack_find_props >> simp[LENGTH_REVERSE] >>
  strip_tac >> drule stack_peek_eq_EL_REVERSE >> simp[]
QED

Theorem stack_get_depth_NONE:
  stack_get_depth op stk = NONE ⇔
  ∀d. d < LENGTH stk ⇒ stack_peek d stk ≠ op
Proof
  simp[stack_get_depth_def, stack_find_NONE, LENGTH_REVERSE] >>
  metis_tac[stack_peek_eq_EL_REVERSE]
QED

(* Find the shallowest matching operand whose depth is not in the protected
   interval (f,n).  Reorder uses this to avoid selecting target slots that
   have already been finalized. *)
Definition stack_get_unfixed_depth_def:
  stack_get_unfixed_depth op f n stk =
    if n ≤ f + 1 then stack_get_depth op stk
    else
      FIND (λd. ¬(f < d ∧ d < n) ∧ stack_peek d stk = op)
        (GENLIST I (LENGTH stk))
End

Theorem FIND_SOME_MEM_P[local]:
  ∀p xs x. FIND p xs = SOME x ⇒ MEM x xs ∧ p x
Proof
  gen_tac >> Induct >> simp[FIND_thm] >>
  rpt strip_tac >> Cases_on `p h` >> gvs[] >>
  Cases_on `FIND p xs` >> gvs[]
QED

Theorem FIND_NONE_EVERY[local]:
  ∀p xs. FIND p xs = NONE ⇔ ∀x. MEM x xs ⇒ ¬p x
Proof
  gen_tac >> Induct >> simp[FIND_thm] >> metis_tac[]
QED

Theorem stack_get_unfixed_depth_props:
  stack_get_unfixed_depth op f n stk = SOME d ⇒
  d < LENGTH stk ∧ stack_peek d stk = op ∧ ¬(f < d ∧ d < n)
Proof
  Cases_on `n ≤ f + 1`
  >- (simp[stack_get_unfixed_depth_def] >> strip_tac >>
      drule stack_get_depth_props >> strip_tac >>
      simp[] >> decide_tac) >>
  simp[stack_get_unfixed_depth_def] >> strip_tac >>
  drule FIND_SOME_MEM_P >> simp[MEM_GENLIST]
QED

Theorem stack_get_unfixed_depth_bound:
  stack_get_unfixed_depth op f n stk = SOME d ⇒ d < LENGTH stk
Proof
  metis_tac[stack_get_unfixed_depth_props]
QED

Theorem stack_get_unfixed_depth_peek:
  stack_get_unfixed_depth op f n stk = SOME d ⇒ stack_peek d stk = op
Proof
  metis_tac[stack_get_unfixed_depth_props]
QED

Theorem stack_get_unfixed_depth_excluded:
  stack_get_unfixed_depth op f n stk = SOME d ⇒ ¬(f < d ∧ d < n)
Proof
  metis_tac[stack_get_unfixed_depth_props]
QED

Theorem stack_get_unfixed_depth_NONE:
  stack_get_unfixed_depth op f n stk = NONE ⇔
  ∀d. d < LENGTH stk ∧ ¬(f < d ∧ d < n) ⇒ stack_peek d stk ≠ op
Proof
  Cases_on `n ≤ f + 1`
  >- (simp[stack_get_unfixed_depth_def, stack_get_depth_NONE] >>
      metis_tac[]) >>
  simp[stack_get_unfixed_depth_def, FIND_NONE_EVERY, MEM_GENLIST] >>
  metis_tac[]
QED

Theorem stack_get_unfixed_depth_empty_window:
  n ≤ f + 1 ⇒
  stack_get_unfixed_depth op f n stk = stack_get_depth op stk
Proof
  simp[stack_get_unfixed_depth_def]
QED

Theorem stack_get_unfixed_depth_zero:
  stack_get_depth op stk = SOME 0 ⇒
  stack_get_unfixed_depth op f n stk = SOME 0
Proof
  strip_tac >> Cases_on `n ≤ f + 1`
  >- simp[stack_get_unfixed_depth_def] >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `LENGTH stk` >>
  gvs[stack_get_unfixed_depth_def, FIND_thm, GENLIST_CONS]
QED

(* Get depth of first matching phi operand.
   Python: get_phi_depth iterates reversed stack.
   HOL4: returns SOME dist or NONE, 0 = TOS. *)
Definition stack_get_phi_depth_def:
  stack_get_phi_depth phis stk = stack_find (λx. MEM x phis) (REVERSE stk)
End
