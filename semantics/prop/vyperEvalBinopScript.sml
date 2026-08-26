Theory vyperEvalBinop

Ancestors
  vyperInterpreter vyperArith

Libs
  intLib wordsLib

(****************************************************************************)
(*                         Main theorems                                    *)
(****************************************************************************)

(* ========= Add / Sub / Mul ========== *)

Theorem evaluate_binop_add:
  ∀u tv x y.
    within_int_bound u (x + y) ⇒
    evaluate_binop u tv Add (IntV x) (IntV y) =
    INL (IntV (x + y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.bounded_int_op_def]
QED

Theorem evaluate_binop_sub:
  ∀u tv x y.
    within_int_bound u (x − y) ⇒
    evaluate_binop u tv Sub (IntV x) (IntV y) =
    INL (IntV (x − y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.bounded_int_op_def]
QED

Theorem evaluate_binop_mul:
  ∀u tv x y.
    within_int_bound u (x * y) ⇒
    evaluate_binop u tv Mul (IntV x) (IntV y) =
    INL (IntV (x * y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.bounded_int_op_def]
QED

(* ========= Mod / Div (Unsigned) ========== *)

Theorem evaluate_binop_mod_unsigned:
  ∀x y n tv.
    within_int_bound (Unsigned n) x ∧ within_int_bound (Unsigned n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop (Unsigned n) tv Mod (IntV x) (IntV y) =
    INL (IntV (x rem y))
Proof
  rpt strip_tac >>
  gvs[vyperValueTheory.within_int_bound_def] >>
  simp[vyperValueOperationTheory.evaluate_binop_def, vyperValueOperationTheory.bounded_int_op_def, vyperValueTheory.within_int_bound_def] >>
  `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[integerTheory.NUM_OF_INT] >>
  `Num y ≠ 0` by simp[] >>
  `Num x < dimword (:256)` by (irule lt_dimword_256 >> qexists_tac `n` >> simp[]) >>
  `Num y < dimword (:256)` by (irule lt_dimword_256 >> qexists_tac `n` >> simp[]) >>
  simp[wordsTheory.word_mod_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w] >>
  `Num x MOD Num y < Num y` by simp[] >>
  `Num x MOD Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_TRANS >> qexists_tac `Num y` >> simp[]) >>
  conj_tac >- (
    irule arithmeticTheory.LESS_TRANS >> qexists_tac `Num y` >> fs[integerTheory.NUM_OF_INT]
  ) >>
  simp[integerTheory.INT_REM] >>
  once_rewrite_tac[GSYM (EVAL ``dimword(:256)``)] >>
  irule lt_dimword_256 >> qexists_tac `n` >> simp[]
QED

Theorem evaluate_binop_div_unsigned:
  ∀x y n tv.
    within_int_bound (Unsigned n) x ∧ within_int_bound (Unsigned n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop (Unsigned n) tv Div (IntV x) (IntV y) =
    INL (IntV (x / y))
Proof
  rpt strip_tac >>
  gvs[vyperValueTheory.within_int_bound_def] >>
  simp[vyperValueOperationTheory.evaluate_binop_def, vyperValueOperationTheory.bounded_int_op_def, vyperValueTheory.within_int_bound_def] >>
  `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[integerTheory.NUM_OF_INT] >>
  `Num y ≠ 0` by simp[] >>
  `Num x < dimword (:256)` by (irule lt_dimword_256 >> qexists_tac `n` >> simp[]) >>
  `Num y < dimword (:256)` by (irule lt_dimword_256 >> qexists_tac `n` >> simp[]) >>
  `Num x DIV Num y ≤ Num x` by simp[arithmeticTheory.DIV_LESS_EQ] >>
  `Num x DIV Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
    qexists_tac `Num x` >> simp[]) >>
  simp[wordsTheory.word_div_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w, integerTheory.INT_DIV] >>
  conj_tac >- (
    irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
    qexists_tac `Num x` >> fs[integerTheory.NUM_OF_INT]
  ) >>
  once_rewrite_tac[GSYM (EVAL ``dimword(:256)``)] >>
  irule lt_dimword_256 >> qexists_tac `n` >> simp[]
QED

(* ========= Div / Mod (Signed) ========== *)

Theorem evaluate_binop_div_signed:
  ∀x y n tv.
    within_int_bound (Signed n) x ∧ within_int_bound (Signed n) y ∧
    within_int_bound (Signed n) (x quot y) ∧
    y ≠ 0 ∧ n ≤ 256 ∧
    (* MIN_INT / -1 overflows — now correctly reverts *)
    ¬(y = -1 ∧ x = -&(2 ** (n − 1))) ⇒
    evaluate_binop (Signed n) tv Div (IntV x) (IntV y) =
    INL (IntV (x quot y))
Proof
  rpt strip_tac >>
  simp[vyperValueOperationTheory.evaluate_binop_def, vyperValueOperationTheory.bounded_int_op_def] >>
  `w2i ((i2w x):bytes32) = x` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `w2i ((i2w y):bytes32) = y` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `(i2w y):bytes32 ≠ 0w` by (
    CCONTR_TAC >> fs[] >> fs[integer_wordTheory.word_0_w2i]) >>
  drule integer_wordTheory.word_quot >>
  disch_then (qspecl_then [`(i2w x):bytes32`] mp_tac) >>
  strip_tac >> gvs[] >>
  `w2i ((i2w (x quot y)):bytes32) = x quot y` by
    (irule w2i_i2w_within_signed >> metis_tac[]) >>
  simp[]
QED

Theorem evaluate_binop_mod_signed:
  ∀x y n tv.
    within_int_bound (Signed n) x ∧ within_int_bound (Signed n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop (Signed n) tv Mod (IntV x) (IntV y) =
    INL (IntV (x rem y))
Proof
  rpt strip_tac >>
  simp[vyperValueOperationTheory.evaluate_binop_def, vyperValueOperationTheory.bounded_int_op_def] >>
  `w2i ((i2w x):bytes32) = x` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `w2i ((i2w y):bytes32) = y` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `(i2w y):bytes32 ≠ 0w` by (
    CCONTR_TAC >> fs[] >> fs[integer_wordTheory.word_0_w2i]) >>
  drule integer_wordTheory.word_rem >>
  disch_then (qspecl_then [`(i2w x):bytes32`] mp_tac) >>
  strip_tac >> gvs[] >>
  `within_int_bound (Signed n) (x rem y)` by
    (irule within_int_bound_rem >> metis_tac[]) >>
  `w2i ((i2w (x rem y)):bytes32) = x rem y` by
    (irule w2i_i2w_within_signed >> metis_tac[]) >>
  simp[]
QED

(* ========= Exp ========== *)

Theorem evaluate_binop_exp:
  ∀u tv x y.
    within_int_bound u (x ** Num y) ∧ 0 ≤ y ⇒
    evaluate_binop u tv Exp (IntV x) (IntV y) =
    INL (IntV (x ** Num y))
Proof
  rpt strip_tac >>
  `¬(y < 0)` by intLib.ARITH_TAC >>
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.bounded_int_op_def]
QED

(* ========= Bitwise (IntV) ========== *)

Theorem evaluate_binop_and_int:
  ∀u tv x y.
    within_int_bound u (int_and x y) ⇒
    evaluate_binop u tv And (IntV x) (IntV y) =
    INL (IntV (int_and x y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.bounded_int_op_def]
QED

Theorem evaluate_binop_or_int:
  ∀u tv x y.
    within_int_bound u (int_or x y) ⇒
    evaluate_binop u tv Or (IntV x) (IntV y) =
    INL (IntV (int_or x y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.bounded_int_op_def]
QED

Theorem evaluate_binop_xor_int:
  ∀u tv x y.
    within_int_bound u (int_xor x y) ⇒
    evaluate_binop u tv XOr (IntV x) (IntV y) =
    INL (IntV (int_xor x y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.bounded_int_op_def]
QED

(* ========= Bitwise (BoolV) ========== *)

Theorem evaluate_binop_and_bool:
  ∀u tv a b.
    evaluate_binop u tv And (BoolV a) (BoolV b) = INL (BoolV (a ∧ b))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_or_bool:
  ∀u tv a b.
    evaluate_binop u tv Or (BoolV a) (BoolV b) = INL (BoolV (a ∨ b))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_xor_bool:
  ∀u tv a b.
    evaluate_binop u tv XOr (BoolV a) (BoolV b) = INL (BoolV (a ≠ b))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

(* ========= Wrapped arithmetic (UnsafeAdd, UnsafeSub, UnsafeMul, UnsafeDiv) ========== *)

Theorem evaluate_binop_uadd:
  ∀u tv x y.
    evaluate_binop u tv UnsafeAdd (IntV x) (IntV y) =
    INL (IntV (if is_Unsigned u then (x + y) % &(2 ** int_bound_bits u)
                 else signed_int_mod (int_bound_bits u) (x + y)))
Proof
  Cases >> simp[vyperValueOperationTheory.evaluate_binop_def,
                vyperValueOperationTheory.wrapped_int_op_def]
QED

Theorem evaluate_binop_usub:
  ∀u tv x y.
    evaluate_binop u tv UnsafeSub (IntV x) (IntV y) =
    INL (IntV (if is_Unsigned u then (x − y) % &(2 ** int_bound_bits u)
                 else signed_int_mod (int_bound_bits u) (x − y)))
Proof
  Cases >> simp[vyperValueOperationTheory.evaluate_binop_def,
                vyperValueOperationTheory.wrapped_int_op_def]
QED

Theorem evaluate_binop_umul:
  ∀u tv x y.
    evaluate_binop u tv UnsafeMul (IntV x) (IntV y) =
    INL (IntV (if is_Unsigned u then (x * y) % &(2 ** int_bound_bits u)
                 else signed_int_mod (int_bound_bits u) (x * y)))
Proof
  Cases >> simp[vyperValueOperationTheory.evaluate_binop_def,
                vyperValueOperationTheory.wrapped_int_op_def]
QED

Theorem evaluate_binop_udiv:
  ∀u tv x y.
    y ≠ 0 ⇒
    evaluate_binop u tv UnsafeDiv (IntV x) (IntV y) =
    INL (IntV (if is_Unsigned u
               then &(w2n (word_div ((i2w x):bytes32) ((i2w y):bytes32))) % &(2 ** int_bound_bits u)
               else signed_int_mod (int_bound_bits u)
                     (w2i (word_quot ((i2w x):bytes32) ((i2w y):bytes32)))))
Proof
  Cases >> simp[vyperValueOperationTheory.evaluate_binop_def,
                vyperValueOperationTheory.wrapped_int_op_def] >>
  rpt strip_tac >>
  `(i2w y):bytes32 ≠ 0w` by (
    CCONTR_TAC >> fs[] >> fs[integer_wordTheory.word_0_w2i]) >>
  simp[]
QED

(* ========= Shifts ========== *)

Theorem evaluate_binop_shl:
  ∀u tv x y.
    0 ≤ y ⇒
    evaluate_binop u tv ShL (IntV x) (IntV y) =
    INL (IntV (if is_Unsigned u then
               int_mod (int_shift_left (Num y) x) &(2 ** int_bound_bits u) else
               signed_int_mod (int_bound_bits u) (int_shift_left (Num y) x)))
Proof
  rpt strip_tac >>
  `¬(y < 0)` by intLib.ARITH_TAC >>
  simp[vyperValueOperationTheory.evaluate_binop_def] >>
  rw[]
QED

Theorem evaluate_binop_shr:
  ∀u tv x y.
    0 ≤ y ⇒
    evaluate_binop u tv ShR (IntV x) (IntV y) =
    INL (IntV (int_shift_right (Num y) x))
Proof
  rpt strip_tac >>
  `¬(y < 0)` by intLib.ARITH_TAC >>
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

(* ========= ExpMod ========== *)

Theorem evaluate_binop_expmod:
  ∀tv x y.
    evaluate_binop (Unsigned 256) tv ExpMod (IntV x) (IntV y) =
    INL (IntV (&(w2n (word_exp ((i2w x):bytes32) (i2w y)))))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

(* ========= Min / Max ========== *)

Theorem evaluate_binop_min:
  ∀u tv x y.
    evaluate_binop u tv Min (IntV x) (IntV y) =
    INL (IntV (if x < y then x else y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_max:
  ∀u tv x y.
    evaluate_binop u tv Max (IntV x) (IntV y) =
    INL (IntV (if x < y then y else x))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

(* ========= Comparisons ========== *)

Theorem evaluate_binop_eq_int:
  ∀u tv x y.
    evaluate_binop u tv Eq (IntV x) (IntV y) = INL (BoolV (x = y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_lt:
  ∀u tv x y.
    evaluate_binop u tv Lt (IntV x) (IntV y) = INL (BoolV (x < y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_lte:
  ∀u tv x y.
    evaluate_binop u tv LtE (IntV x) (IntV y) = INL (BoolV (x ≤ y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_gt:
  ∀u tv x y.
    evaluate_binop u tv Gt (IntV x) (IntV y) = INL (BoolV (x > y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_gte:
  ∀u tv x y.
    evaluate_binop u tv GtE (IntV x) (IntV y) = INL (BoolV (x ≥ y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_noteq_int:
  ∀u tv x y.
    evaluate_binop u tv NotEq (IntV x) (IntV y) = INL (BoolV (x ≠ y))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.binop_negate_def]
QED

Theorem evaluate_binop_eq_bool:
  ∀u tv a b.
    evaluate_binop u tv Eq (BoolV a) (BoolV b) = INL (BoolV (a = b))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_noteq_bool:
  ∀u tv a b.
    evaluate_binop u tv NotEq (BoolV a) (BoolV b) = INL (BoolV (a ≠ b))
Proof
  simp[vyperValueOperationTheory.evaluate_binop_def,
       vyperValueOperationTheory.binop_negate_def]
QED

(* ========= Division/Modulo: success implies nonzero divisor ========== *)

Theorem evaluate_binop_div_mod_success_nonzero:
  ∀u tv bop v1 v2 result.
    (bop = Div ∨ bop = UnsafeDiv ∨ bop = Mod) ∧
    evaluate_binop u tv bop v1 v2 = INL result ⇒
    (∃i1 i2. v1 = IntV i1 ∧ v2 = IntV i2 ∧ i2 ≠ 0) ∨
    (∃i1 i2. v1 = DecimalV i1 ∧ v2 = DecimalV i2 ∧ i2 ≠ 0)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bop = Div`
  >- (gvs[] >>
      gvs[vyperValueOperationTheory.evaluate_binop_def, AllCaseEqs(),
          vyperValueOperationTheory.bounded_int_op_def,
          vyperValueOperationTheory.bounded_decimal_op_def,
          vyperValueOperationTheory.wrapped_int_op_def] >>
      Cases_on `v1` >> gvs[AllCaseEqs()] >>
      Cases_on `v2` >> gvs[AllCaseEqs()]) >>
  Cases_on `bop = UnsafeDiv`
  >- (gvs[] >>
      gvs[vyperValueOperationTheory.evaluate_binop_def, AllCaseEqs(),
          vyperValueOperationTheory.bounded_int_op_def,
          vyperValueOperationTheory.bounded_decimal_op_def,
          vyperValueOperationTheory.wrapped_int_op_def] >>
      Cases_on `v1` >> gvs[AllCaseEqs()] >>
      Cases_on `v2` >> gvs[AllCaseEqs()]) >>
  gvs[] >>
  gvs[vyperValueOperationTheory.evaluate_binop_def, AllCaseEqs(),
      vyperValueOperationTheory.bounded_int_op_def,
      vyperValueOperationTheory.bounded_decimal_op_def,
      vyperValueOperationTheory.wrapped_int_op_def] >>
  Cases_on `v1` >> gvs[AllCaseEqs()] >>
  Cases_on `v2` >> gvs[AllCaseEqs()]
QED
