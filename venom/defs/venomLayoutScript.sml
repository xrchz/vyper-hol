(*
 * Venom low-level layout arithmetic.
 *)

Theory venomLayout
Ancestors
  words arithmetic

Definition ceil32_def:
  ceil32 n = if n MOD 32 = 0 then n else n + (32 - n MOD 32)
End

Theorem ceil32_ge:
  n <= ceil32 n
Proof
  rw[ceil32_def]
QED

Theorem ceil32_aligned:
  ceil32 n MOD 32 = 0
Proof
  rw[ceil32_def] >>
  `n MOD 32 < 32` by simp[] >>
  `n = n MOD 32 + n DIV 32 * 32` by
    (qspec_then `32` mp_tac DIVISION >> simp[MULT_COMM]) >>
  `n + (32 - n MOD 32) = (n DIV 32 + 1) * 32` by
    decide_tac >>
  simp[]
QED

Theorem dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem ceil32_lt_dimword:
  n <= dimword (:256) - 32 ==> ceil32 n < dimword (:256)
Proof
  strip_tac >>
  `32 <= dimword (:256)` by simp[dimword_def] >>
  Cases_on `n MOD 32 = 0`
  >- (simp[ceil32_def] >> decide_tac)
  >> simp[ceil32_def] >>
  `n MOD 32 < 32` by simp[] >>
  `32 - n MOD 32 <= 31` by decide_tac >>
  decide_tac
QED

val _ = export_theory();
