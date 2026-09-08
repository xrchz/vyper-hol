(*
 * Builtin, type-builtin, binop, account/env, and call-target typing lemmas.
 *)

Theory vyperTypeBuiltins
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sorting
  words byte integer keccak vyperAST vyperValue vyperValueOperation vyperMisc
  vyperABI vyperInterpreter vyperState vyperContext vyperStorage
  vyperTyping vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeBytesCrypto vyperTypeDefaults vyperTypeConversions vyperTypeABI vyperEvalBinop
  vyperAssignPreservesType bn254 vfmExecution
Libs
  wordsLib
  intLib

(* ===== Environment/account items ===== *)

Theorem Env_builtin_no_type_error:
  context_well_typed cx ∧ item <> MsgGas ==>
  !msg. evaluate_builtin cx acc (env_item_type item) (Env item) [] <> INR (TypeError msg)
Proof
  strip_tac >> Cases_on `item` >>
  gvs[evaluate_builtin_def, env_item_type_def]
  >> rw[evaluate_block_hash_def]
QED

Theorem Env_builtin_success_type:
  context_well_typed cx ∧ evaluate_type tenv (env_item_type item) = SOME tv ∧
  evaluate_builtin cx acc (env_item_type item) (Env item) [] = INL v ==>
  value_has_type tv v
Proof
  Cases_on`item` >> simp[evaluate_builtin_def, env_item_type_def] >>
  rw[] >> gvs[value_has_type_def, evaluate_type_def] >>
  gvs[context_well_typed_def]
  >> gvs[evaluate_block_hash_def, AllCaseEqs(), LET_THM, value_has_type_def]
  >> simp[LENGTH_word_to_bytes,word_to_bytes_be_def]
QED

Theorem account_well_typed_op:
  account_well_typed a ∧ evaluate_type tenv (account_item_type item) = SOME tv ∧
  value_has_type (BaseTV AddressT) addr_v ==>
  value_has_type tv (evaluate_account_op item (case addr_v of BytesV bs => bs | _ => []) a)
Proof
  strip_tac >> Cases_on `addr_v` >> gvs[value_has_type_def] >>
  Cases_on `item` >>
  gvs[account_well_typed_def, account_item_type_def, evaluate_account_op_def,
      evaluate_type_def, value_has_type_def, LENGTH_Keccak_256_w64]
QED

Theorem Acc_builtin_sound:
  accounts_well_typed acc ∧ evaluate_type tenv (account_item_type item) = SOME tv ∧
  value_has_type (BaseTV AddressT) addr_v ==>
  ?v. evaluate_builtin cx acc (account_item_type item) (Acc item) [addr_v] = INL v ∧
      value_has_type tv v
Proof
  Cases_on `addr_v` >> rw[value_has_type_def] >>
  simp[evaluate_builtin_def] >>
  drule_at Any account_well_typed_op >>
  simp[Once(oneline value_has_type_def)] >>
  disch_then(qspec_then`BytesV l`mp_tac) >> simp[] >>
  disch_then irule >>
  gvs[accounts_well_typed_def]
QED

(* ===== Word mask helpers (needed by binop and builtin proofs) ===== *)

Theorem low_mask_eq:
  !m. m <= 256 ==>
    ~(~(0w:bytes32) << m) = n2w (2 ** m - 1)
Proof
  rpt strip_tac >>
  rewrite_tac[wordsTheory.WORD_NOT_0, wordsTheory.LSL_UINT_MAX,
              wordsTheory.word_1comp_n2w] >>
  AP_TERM_TAC >>
  rewrite_tac[wordsTheory.dimword_def] >>
  `dimindex(:256) = 256` by EVAL_TAC >>
  asm_rewrite_tac[] >>
  `2 ** m <= 2 ** 256` by (irule (iffRL EXP_BASE_LE_MONO) >> simp[]) >>
  `(2 ** 256 - 2 ** m) MOD 2 ** 256 = 2 ** 256 - 2 ** m` by simp[LESS_MOD] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem w2n_and_mask_mod:
  !m (w:bytes32). w2n (w && n2w (2 ** m - 1)) = w2n w MOD 2 ** m
Proof
  rpt strip_tac >>
  CONV_TAC (LHS_CONV (RAND_CONV (RATOR_CONV (RAND_CONV
    (REWR_CONV (GSYM wordsTheory.n2w_w2n)))))) >>
  rewrite_tac[wordsTheory.WORD_AND_EXP_SUB1, wordsTheory.w2n_n2w] >>
  irule LESS_MOD >>
  irule LESS_EQ_LESS_TRANS >>
  qexists `w2n w` >>
  simp[MOD_LESS_EQ, wordsTheory.w2n_lt]
QED

Theorem w2n_and_low_mask_lt:
  !m (w:bytes32). m <= 256 ==>
    w2n (w && ~(~0w << m)) < 2 ** m
Proof
  rpt strip_tac >>
  imp_res_tac low_mask_eq >> pop_assum (fn th => rewrite_tac[th]) >>
  simp[w2n_and_mask_mod, MOD_LESS]
QED

(* ===== Binary operations ===== *)

(* Helper: modexp result < modulus when modulus > 0 *)
Theorem modexp_lt:
  !b e m a. 0 < m ==> vfmExecution$modexp b e m a < m
Proof
  simp[vfmExecutionTheory.modexp_exp]
QED

(* Helper: bounded_int_op never produces TypeError *)
Theorem bounded_int_op_no_type_error[local,simp]:
  !u r msg. bounded_int_op u r <> INR (TypeError msg)
Proof
  simp[bounded_int_op_def] >> Cases_on `within_int_bound u r` >> simp[]
QED

(* Helper: bounded_decimal_op never produces TypeError *)
Theorem wrapped_int_op_no_type_error[local,simp]:
  !u r msg. wrapped_int_op u r <> INR (TypeError msg)
Proof
  Cases >> simp[wrapped_int_op_def]
QED

(* INL inversion: bounded_int_op INL gives within_int_bound + result value *)
Theorem bounded_int_op_INL[local]:
  !u r v. bounded_int_op u r = INL v ==>
          ?i. v = IntV i ∧ within_int_bound u i
Proof
  simp[bounded_int_op_def, AllCaseEqs()]
QED

(* INL inversion: bounded_decimal_op INL gives within_int_bound + DecimalV *)
Theorem bounded_decimal_op_INL[local]:
  !r v. bounded_decimal_op r = INL v ==>
        ?d. v = DecimalV d ∧ within_int_bound (Signed 168) d
Proof
  rw[bounded_decimal_op_def, AllCaseEqs()]
QED

(* Boundary lemmas: value_has_type with known type_value constrains value constructor.
   These avoid evaluate_type and work on type_value directly. *)

Theorem vht_BaseTV_UintT[local,simp]:
  value_has_type (BaseTV (UintT n)) v ⇔ ∃i. v = IntV i ∧ 0 ≤ i ∧ Num i < 2 ** n
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_BaseTV_IntT[local,simp]:
  value_has_type (BaseTV (IntT n)) v ⇔ ∃i. v = IntV i ∧ within_int_bound (Signed n) i
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_BaseTV_DecimalT[local,simp]:
  value_has_type (BaseTV DecimalT) v ⇔ ∃d. v = DecimalV d ∧ within_int_bound (Signed 168) d
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_BaseTV_BoolT[local,simp]:
  value_has_type (BaseTV BoolT) v ⇔ ∃b. v = BoolV b
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_FlagTV[local,simp]:
  value_has_type (FlagTV m) v ⇔ ∃k. v = FlagV k ∧ k < 2 ** m
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_BaseTV_StringT[local,simp]:
  value_has_type (BaseTV (StringT m)) v ⇔ ∃s. v = StringV s ∧ LENGTH s ≤ m
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_BaseTV_BytesT_Fixed[local,simp]:
  value_has_type (BaseTV (BytesT (Fixed n))) v ⇔ ∃bs. v = BytesV bs ∧ LENGTH bs = n
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_BaseTV_BytesT_Dynamic[local,simp]:
  value_has_type (BaseTV (BytesT (Dynamic m))) v ⇔ ∃bs. v = BytesV bs ∧ LENGTH bs ≤ m
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_BaseTV_AddressT[local,simp]:
  value_has_type (BaseTV AddressT) v ⇔ ∃bs. v = BytesV bs ∧ LENGTH bs = 20
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem vht_ArrayTV_exists[local]:
  value_has_type (ArrayTV tv bd) v ==> ∃av. v = ArrayV av
Proof
  Cases_on `v` >> simp[value_has_type_def] >> Cases_on `a` >> simp[value_has_type_def]
QED

(* Type classifier inversion lemmas: convert classifiers to disjunctions
   of concrete type constructors. The [simp] catch-all rules (e.g.
   is_int_type _ = F) fire incorrectly when the argument is a free variable
   (e.g. is_int_type (BaseT b) where b is free), losing the UintT/IntT cases.
   These inversion lemmas are MORE SPECIFIC than the catch-alls in the
   discrimination net (pattern BaseT b vs _), so they override for the
   BaseT-b-free case. *)

Theorem is_int_type_inv[local]:
  !ty. is_int_type ty ⇔ (∃n:num. ty = BaseT (UintT n)) ∨ (∃n:num. ty = BaseT (IntT n))
Proof
  gen_tac >> Cases_on `ty` >- (Cases_on `b` >> simp[is_int_type_def] >> metis_tac[]) >>
  simp[is_int_type_def]
QED

Theorem is_uint_type_inv[local]:
  !ty. is_uint_type ty ⇔ (∃n:num. ty = BaseT (UintT n))
Proof
  gen_tac >> Cases_on `ty` >- (Cases_on `b` >> simp[is_uint_type_def] >> metis_tac[]) >>
  simp[is_uint_type_def]
QED

Theorem is_bool_type_inv[local]:
  !ty. is_bool_type ty ⇔ ty = BaseT BoolT
Proof
  gen_tac >> Cases_on `ty` >- (Cases_on `b` >> simp[is_bool_type_def] >> metis_tac[]) >>
  simp[is_bool_type_def]
QED

Theorem is_numeric_type_inv[local]:
  !ty. is_numeric_type ty ⇔ is_int_type ty ∨ ty = BaseT DecimalT
Proof
  gen_tac >> simp[is_numeric_type_def, is_int_type_inv]
QED

Theorem is_flag_type_inv[local]:
  !ty. is_flag_type ty ⇔ (∃fid. ty = FlagT fid)
Proof
  gen_tac >> Cases_on `ty` >> simp[is_flag_type_def]
QED

Theorem is_comparable_type_inv[local]:
  !ty. is_comparable_type ty ⇔ (∃b. ty = BaseT b) ∨ (∃fid. ty = FlagT fid)
Proof
  gen_tac >> Cases_on `ty` >- (simp[is_comparable_type_def] >> metis_tac[]) >>
  simp[is_comparable_type_def]
QED

Theorem is_bytes_or_string_type_inv[local]:
  !ty. is_bytes_or_string_type ty ⇔
    (∃m. ty = BaseT (StringT m)) ∨ (∃bd. ty = BaseT (BytesT bd))
Proof
  gen_tac >> Cases_on `ty` >- (
    Cases_on `b` >> simp[is_bytes_or_string_type_def] >> metis_tac[]) >>
  simp[is_bytes_or_string_type_def]
QED


Theorem binop_negate_INL[local,simp]:
  !b. binop_negate (INL (BoolV b)) = INL (BoolV (~b))
Proof
  simp[binop_negate_def]
QED

Theorem binop_negate_INR[local,simp]:
  !e. binop_negate (INR e) = INR e
Proof
  simp[binop_negate_def]
QED

(* Per-operator no-TypeError helpers: evaluate_binop with concrete
   value constructors never produces TypeError. TypeError only appears
   in value-mismatch fallback branches (| _ => INR(TypeError "binop")),
   which a well-typed value pair never reaches. All other branches give
   INL or INR(RuntimeError), both ≠ INR(TypeError msg). *)

Theorem binop_no_type_error_Add[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Add (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Add_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Add (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Sub[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Sub (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Sub_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Sub (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Mul[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Mul (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Mul_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Mul (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Div[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Div (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_Div_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Div (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_Mod[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Mod (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_Mod_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Mod (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_Exp[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Exp (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_ExpMod[local]:
  !tv i1 i2 msg.
    evaluate_binop (Unsigned 256) tv ExpMod (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_UnsafeAdd[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv UnsafeAdd (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_UnsafeSub[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv UnsafeSub (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_UnsafeMul[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv UnsafeMul (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_UnsafeDiv[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv UnsafeDiv (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_ShL[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv ShL (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_ShR[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv ShR (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  rpt gen_tac >> simp[evaluate_binop_def] >> rpt (COND_CASES_TAC >> simp[])
QED

Theorem binop_no_type_error_And_int[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv And (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_And_bool[local]:
  !u tv b1 b2 msg.
    evaluate_binop u tv And (BoolV b1) (BoolV b2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_And_flag[local]:
  !u tv n1 n2 msg.
    evaluate_binop u tv And (FlagV n1) (FlagV n2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Or_int[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Or (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Or_bool[local]:
  !u tv b1 b2 msg.
    evaluate_binop u tv Or (BoolV b1) (BoolV b2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Or_flag[local]:
  !u tv n1 n2 msg.
    evaluate_binop u tv Or (FlagV n1) (FlagV n2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_XOr_int[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv XOr (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_XOr_bool[local]:
  !u tv b1 b2 msg.
    evaluate_binop u tv XOr (BoolV b1) (BoolV b2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_XOr_flag[local]:
  !u tv n1 n2 msg.
    evaluate_binop u tv XOr (FlagV n1) (FlagV n2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Eq_int[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Eq (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Eq_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Eq (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Eq_bool[local]:
  !u tv b1 b2 msg.
    evaluate_binop u tv Eq (BoolV b1) (BoolV b2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Eq_flag[local]:
  !u tv n1 n2 msg.
    evaluate_binop u tv Eq (FlagV n1) (FlagV n2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Eq_string[local]:
  !u tv s1 s2 msg.
    evaluate_binop u tv Eq (StringV s1) (StringV s2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Eq_bytes[local]:
  !u tv bs1 bs2 msg.
    evaluate_binop u tv Eq (BytesV bs1) (BytesV bs2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Eq_addr[local]:
  !u tv bs1 bs2 msg.
    evaluate_binop u tv Eq (BytesV bs1) (BytesV bs2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Lt[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Lt (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Lt_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Lt (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_LtE[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv LtE (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_LtE_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv LtE (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Gt[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Gt (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Gt_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Gt (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_GtE[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv GtE (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_GtE_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv GtE (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Min[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Min (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Min_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Min (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Max[local]:
  !u tv i1 i2 msg.
    evaluate_binop u tv Max (IntV i1) (IntV i2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_Max_dec[local]:
  !u tv d1 d2 msg.
    evaluate_binop u tv Max (DecimalV d1) (DecimalV d2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_In_flag[local]:
  !tv n1 n2 msg.
    evaluate_binop u tv In (FlagV n1) (FlagV n2) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

Theorem binop_no_type_error_In_array[local]:
  !u tv v av msg.
    evaluate_binop u tv In v (ArrayV av) <> INR (TypeError msg)
Proof
  simp[evaluate_binop_def]
QED

(* Main theorem: well-typed binops never produce TypeError.
   Proof by contradiction: assume evaluate_binop returns INR(TypeError msg),
   then fully resolve type/value constructors using inversion lemmas and gvs.
   After resolution, evaluate_binop_def reduces to INL or INR(RuntimeError),
   contradicting INR(TypeError msg). NotIn/NotEq: binop_negate preserves
   non-TypeError. *)
Theorem well_typed_binop_no_type_error:
  well_typed_binop ty bop t1 t2 ∧
  evaluate_type tenv ty = SOME result_tv ∧
  evaluate_type tenv t1 = SOME tv1 ∧ evaluate_type tenv t2 = SOME tv2 ∧
  value_has_type tv1 v1 ∧ value_has_type tv2 v2 ∧
  u = (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) ==>
  !msg. evaluate_binop u result_tv bop v1 v2 <> INR (TypeError msg)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bop` >>
  gvs[well_typed_binop_def,
      Excl "is_int_type_def", Excl "is_numeric_type_def", Excl "is_bool_type_def",
      Excl "is_flag_type_def", Excl "is_comparable_type_def",
      is_int_type_inv, is_numeric_type_inv, is_bool_type_inv,
      is_flag_type_inv, is_comparable_type_inv] >>
  gvs[evaluate_type_def, type_to_int_bound_def, AllCaseEqs()] >>
  gen_tac >>
  TRY (
    (* NotIn/NotEq: unfold once to binop_negate, then simp with binop_negate lemmas *)
    simp[Once evaluate_binop_def, binop_negate_def] >>
    NO_TAC) >>
  gvs[evaluate_binop_def, AllCaseEqs(), value_has_type_def] >>
  rpt (Cases_on `v2` >> gvs[value_has_type_def]) >>
  rpt (COND_CASES_TAC >> simp[])
QED

Theorem well_typed_builtin_bop_no_type_error[local]:
  well_typed_binop ty bop h h' ∧
  [evaluate_type (get_tenv cx) h; evaluate_type (get_tenv cx) h'] = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty (Bop bop) vs <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  Cases_on `tvs` >> gvs[] >>
  gvs[evaluate_builtin_def] >>
  metis_tac[well_typed_binop_no_type_error]
QED

(* Helper: pure-int characterization of within_int_bound (Signed m) *)
Theorem within_int_bound_signed_int[local]:
  !m i. 0 < m ==>
        (within_int_bound (Signed m) i ⇔
         -&(2 ** (m - 1)) ≤ i ∧ i < &(2 ** (m - 1)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[within_int_bound_def, LET_THM] >>
  Cases_on `i < 0` >> simp[] >-
  ((* i < 0 *)
   `0 ≤ -i` by intLib.ARITH_TAC >>
   simp[Once (GSYM integerTheory.INT_OF_NUM)] >>
   `0 ≤ &(2 ** (m - 1))` by simp[] >>
   EQ_TAC >> strip_tac >> intLib.ARITH_TAC) >-
  ((* i ≥ 0 *)
   `0 ≤ i` by intLib.ARITH_TAC >>
   simp[Once (GSYM integerTheory.INT_OF_NUM)] >>
   `0 ≤ &(2 ** (m - 1))` by simp[] >>
   EQ_TAC >> strip_tac >> intLib.ARITH_TAC)
QED

(* Helper: signed_int_mod preserves within_int_bound (Signed m) *)
Theorem signed_int_mod_within_bound[local]:
  !m i. 0 < m ==> within_int_bound (Signed m) (signed_int_mod m i)
Proof
  rpt strip_tac >>
  simp[within_int_bound_signed_int, signed_int_mod_def, LET_THM] >>
  `2 ** m = 2 * 2 ** (m - 1)` by
    (`m = SUC (m - 1)` by simp[] >> pop_assum SUBST1_TAC >> simp[EXP]) >>
  `&(2 ** m) ≠ 0i` by simp[] >>
  `0i < &(2 ** m)` by simp[] >>
  drule integerTheory.INT_MOD_BOUNDS >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  qabbrev_tac `r = i % &(2 ** m)` >>
  Cases_on `r ≥ &(2 ** (m - 1))` >> simp[] >>
  qpat_x_assum `Abbrev _` kall_tac >>
  `¬(&(2 ** m) < 0i)` by simp[] >> fs[] >>
  pop_assum kall_tac >>
  qpat_x_assum `2 ** m = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE[th, GSYM integerTheory.INT_MUL]) >>
    PURE_REWRITE_TAC[th, GSYM integerTheory.INT_MUL]) >>
  qabbrev_tac `k = &(2 ** (m - 1)):int` >>
  qpat_x_assum `Abbrev _` kall_tac >>
  intLib.ARITH_TAC
QED


(* Helper: int % &(2^n) is in unsigned range [0, 2^n) *)
Theorem int_mod_unsigned_within_bound[local]:
  !m i. 0 < m ==> within_int_bound (Unsigned m) (i % &(2 ** m))
Proof
  rpt strip_tac >>
  simp[within_int_bound_def] >>
  `0i < &(2 ** m)` by simp[] >>
  `&(2 ** m) ≠ 0i` by simp[] >>
  drule integerTheory.INT_MOD_BOUNDS >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  gvs[] >>
  (* Remaining: Num (i % &(2 ** m)) < 2 ** m *)
  (* Num_int_lt: 0 <= a ∧ a < b ==> Num a < Num b, plus Num (&(2**m)) = 2**m *)
  `Num (i % &(2 ** m)) < Num (&(2 ** m))` by (
    irule vyperArithTheory.Num_int_lt >> simp[]) >>
  pop_assum mp_tac >> simp[integerTheory.INT_OF_NUM]
QED

(* INL inversion: wrapped_int_op INL gives within_int_bound + IntV *)
Theorem wrapped_int_op_INL[local]:
  !u r v. 0 < int_bound_bits u ∧ wrapped_int_op u r = INL v ==>
        ∃i. v = IntV i ∧ within_int_bound u i
Proof
  Cases_on `u` >> simp[wrapped_int_op_def, int_bound_bits_def, is_Unsigned_def] >>
  rpt strip_tac
  >- (irule signed_int_mod_within_bound >> simp[]) >>
  irule int_mod_unsigned_within_bound >> simp[]
QED

(* ===== Additional bound helpers for well_typed_binop_success_type ===== *)

(* Int division upper bound: x / d < n implies x < n * d *)
Theorem int_div_lt_imp[local]:
  !x d (n:int). 0 ≤ x ∧ 0 < d ∧ x / d < n ==> x < n * d
Proof
  rpt strip_tac >>
  `?xn. x = &xn` by (qexists_tac `Num x` >> fs[integerTheory.INT_OF_NUM]) >>
  `?dn. d = &dn ∧ 0 < dn`
    by (qexists_tac `Num d` >> fs[integerTheory.INT_OF_NUM,
          integerTheory.INT_LT] >> intLib.ARITH_TAC) >>
  `&dn ≠ (0:int)` by intLib.ARITH_TAC >>
  fs[integerTheory.INT_DIV] >>
  `0 ≤ (n:int)` by (spose_not_then assume_tac >>
    fs[integerTheory.INT_NOT_LE] >> intLib.ARITH_TAC) >>
  `?nn. n = &nn` by (qexists_tac `Num n` >> fs[integerTheory.INT_OF_NUM]) >>
  fs[integerTheory.INT_LT, integerTheory.INT_MUL] >>
  fs[arithmeticTheory.DIV_LT_X]
QED

(* Decimal Mul: w2i(word_quot(i2w p) / 10^10w) preserves Signed 168 bound *)
Theorem decimal_mul_word_bound[local]:
  !p. within_int_bound (Signed 168) (ABS p / 10000000000) ==>
      within_int_bound (Signed 168) (w2i ((i2w p : bytes32) / 0x2540BE400w))
Proof
  rpt strip_tac >>
  `ABS p / 10000000000 < 2 ** 167`
    by (qpat_x_assum `within_int_bound _ _` mp_tac >>
        simp[within_int_bound_def, LET_THM] >>
        `0 ≤ ABS p / 10000000000` by
          (simp[integerTheory.int_div, integerTheory.INT_ABS] >>
           Cases_on `0 ≤ p` >> simp[] >> intLib.ARITH_TAC) >>
        intLib.ARITH_TAC) >>
  `ABS p < 2 ** 167 * 10000000000`
    by (qspecl_then [`ABS p`, `10000000000`, `2 ** 167`] mp_tac int_div_lt_imp >>
        simp[integerTheory.INT_ABS_POS]) >>
  `ABS p < 2 ** 255`
    by (`(2:int) ** 167 * 10000000000 < 2 ** 255` by EVAL_TAC >> intLib.ARITH_TAC) >>
  `within_int_bound (Signed 256) p`
    by (simp[within_int_bound_def, LET_THM] >>
        Cases_on `p < 0` >>
        fs[integerTheory.INT_ABS, integerTheory.INT_NOT_LT] >>
        intLib.ARITH_TAC) >>
  `w2i (i2w p : bytes32) = p`
    by (qspecl_then [`p`, `256`] mp_tac w2i_i2w_within_signed >> simp[]) >>
  `(0x2540BE400w : bytes32) ≠ 0w` by EVAL_TAC >>
  `w2i (0x2540BE400w : bytes32) = 10000000000` by EVAL_TAC >>
  `(i2w p : bytes32) / 0x2540BE400w = i2w (p quot 10000000000)`
    by (drule integer_wordTheory.word_quot >>
        disch_then (qspec_then `i2w p` mp_tac) >> simp[]) >>
  `ABS (p quot 10000000000) = ABS p / 10000000000`
    by (`(10000000000:int) ≠ 0` by intLib.ARITH_TAC >>
        simp[integerTheory.int_quot, integerTheory.int_div] >>
        Cases_on `0 ≤ p` >> simp[integerTheory.INT_ABS] >> intLib.ARITH_TAC) >>
  `within_int_bound (Signed 168) (p quot 10000000000)`
    by (qpat_x_assum `within_int_bound _ (ABS p / _)` mp_tac >>
        simp[within_int_bound_def, LET_THM] >>
        Cases_on `p quot 10000000000 < 0` >>
        Cases_on `ABS p / 10000000000 < 0` >> fs[] >> intLib.ARITH_TAC) >>
  `within_int_bound (Signed 256) (p quot 10000000000)`
    by (qpat_x_assum `within_int_bound (Signed 168) _` mp_tac >>
        simp[within_int_bound_def, LET_THM] >>
        Cases_on `p quot 10000000000 < 0` >> fs[] >> intLib.ARITH_TAC) >>
  `w2i (i2w (p quot 10000000000) : bytes32) = p quot 10000000000`
    by (qspecl_then [`p quot 10000000000`, `256`] mp_tac w2i_i2w_within_signed >> simp[]) >>
  simp[]
QED

(* --- int_shift_right bounds machinery --- *)

Theorem num_of_bits_bits_of_num[local]:
  !n. num_of_bits (bits_of_num n) = n
Proof
  gen_tac >>
  mp_tac (Q.SPEC `&n` int_bitwiseTheory.int_of_bits_bits_of_int) >>
  simp[int_bitwiseTheory.bits_of_int_def, int_bitwiseTheory.int_of_bits_def]
QED

Theorem num_of_bits_drop_le[local]:
  !bs m. num_of_bits (DROP m bs) ≤ num_of_bits bs
Proof
  Induct >> simp[int_bitwiseTheory.num_of_bits_def, listTheory.DROP_def] >>
  rpt gen_tac >> Cases_on `m` >>
  simp[int_bitwiseTheory.num_of_bits_def] >>
  Cases_on `h` >> simp[int_bitwiseTheory.num_of_bits_def] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem MAP_DROP[local]:
  !f bs m. MAP f (DROP m bs) = DROP m (MAP f bs)
Proof
  gen_tac >> Induct >> simp[listTheory.DROP_def] >>
  rpt gen_tac >> Cases_on `m` >> simp[listTheory.DROP_def]
QED

Theorem int_shift_right_nonneg_bounds[local]:
  !m i. 0 ≤ i ==> 0 ≤ int_shift_right m i ∧ int_shift_right m i ≤ i
Proof
  rpt strip_tac >>
  `¬(i < 0)` by intLib.ARITH_TAC >>
  simp[int_bitwiseTheory.int_shift_right_def,
       int_bitwiseTheory.bits_of_int_def,
       int_bitwiseTheory.int_of_bits_def, LET_THM,
       pairTheory.UNCURRY_DEF] >>
  `num_of_bits (DROP m (bits_of_num (Num i))) ≤ num_of_bits (bits_of_num (Num i))`
    by simp[num_of_bits_drop_le] >>
  fs[num_of_bits_bits_of_num] >>
  metis_tac[integerTheory.INT_OF_NUM, integerTheory.INT_LE,
            integerTheory.INT_LE_TRANS]
QED

Theorem int_shift_right_neg_bounds[local]:
  !m i. i < 0 ==> int_shift_right m i < 0 ∧ i ≤ int_shift_right m i
Proof
  rpt strip_tac >>
  qabbrev_tac `k = Num (-i - 1)` >>
  `0 ≤ -i - 1` by intLib.ARITH_TAC >>
  `int_not i = -i - 1` by simp[int_bitwiseTheory.int_not_def] >>
  simp[int_bitwiseTheory.int_shift_right_def,
       int_bitwiseTheory.bits_of_int_def, LET_THM,
       pairTheory.UNCURRY_DEF] >>
  simp[int_bitwiseTheory.int_of_bits_def, MAP_DROP] >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  `num_of_bits (DROP m (bits_of_num k)) ≤ k`
    by metis_tac[num_of_bits_drop_le, num_of_bits_bits_of_num,
                  LESS_EQ_TRANS] >>
  simp[int_bitwiseTheory.int_not_def] >>
  `&k = -i - 1` by (qunabbrev_tac `k` >> metis_tac[integerTheory.INT_OF_NUM]) >>
  qabbrev_tac `j = num_of_bits (DROP m (bits_of_num k))` >>
  `&j ≤ &k` by simp[integerTheory.INT_LE] >>
  intLib.ARITH_TAC
QED

Theorem int_shift_right_within_bound[local]:
  !m n i. 0 < n ∧ within_int_bound (Signed n) i ==>
          within_int_bound (Signed n) (int_shift_right m i)
Proof
  rpt strip_tac >>
  `!j. within_int_bound (Signed n) j ⇔ -&(2 ** (n-1)) ≤ j ∧ j < &(2 ** (n-1))`
    by simp[within_int_bound_signed_int] >>
  fs[] >>
  Cases_on `0 ≤ i`
  >- (
    drule int_shift_right_nonneg_bounds >>
    disch_then (qspec_then `m` strip_assume_tac) >>
    intLib.ARITH_TAC)
  >- (
    `i < 0` by intLib.ARITH_TAC >>
    drule int_shift_right_neg_bounds >>
    disch_then (qspec_then `m` strip_assume_tac) >>
    intLib.ARITH_TAC)
QED

Theorem int_shift_right_unsigned_within_bound[local]:
  !m n i. 0 < n ∧ 0 ≤ i ∧ i < &(2 ** n) ==>
          0 ≤ int_shift_right m i ∧ int_shift_right m i < &(2 ** n)
Proof
  rpt strip_tac >>
  drule int_shift_right_nonneg_bounds >>
  disch_then (qspec_then `m` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

(* --- int_bitwise bounds machinery --- *)

Theorem int_bitwise_eq_BITWISE[local]:
  !f a b k. a < 2 ** k ∧ b < 2 ** k ∧ ¬f F F ==>
    int_bitwise f (&a) (&b) = &(BITWISE k f a b)
Proof
  rpt strip_tac >>
  simp[int_bitwiseTheory.int_bit_equiv] >>
  gen_tac >>
  simp[int_bitwiseTheory.int_bit_bitwise, int_bitwiseTheory.int_bit_def] >>
  Cases_on `n < k` >- (
    `¬((&(BITWISE k f a b)):int < 0)` by simp[] >>
    ASM_SIMP_TAC std_ss [integerTheory.NUM_OF_INT] >>
    simp[bitTheory.BITWISE_THM]) >>
  `¬((&a):int < 0) ∧ ¬((&b):int < 0)` by simp[] >>
  ASM_SIMP_TAC std_ss [integerTheory.NUM_OF_INT] >>
  `¬BIT n a` by (irule bitTheory.NOT_BIT_GT_TWOEXP >>
                  irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >> simp[]) >>
  `¬BIT n b` by (irule bitTheory.NOT_BIT_GT_TWOEXP >>
                  irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >> simp[]) >>
  ASM_REWRITE_TAC[] >>
  `¬((&(BITWISE k f a b)):int < 0)` by simp[] >>
  ASM_SIMP_TAC std_ss [integerTheory.NUM_OF_INT] >>
  irule bitTheory.NOT_BIT_GT_TWOEXP >>
  irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >>
  simp[bitTheory.BITWISE_LT_2EXP]
QED

Theorem int_bitwise_nat_bound[local]:
  !f a b k. a < 2 ** k ∧ b < 2 ** k ∧ ¬f F F ==>
    0 ≤ int_bitwise f (&a) (&b) ∧ Num (int_bitwise f (&a) (&b)) < 2 ** k
Proof
  rpt strip_tac >>
  qspecl_then [`f`,`a`,`b`,`k`] mp_tac int_bitwise_eq_BITWISE >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  ASM_REWRITE_TAC[] >> simp[bitTheory.BITWISE_LT_2EXP]
QED

(* --- Bridge lemmas for well_typed_binop_success_type remaining goals --- *)

Theorem int_bitwise_nat_bound_lt[local]:
  !f a b k. a < 2 ** k ∧ b < 2 ** k ∧ ¬f F F ==>
    Num (int_bitwise f (&a) (&b)) < 2 ** k
Proof
  rpt strip_tac >> imp_res_tac int_bitwise_nat_bound >> simp[]
QED

Theorem int_shift_right_unsigned_Num_bound[local]:
  !m i n. 0 ≤ i ∧ Num i < 2 ** n ==>
    0 ≤ int_shift_right m i ∧ Num (int_shift_right m i) < 2 ** n
Proof
  rpt strip_tac >-
    (qspecl_then [`m`,`i`] mp_tac int_shift_right_nonneg_bounds >> simp[]) >>
  qspecl_then [`m`,`i`] mp_tac int_shift_right_nonneg_bounds >>
  simp[] >> strip_tac >>
  `Num (int_shift_right m i) ≤ Num i` suffices_by decide_tac >>
  Cases_on `int_shift_right m i = i` >- simp[] >>
  `int_shift_right m i < i` by metis_tac[integerTheory.INT_LT_LE] >>
  imp_res_tac Num_int_lt >> simp[]
QED

Theorem w2n_word_exp_lt_256[local]:
  !i i'. w2n (i2w i ** i2w i' : 256 word) < dimword (:256)
Proof
  irule wordsTheory.w2n_lt
QED

Theorem within_int_bound_min[local]:
  !n i i'. within_int_bound (Signed n) i ∧ within_int_bound (Signed n) i' ==>
    ∃i''. (i < i' ∧ i = i'' ∨ ¬(i < i') ∧ i' = i'') ∧ within_int_bound (Signed n) i''
Proof
  rpt strip_tac >> Cases_on `i < i'` >-
    (qexists_tac `i` >> simp[]) >>
  qexists_tac `i'` >> simp[]
QED

Theorem within_int_bound_max[local]:
  !n i i'. within_int_bound (Signed n) i ∧ within_int_bound (Signed n) i' ==>
    ∃i''. (i < i' ∧ i' = i'' ∨ ¬(i < i') ∧ i = i'') ∧ within_int_bound (Signed n) i''
Proof
  rpt strip_tac >> Cases_on `i < i'` >-
    (qexists_tac `i'` >> simp[]) >>
  qexists_tac `i` >> simp[]
QED


(* --- ShL: evaluate_binop applies int_mod/signed_int_mod after int_shift_left,
   so the bounds follow from int_mod_unsigned_within_bound and
   signed_int_mod_within_bound (already proved above). No separate
   int_shift_left bound lemma is needed. --- *)

(* --- wrapped_int_op for pre-resolved u --- *)

Theorem wrapped_int_op_INL_Unsigned[local]:
  !n r v. 0 < n ∧ wrapped_int_op (Unsigned n) r = INL v ==>
    ∃i. v = IntV i ∧ 0 ≤ i ∧ Num i < 2 ** n
Proof
  rpt strip_tac >>
  `0 < int_bound_bits (Unsigned n)` by simp[int_bound_bits_def] >>
  imp_res_tac wrapped_int_op_INL >>
  gvs[within_int_bound_def] >>
  qexists_tac `i` >> simp[]
QED

Theorem wrapped_int_op_INL_Signed[local]:
  !n r v. 1 < n ∧ wrapped_int_op (Signed n) r = INL v ==>
    ∃i. v = IntV i ∧ within_int_bound (Signed n) i
Proof
  rpt strip_tac >>
  `0 < int_bound_bits (Signed n)` by (simp[int_bound_bits_def] >> intLib.ARITH_TAC) >>
  imp_res_tac wrapped_int_op_INL >>
  gvs[within_int_bound_def] >>
  qexists_tac `i` >> simp[]
QED


Theorem negated_flag_membership_INL[local]:
  binop_negate (evaluate_binop u tv In (FlagV k) (FlagV k')) = INL v ==>
  ?b. v = BoolV b
Proof
  simp[Once evaluate_binop_def, binop_negate_def] >> strip_tac >>
  qexists_tac `int_and (&k) (&k') = 0` >> gvs[]
QED

Theorem negated_array_membership_INL[local]:
  value_has_type (ArrayTV tv bd) v2 /\
  binop_negate (evaluate_binop u result_tv In v1 v2) = INL v ==>
  ?b. v = BoolV b
Proof
  Cases_on `v2` >> gvs[value_has_type_def] >>
  simp[Once evaluate_binop_def, binop_negate_def] >>
  metis_tac[]
QED

Theorem negated_equality_INL[local]:
  binop_negate (evaluate_binop u tv Eq v1 v2) = INL v ==>
  ?b. v = BoolV b
Proof
  Cases_on `v1` >> Cases_on `v2` >>
  simp[Once evaluate_binop_def, binop_negate_def] >>
  metis_tac[]
QED

Theorem well_typed_binop_success_type:
  well_typed_binop ty bop t1 t2 ∧
  evaluate_type tenv ty = SOME result_tv ∧
  evaluate_type tenv t1 = SOME tv1 ∧ evaluate_type tenv t2 = SOME tv2 ∧
  value_has_type tv1 v1 ∧ value_has_type tv2 v2 ∧
  u = (case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u) ∧
  evaluate_binop u result_tv bop v1 v2 = INL v ==>
  value_has_type result_tv v
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bop` >>
  gvs[well_typed_binop_def,
      Excl "is_int_type_def", Excl "is_numeric_type_def",
      Excl "is_bool_type_def", Excl "is_flag_type_def",
      Excl "is_comparable_type_def"] >>
  gvs[is_int_type_inv, is_numeric_type_inv] >>
  gvs[is_bool_type_inv, is_flag_type_inv, is_comparable_type_inv] >>
  gvs[evaluate_type_def] >>
  gvs[type_to_int_bound_def] >>
  gvs[AllCaseEqs()] >>
  (* Signed Add: route the successful bounded operation through its inversion lemma. *)
  TRY (
    qpat_x_assum `evaluate_binop (Signed n) (BaseTV (IntT n)) Add
                    (IntV i) (IntV i') = INL v` mp_tac >>
    simp[Once evaluate_binop_def] >> strip_tac >>
    imp_res_tac bounded_int_op_INL >> gvs[] >> NO_TAC) >>
  (* NotIn/NotEq: unfold once to binop_negate, result is BoolV *)
  TRY (
    simp[Once evaluate_binop_def, binop_negate_def] >> NO_TAC) >>
  (* In: result is FlagV or BoolV *)
  TRY (
    simp[Once evaluate_binop_def] >>
    first_assum (irule_at (Pat `value_has_type _ (FlagV _)`)) >> NO_TAC) >>
  (* Comparison: BoolV result *)
  TRY (
    simp[Once evaluate_binop_def] >>
    rpt (Cases_on `v1` >> gvs[value_has_type_def]) >>
    rpt (Cases_on `v2` >> gvs[value_has_type_def]) >>
    first_assum (irule_at (Pat `value_has_type _ (BoolV _)`)) >> NO_TAC) >>
  (* Flag bitwise: FlagV result with w2n_and_low_mask_lt *)
  TRY (
    simp[Once evaluate_binop_def] >>
    gvs[value_has_type_def, w2n_and_low_mask_lt] >> NO_TAC) >>
  (* All remaining: expand evaluate_binop but keep bounded/wrapped ops opaque.
     Use INL inversion lemmas to extract within_int_bound. *)
  qpat_x_assum `evaluate_binop _ _ _ _ _ = INL v` mp_tac >>
  PURE_ONCE_REWRITE_TAC[evaluate_binop_def] >>
  PURE_REWRITE_TAC[vyperASTTheory.binop_case_def,
                   vyperValueTheory.value_case_def] >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  gvs[value_has_type_def, Excl "within_int_bound_def"] >>
  (* Re-abstract within_int_bound that got expanded by value_has_type_def *)
  TRY (simp[GSYM within_int_bound_def] >> NO_TAC) >>
  (* Bounded int ops: INL gives within_int_bound *)
  TRY (
    imp_res_tac bounded_int_op_INL >>
    gvs[within_int_bound_def] >> NO_TAC) >>
  (* Bounded decimal ops: INL gives within_int_bound (Signed 168) *)
  TRY (
    imp_res_tac bounded_decimal_op_INL >>
    gvs[within_int_bound_def] >> NO_TAC) >>
  (* Wrapped int ops (Unsigned): use specialized lemma *)
  TRY (
    imp_res_tac wrapped_int_op_INL_Unsigned >>
    gvs[within_int_bound_def] >> NO_TAC) >>
  (* Wrapped int ops (Signed): use specialized lemma *)
  TRY (
    imp_res_tac wrapped_int_op_INL_Signed >>
    gvs[within_int_bound_def] >> NO_TAC) >>
  (* Decimal Mul: bridge word_quot to integer division *)
  TRY (
    imp_res_tac decimal_mul_word_bound >>
    gvs[within_int_bound_def] >> NO_TAC) >>
  (* ExpMod: word_exp result bounded by 2^256 *)
  TRY (
    mp_tac w2n_word_exp_lt_256 >> simp[] >> NO_TAC) >>
  (* Flag bitwise: unfold to int_bitwise, apply nat bound (just the < part) *)
  PURE_REWRITE_TAC[int_bitwiseTheory.int_and_def, int_bitwiseTheory.int_or_def,
                   int_bitwiseTheory.int_xor_def] >>
  TRY (
    mp_tac int_bitwise_nat_bound_lt >> simp[] >> NO_TAC) >>
  (* ShL/ShR: re-abstract to within_int_bound, then use bound lemmas *)
  TRY (
    simp[GSYM within_int_bound_def] >>
    irule int_mod_unsigned_within_bound >> simp[] >> NO_TAC) >>
  TRY (
    simp[GSYM within_int_bound_def] >>
    irule signed_int_mod_within_bound >> simp[] >> NO_TAC) >>
  TRY (
    simp[GSYM within_int_bound_def] >>
    irule int_shift_right_within_bound >> simp[] >> NO_TAC) >>
  (* ShR unsigned: expanded to 0 ≤ X ∧ Num X < 2**n form, use bridge lemma *)
  TRY (
    irule int_shift_right_unsigned_Num_bound >> simp[] >> NO_TAC) >>
  (* In_array: resolve binop_negate value constructors *)
  TRY (
    Cases_on `v2` >> gvs[value_has_type_def, binop_negate_INL] >> NO_TAC) >>
  (* Min: choose the smaller value *)
  TRY (
    irule within_int_bound_min >> simp[] >> NO_TAC) >>
  (* Max: choose the larger value *)
  TRY (
    irule within_int_bound_max >> simp[] >> NO_TAC) >>
  (* Negated flag membership has a boolean result. *)
  TRY (drule_all_then ACCEPT_TAC negated_flag_membership_INL >> NO_TAC) >>
  TRY (drule_all_then ACCEPT_TAC negated_array_membership_INL >> NO_TAC) >>
  TRY (drule_all_then ACCEPT_TAC negated_equality_INL >> NO_TAC) >>
  (* Negated membership/equality: expose the inner boolean result. *)
  TRY (
    qpat_x_assum `binop_negate _ = INL v` mp_tac >>
    simp[Once evaluate_binop_def, binop_negate_def] >> NO_TAC) >>
  (* Catch-all for simple remaining cases *)
  TRY (gvs[within_int_bound_def] >> NO_TAC) >>
  TRY (intLib.ARITH_TAC >> NO_TAC) >>
  TRY (gvs[] >> NO_TAC)
QED
Theorem builtin_bop_success_type[local]:
  well_typed_binop ty bop t1 t2 /\
  [evaluate_type (get_tenv cx) t1; evaluate_type (get_tenv cx) t2] = MAP SOME tvs /\
  evaluate_type (get_tenv cx) ty = SOME result_tv /\
  LIST_REL value_has_type tvs vs /\
  evaluate_builtin cx acc ty (Bop bop) vs = INL v ==>
  value_has_type result_tv v
Proof
  rpt strip_tac >>
  Cases_on `tvs` >> gvs[evaluate_builtin_def] >>
  irule well_typed_binop_success_type >>
  qexistsl [`bop`, `t1`, `t2`, `get_tenv cx`, `h`, `x0`, `ty`,
            `case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u`,
            `y`, `y'`] >>
  gvs[]
QED

(* ===== Builtins ===== *)

Theorem int_type_Num_bound:
  !tyv i. value_has_type tyv (IntV i) ∧ well_formed_type_value tyv ==>
          Num i < 2 ** 256
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `_ < bound` >>
  qpat_x_assum `value_has_type _ _` mp_tac >>
  simp[value_has_type_inv] >> strip_tac >> gvs[well_formed_type_value_def]
  >- (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** n` >>
      unabbrev_all_tac >> simp[] >>
      irule (iffRL EXP_BASE_LE_MONO) >> simp[]) >>
  Cases_on `n = 0` >- (unabbrev_all_tac >> gvs[within_int_bound_def]) >>
  gvs[within_int_bound_def, LET_THM, Num_neg] >>
  Cases_on `i < 0` >> gvs[] >>
  irule LESS_EQ_LESS_TRANS >>
  qexists_tac `2 ** (n - 1)` >>
  unabbrev_all_tac >>
  (reverse conj_tac >- simp[]) >>
  irule LESS_LESS_EQ_TRANS >>
  qexists_tac`2 ** 256` >>
  (reverse conj_tac >- (
     rewrite_tac[LESS_OR_EQ] >>
     disj2_tac >>
     simp[])) >>
  simp[]
QED

Theorem uint2str_strlen_bound:
  !tyv i. value_has_type tyv (IntV i) ∧ well_formed_type_value tyv ==>
          STRLEN (toString (Num i)) ≤ 78
Proof
  rpt strip_tac >>
  imp_res_tac int_type_Num_bound >>
  qmatch_asmsub_abbrev_tac `Num i < bound` >>
  simp[ASCIInumbersTheory.LENGTH_num_to_dec_string] >>
  Cases_on `i = 0` >> gvs[] >>
  `0 < Num i` by intLib.ARITH_TAC >>
  `Num i ≤ bound - 1` by decide_tac >>
  `LOG 10 (Num i) ≤ LOG 10 (bound - 1)` by
    (irule logrootTheory.LOG_LE_MONO >> simp[]) >>
  `LOG 10 (bound - 1) = 77` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  decide_tac
QED

Theorem floor_decimal_in_int256_bounds:
  within_int_bound (Signed 168) i ==>
  -(&(2 ** 255)) ≤ i / 10000000000 ∧
  i / 10000000000 < &(2 ** 255)
Proof
  rw[within_int_bound_def] >>
  `10000000000:int ≠ 0` by intLib.ARITH_TAC >>
  drule INT_DIVISION >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

Theorem ceil_decimal_in_int256_bounds:
  within_int_bound (Signed 168) i ==>
  -(&(2 ** 255)) ≤ (i + 9999999999) / 10000000000 ∧
  (i + 9999999999) / 10000000000 < &(2 ** 255)
Proof
  rw[within_int_bound_def] >>
  `10000000000:int ≠ 0` by intLib.ARITH_TAC >>
  drule INT_DIVISION >>
  disch_then (qspec_then `i + 9999999999` strip_assume_tac) >>
  intLib.ARITH_TAC
QED
Theorem ceil_builtin_success_type[local]:
  !cx acc d v.
    within_int_bound (Signed 168) d /\
    evaluate_builtin cx acc (BaseT (IntT 256)) Ceil [DecimalV d] = INL v ==>
    ?i. v = IntV i /\ within_int_bound (Signed 256) i
Proof
  rpt strip_tac >>
  gvs[evaluate_builtin_def] >>
  drule ceil_decimal_in_int256_bounds >> strip_tac >>
  `2 ** 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968` by EVAL_TAC >>
  gvs[within_int_bound_signed_int]
QED

Theorem floor_builtin_success_type[local]:
  !cx acc d v.
    within_int_bound (Signed 168) d /\
    evaluate_builtin cx acc (BaseT (IntT 256)) Floor [DecimalV d] = INL v ==>
    ?i. v = IntV i /\ within_int_bound (Signed 256) i
Proof
  rpt strip_tac >>
  gvs[evaluate_builtin_def] >>
  drule floor_decimal_in_int256_bounds >> strip_tac >>
  `2 ** 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968` by EVAL_TAC >>
  gvs[within_int_bound_signed_int]
QED


Theorem well_typed_builtin_app_length:
  well_typed_builtin_app ty blt ts ==> builtin_args_length_ok blt (LENGTH ts)
Proof
  simp[oneline well_typed_builtin_app_def] >>
  Cases_on `blt` >> rw[builtin_args_length_ok_def] >>
  pop_assum mp_tac >> CASE_TAC >> rw[]
QED

(* Helper: Flag Not never produces TypeError when well-typed *)
Theorem flag_Not_no_type_error[local]:
  context_well_typed cx ∧
  evaluate_type (get_tenv cx) (FlagT fid) = SOME tv ∧
  value_has_type tv y ==>
  !msg. evaluate_builtin cx acc (FlagT fid) Not [y] ≠ INR (TypeError msg)
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  gvs[value_has_type_def] >>
  (* evaluate_type_def must be expanded alongside evaluate_builtin_def
     so the simplifier resolves 'case evaluate_type ... of' using the FLOOKUP assumption *)
  simp[evaluate_type_def, evaluate_builtin_def] >>
  irule w2n_and_low_mask_lt >> simp[]
QED

(* Helper: AsWeiValue with UintT input never produces TypeError *)
Theorem as_wei_value_uint_no_type_error[local]:
  is_uint_type ty ∧ evaluate_type (get_tenv cx) ty = SOME tv ∧
  value_has_type tv v ==>
  !msg. evaluate_builtin cx acc ty (AsWeiValue dn) [v] ≠ INR (TypeError msg)
Proof
  strip_tac >>
  gvs[is_uint_type_def] >>
  gvs[evaluate_type_def] >>
  (* v must be IntV i since value_has_type (BaseTV (UintT n)) v *)
  gvs[vht_BaseTV_UintT] >>
  simp[evaluate_builtin_def, evaluate_as_wei_value_def, LET_THM] >>
  Cases_on `dn` >> simp[within_int_bound_def] >> intLib.ARITH_TAC
QED

(* Helper: LIST_REL with BytesT types implies all values are BytesV *)
(* evaluate_concat_loop never produces TypeError when all values are BytesV *)
Theorem evaluate_concat_loop_bytes_no_type_error[local]:
  !n b1 sa ba vs.
    EVERY (λv. ∃bs. v = BytesV bs) vs ⇒
    !msg. evaluate_concat_loop n (BytesV b1) sa ba vs ≠ INR (TypeError msg)
Proof
  Induct_on `vs` >> rw[evaluate_concat_loop_def] >>
  gvs[evaluate_concat_loop_def, AllCaseEqs()] >>
  first_x_assum $ qspecl_then [`n`,`b1`,`sa`,`b2::ba`,`msg`] mp_tac >> simp[]
QED

(* evaluate_concat_loop never produces TypeError when all values are StringV *)
Theorem evaluate_concat_loop_string_no_type_error[local]:
  !n s1 sa ba vs.
    EVERY (λv. ∃s. v = StringV s) vs ⇒
    !msg. evaluate_concat_loop n (StringV s1) sa ba vs ≠ INR (TypeError msg)
Proof
  Induct_on `vs` >> rw[evaluate_concat_loop_def] >>
  gvs[evaluate_concat_loop_def, AllCaseEqs()] >>
  first_x_assum $ qspecl_then [`n`,`s1`,`s2::sa`,`ba`,`msg`] mp_tac >> simp[]
QED

(* evaluate_concat_loop success typing for byte results. *)
Theorem evaluate_concat_loop_bytes_success_type[local]:
  !n b1 sa ba vs v.
    evaluate_concat_loop n (BytesV b1) sa ba vs = INL v ==>
    ?bs. v = BytesV bs ∧ LENGTH bs <= n
Proof
  Induct_on `vs` >>
  rw[evaluate_concat_loop_def, LET_THM, compatible_bound_def, AllCaseEqs()] >>
  Cases_on `h` >> gvs[evaluate_concat_loop_def] >>
  first_x_assum drule >> simp[]
QED

(* evaluate_concat_loop success typing for string results. *)
Theorem evaluate_concat_loop_string_success_type[local]:
  !n s1 sa ba vs v.
    evaluate_concat_loop n (StringV s1) sa ba vs = INL v ==>
    ?s. v = StringV s ∧ LENGTH s <= n
Proof
  Induct_on `vs` >>
  rw[evaluate_concat_loop_def, LET_THM, compatible_bound_def, AllCaseEqs()] >>
  Cases_on `h` >> gvs[evaluate_concat_loop_def] >>
  first_x_assum drule >> simp[]
QED

Theorem list_rel_bytes_all_bytesv[local]:
  !vs tys tenv.
    LIST_REL (λv t. ∃tyv. evaluate_type tenv t = SOME tyv ∧ value_has_type tyv v) vs tys ∧
    EVERY (λt. ∃bd. t = BaseT (BytesT bd)) tys ⇒
    EVERY (λv. ∃bs. v = BytesV bs) vs
Proof
  Induct >> rw[LIST_REL_CONS1] >> gvs[] >>
  first_x_assum drule >> (impl_tac >- simp[]) >> simp[] >>
  Cases_on `bd` >>
  gvs[evaluate_type_def, LET_THM, AllCaseEqs()] >>
  Cases_on `h` >> gvs[value_has_type_def]
QED

Theorem list_rel_string_all_stringv[local]:
  !vs tys tenv.
    LIST_REL (λv t. ∃tyv. evaluate_type tenv t = SOME tyv ∧ value_has_type tyv v) vs tys ∧
    EVERY (λt. ∃m. t = BaseT (StringT m)) tys ⇒
    EVERY (λv. ∃s. v = StringV s) vs
Proof
  Induct >> rw[LIST_REL_CONS1] >> gvs[] >>
  first_x_assum drule >> (impl_tac >- simp[]) >> simp[] >>
  gvs[evaluate_type_def, LET_THM, AllCaseEqs()] >>
  Cases_on `h` >> gvs[value_has_type_def]
QED

(* Bridge: fresh-stack LIST_REL interface to combined form used by helpers *)
Theorem LIST_REL_value_has_type_imp_combined[local]:
  !tvs vs ts tenv.
    LIST_REL value_has_type tvs vs ∧
    MAP (evaluate_type tenv) ts = MAP SOME tvs ⇒
    LIST_REL (λv t. ∃tyv. evaluate_type tenv t = SOME tyv ∧ value_has_type tyv v) vs ts
Proof
  Induct_on `ts` >> rpt strip_tac >- (Cases_on `tvs` >> Cases_on `vs` >> gvs[LIST_REL_NIL]) >>
  Cases_on `tvs` >> gvs[LIST_REL_NIL] >>
  gvs[LIST_REL_CONS1] >>
  first_x_assum (qspecl_then [`t`,`ys`] mp_tac) >> simp[]
QED

(* Helper: Concat with all-bytes typed values never produces TypeError *)
Theorem concat_no_type_error[local]:
  EVERY (λt. ∃bd. t = BaseT (BytesT bd)) ts ∧
  ty = BaseT (BytesT (Dynamic n)) ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧
  2 ≤ LENGTH vs ∧
  type_slot_size (BaseTV (BytesT (Dynamic n))) ≤
    115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ==>
  !msg. evaluate_builtin cx acc ty (Concat n) vs ≠ INR (TypeError msg)
Proof
  strip_tac >>
  drule LIST_REL_value_has_type_imp_combined >>
  disch_then (qspecl_then [`ts`,`get_tenv cx`] mp_tac) >> simp[] >>
  strip_tac >>
  `EVERY (λv. ∃bs. v = BytesV bs) vs` by
    (drule (REWRITE_RULE[AND_IMP_INTRO] list_rel_bytes_all_bytesv) >> simp[]) >>
  `2 ≤ LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  simp[evaluate_builtin_def, evaluate_concat_def] >>
  Cases_on `vs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[init_concat_output_def] >>
  irule evaluate_concat_loop_bytes_no_type_error >> gvs[EVERY_DEF]
QED

Theorem concat_string_no_type_error[local]:
  EVERY (λt. ∃m. t = BaseT (StringT m)) ts ∧
  ty = BaseT (StringT n) ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧
  2 ≤ LENGTH vs ∧
  type_slot_size (BaseTV (StringT n)) ≤
    115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ==>
  !msg. evaluate_builtin cx acc ty (Concat n) vs ≠ INR (TypeError msg)
Proof
  strip_tac >>
  drule LIST_REL_value_has_type_imp_combined >>
  disch_then (qspecl_then [`ts`,`get_tenv cx`] mp_tac) >> simp[] >>
  strip_tac >>
  `EVERY (λv. ∃s. v = StringV s) vs` by
    (drule (REWRITE_RULE[AND_IMP_INTRO] list_rel_string_all_stringv) >> simp[]) >>
  `2 ≤ LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  simp[evaluate_builtin_def, evaluate_concat_def] >>
  Cases_on `vs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[init_concat_output_def] >>
  irule evaluate_concat_loop_string_no_type_error >> gvs[EVERY_DEF]
QED

(* For BaseT types, evaluate_type returns BaseTV (when IS_SOME).
   This is stronger than evaluate_type_BaseT_cases which only says ∃btv. tv = BaseTV btv. *)
Theorem IS_SOME_cond[simp]:
  IS_SOME (if c then SOME x else NONE) <=> c
Proof
  Cases_on `c` >> simp[]
QED

Theorem evaluate_type_BaseT[local]:
  !tenv bt. IS_SOME (evaluate_type tenv (BaseT bt)) ==>
            evaluate_type tenv (BaseT bt) = SOME (BaseTV bt)
Proof
  gen_tac >> Cases_on `bt` >>
  rw[evaluate_type_def, LET_THM] >>
  Cases_on `b` >> gvs[evaluate_type_def, LET_THM]
QED

Theorem evaluate_type_BaseT_SOME[local]:
  !tenv bt tv. evaluate_type tenv (BaseT bt) = SOME tv ==> tv = BaseTV bt
Proof
  rpt strip_tac >> Cases_on `bt` >>
  gvs[evaluate_type_def, LET_THM] >>
  Cases_on `b` >> gvs[evaluate_type_def]
QED

Theorem evaluate_type_ArrayT_SOME[local]:
  !tenv t bd tv. evaluate_type tenv (ArrayT t bd) = SOME tv ==>
    ?tv'. tv = ArrayTV tv' bd ∧ evaluate_type tenv t = SOME tv'
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  simp[evaluate_type_def, LET_THM] >>
  CASE_TAC >> strip_tac >>
  Cases_on `0 < type_slot_size tv' ∧ type_slot_size (ArrayTV tv' bd) < dimword(:256)` >>
  gvs[] >>
  qexists_tac `tv'` >> simp[]
QED

(* HD (MAP f l) = f (HD l) when l ≠ [] *)
Theorem HD_MAP[local]:
  !f l. l ≠ [] ==> HD (MAP f l) = f (HD l)
Proof
  Cases_on `l` >> simp[]
QED

(* Boundary lemma: dest_NumV (IntV i) = SOME (Num i) when i >= 0.
   This avoids expanding dest_NumV_def (which has if i < 0 then NONE else SOME)
   into case splits that gvs/ARITH_TAC cannot close for integer contradictions. *)
Theorem dest_NumV_IntV_SOME[local,simp]:
  !i. 0 <= i ==> dest_NumV (IntV i) = SOME (Num i)
Proof
  rpt strip_tac >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  simp[dest_NumV_def]
QED

(* Boundary lemma: UintT values satisfy dest_NumV without producing NONE.
   This lets us resolve 'case dest_NumV sv of NONE => INR(TypeError) | SOME ... => ...'
   pattern in evaluate_slice_def for UintT 256 typed values. *)
Theorem value_has_type_UintT_imp_dest_NumV_SOME[local]:
  !n sv. value_has_type (BaseTV (UintT n)) sv ==>
    ?i. sv = IntV i ∧ 0 ≤ i ∧ dest_NumV sv = SOME (Num i)
Proof
  rpt strip_tac >>
  imp_res_tac vht_BaseTV_UintT >>
  gvs[]
QED

(* Boundary lemma: evaluate_slice on BytesV + IntV indices never produces TypeError.
   Concrete constructor args avoid case-explosion in consumer proofs.
   Proved at implementation level; consumers use irule without expanding evaluate_slice_def. *)
Theorem evaluate_slice_BytesV_no_type_error[local]:
  !bs i j n msg.
    0 ≤ i ∧ 0 ≤ j ==>
    evaluate_slice (BytesV bs) (IntV i) (IntV j) n ≠ INR (TypeError msg)
Proof
  rw[evaluate_slice_def, LET_THM] >>
  Cases_on `Num i + Num j ≤ LENGTH bs` >> gvs[] >>
  Cases_on `compatible_bound (Dynamic n) (Num j)` >> gvs[]
QED

(* Boundary lemma: evaluate_slice on StringV + IntV indices never produces TypeError. *)
Theorem evaluate_slice_StringV_no_type_error[local]:
  !s i j n msg.
    0 ≤ i ∧ 0 ≤ j ==>
    evaluate_slice (StringV s) (IntV i) (IntV j) n ≠ INR (TypeError msg)
Proof
  rw[evaluate_slice_def, LET_THM] >>
  Cases_on `Num i + Num j ≤ LENGTH s` >> gvs[] >>
  Cases_on `compatible_bound (Dynamic n) (Num j)` >> gvs[]
QED

(* Wrapper: evaluate_slice on BytesT-typed values never produces TypeError.
   Handles the Fixed/Dynamic case split internally. *)
Theorem evaluate_slice_BytesT_no_type_error[local]:
  !fv sv lv n msg bd.
    value_has_type (BaseTV (BytesT bd)) fv ∧
    value_has_type (BaseTV (UintT 256)) sv ∧
    value_has_type (BaseTV (UintT 256)) lv ⇒
    evaluate_slice fv sv lv n ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  Cases_on `bd` >-
  (* Fixed bytes *)
  (Cases_on `fv` >> gvs[vht_BaseTV_BytesT_Fixed] >>
   metis_tac[evaluate_slice_BytesV_no_type_error]) >>
  (* Dynamic bytes *)
  Cases_on `fv` >> gvs[vht_BaseTV_BytesT_Dynamic] >>
  metis_tac[evaluate_slice_BytesV_no_type_error]
QED

(* Wrapper: evaluate_slice on StringT-typed values never produces TypeError. *)
Theorem evaluate_slice_StringT_no_type_error[local]:
  !fv sv lv n msg m.
    value_has_type (BaseTV (StringT m)) fv ∧
    value_has_type (BaseTV (UintT 256)) sv ∧
    value_has_type (BaseTV (UintT 256)) lv ⇒
    evaluate_slice fv sv lv n ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  Cases_on `fv` >> gvs[vht_BaseTV_StringT] >>
  imp_res_tac vht_BaseTV_UintT >> gvs[] >>
  metis_tac[evaluate_slice_StringV_no_type_error]
QED

(* Helper: decompose a 3-element list into EL components *)
Theorem list_el_decomp_3[local]:
  !l. LENGTH l = 3 ==> l = [EL 0 l; EL 1 l; EL 2 l]
Proof
  gen_tac >> disch_tac >>
  Cases_on `l` >> fs[] >>
  Cases_on `t` >> fs[EL] >>
  Cases_on `t'` >> fs[EL]
QED

(* Success typing: evaluate_slice on BytesT-typed values returns bounded BytesV. *)
Theorem evaluate_slice_BytesT_success_type[local]:
  !fv sv lv n bd out.
    value_has_type (BaseTV (BytesT bd)) fv ∧
    value_has_type (BaseTV (UintT 256)) sv ∧
    value_has_type (BaseTV (UintT 256)) lv ∧
    evaluate_slice fv sv lv n = INL out ⇒
    ∃bs. out = BytesV bs ∧ LENGTH bs <= n
Proof
  rpt strip_tac >>
  Cases_on `bd` >-
   (Cases_on `fv` >> gvs[vht_BaseTV_BytesT_Fixed] >>
    imp_res_tac vht_BaseTV_UintT >> gvs[] >>
    gvs[evaluate_slice_def, LET_THM, compatible_bound_def,
        AllCaseEqs(), LENGTH_TAKE]) >>
  Cases_on `fv` >> gvs[vht_BaseTV_BytesT_Dynamic] >>
  imp_res_tac vht_BaseTV_UintT >> gvs[] >>
  gvs[evaluate_slice_def, LET_THM, compatible_bound_def,
      AllCaseEqs(), LENGTH_TAKE]
QED

(* Success typing: evaluate_slice on StringT-typed values returns bounded StringV. *)
Theorem evaluate_slice_StringT_success_type[local]:
  !fv sv lv n m out.
    value_has_type (BaseTV (StringT m)) fv ∧
    value_has_type (BaseTV (UintT 256)) sv ∧
    value_has_type (BaseTV (UintT 256)) lv ∧
    evaluate_slice fv sv lv n = INL out ⇒
    ∃s. out = StringV s ∧ LENGTH s <= n
Proof
  rpt strip_tac >>
  Cases_on `fv` >> gvs[vht_BaseTV_StringT] >>
  imp_res_tac vht_BaseTV_UintT >> gvs[] >>
  gvs[evaluate_slice_def, LET_THM, compatible_bound_def,
      AllCaseEqs(), LENGTH_TAKE]
QED

Theorem slice_bytes_builtin_success_type[local]:
  !bd tvs vs cx acc n v.
    [case bd of
       Fixed m => if m <= 32 then SOME (BaseTV (BytesT bd)) else NONE
     | Dynamic m =>
       if m < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
          type_slot_size (BaseTV (BytesT bd)) <=
          115792089237316195423570985008687907853269984665640564039457584007913129639936
       then SOME (BaseTV (BytesT bd)) else NONE;
     SOME (BaseTV (UintT 256)); SOME (BaseTV (UintT 256))] = MAP SOME tvs ∧
    LIST_REL value_has_type tvs vs ∧
    evaluate_builtin cx acc (BaseT (BytesT (Dynamic n))) (Slice n) vs = INL v ⇒
    ∃bs. v = BytesV bs ∧ LENGTH bs <= n
Proof
  rpt strip_tac >>
  `?tv0 tv1 tv2. tvs = [tv0; tv1; tv2]` by
    (Cases_on `tvs` >> gvs[] >>
     Cases_on `t` >> gvs[] >>
     Cases_on `t'` >> gvs[]) >>
  gvs[] >>
  Cases_on `bd` >> Cases_on `y` >>
  gvs[vht_BaseTV_BytesT_Fixed, vht_BaseTV_BytesT_Dynamic,
      evaluate_builtin_def, evaluate_slice_def, LET_THM,
      compatible_bound_def, AllCaseEqs(), LENGTH_TAKE]
QED

Theorem slice_string_builtin_success_type[local]:
  !m tvs vs cx acc n v.
    [if m < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
        type_slot_size (BaseTV (StringT m)) <=
        115792089237316195423570985008687907853269984665640564039457584007913129639936
     then SOME (BaseTV (StringT m)) else NONE;
     SOME (BaseTV (UintT 256)); SOME (BaseTV (UintT 256))] = MAP SOME tvs ∧
    LIST_REL value_has_type tvs vs ∧
    evaluate_builtin cx acc (BaseT (StringT n)) (Slice n) vs = INL v ⇒
    ∃s. v = StringV s ∧ LENGTH s <= n
Proof
  rpt strip_tac >>
  `?tv0 tv1 tv2. tvs = [tv0; tv1; tv2]` by
    (Cases_on `tvs` >> gvs[] >>
     Cases_on `t` >> gvs[] >>
     Cases_on `t'` >> gvs[]) >>
  gvs[] >>
  gvs[evaluate_builtin_def, evaluate_slice_def, LET_THM,
      compatible_bound_def, AllCaseEqs(), LENGTH_TAKE]
QED

(* Helper: Slice with well-typed BytesT values never produces TypeError *)
Theorem slice_no_type_error[local]:
  LENGTH ts = 3 ∧
  (?bd. HD ts = BaseT (BytesT bd)) ∧
  ty = BaseT (BytesT (Dynamic n)) ∧
  n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  type_slot_size (BaseTV (BytesT (Dynamic n))) ≤
    115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧
  EL 1 ts = BaseT (UintT 256) ∧ EL 2 ts = BaseT (UintT 256) ==>
  !msg. evaluate_builtin cx acc ty (Slice n) vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  imp_res_tac LIST_REL_LENGTH >>
  `LENGTH vs = 3` by metis_tac[LENGTH_MAP] >>
  `LENGTH tvs = 3` by gvs[LENGTH_MAP] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  Cases_on `t` >> gvs[LIST_REL_CONS1] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `ts` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  (* Resolve abstract type variables and rewrite evaluate_builtin in
     assumptions, but prevent vht_BaseTV_UintT from consuming value_has_type
     assumptions needed by evaluate_slice_BytesT_no_type_error *)
  imp_res_tac evaluate_type_BaseT_SOME >>
  fs[evaluate_builtin_def, Excl "vht_BaseTV_UintT"] >>
  metis_tac[evaluate_slice_BytesT_no_type_error]
QED

(* Helper: Slice with well-typed StringT values never produces TypeError *)
Theorem slice_string_no_type_error[local]:
  LENGTH ts = 3 ∧
  (?m. HD ts = BaseT (StringT m)) ∧
  ty = BaseT (StringT n) ∧
  n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  type_slot_size (BaseTV (StringT n)) ≤
    115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧
  EL 1 ts = BaseT (UintT 256) ∧ EL 2 ts = BaseT (UintT 256) ==>
  !msg. evaluate_builtin cx acc ty (Slice n) vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  imp_res_tac LIST_REL_LENGTH >>
  `LENGTH vs = 3` by metis_tac[LENGTH_MAP] >>
  `LENGTH tvs = 3` by gvs[LENGTH_MAP] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  Cases_on `t` >> gvs[LIST_REL_CONS1] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `ts` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  imp_res_tac evaluate_type_BaseT_SOME >>
  fs[evaluate_builtin_def, Excl "vht_BaseTV_UintT", Excl "vht_BaseTV_StringT"] >>
  metis_tac[evaluate_slice_StringT_no_type_error]
QED

(* Helper: MakeArray with well-typed args never produces TypeError *)
Theorem make_array_no_type_error[local]:
  well_typed_builtin_app ty (MakeArray o' bd) ts ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧ context_well_typed cx ∧
  accounts_well_typed acc ==>
  !msg. evaluate_builtin cx acc ty (MakeArray o' bd) vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  gvs[well_typed_builtin_app_def] >>
  Cases_on `o'`
  >- (* MakeArray NONE: INL result, trivially not TypeError *)
     gvs[evaluate_builtin_def]
  >> (* MakeArray (SOME x): need evaluate_type for elem type *)
     gvs[evaluate_builtin_def, well_typed_builtin_app_def] >>
     Cases_on `evaluate_type (get_tenv cx) x` >> gvs[]
     >- (* NONE: contradiction, ty=ArrayT x bd means evaluate_type exists *)
        gvs[evaluate_type_def, AllCaseEqs()]
QED

Theorem make_array_dispatch_no_type_error[local]:
  !ty o' bd ts cx tv tvs vs acc msg.
    well_typed_builtin_app ty (MakeArray o' bd) ts ∧
    MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
    evaluate_type (get_tenv cx) ty = SOME tv ∧
    LIST_REL value_has_type tvs vs ∧ context_well_typed cx ∧
    accounts_well_typed acc ==>
    evaluate_builtin cx acc ty (MakeArray o' bd) vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  drule_all make_array_no_type_error >>
  disch_then (qspec_then `msg` mp_tac) >>
  simp[]
QED

Theorem LIST_REL_every_same_type_EVERY_vht[local]:
  !vs arg_tys elem_ty tenv elem_tv.
    LIST_REL (λv t. ∃tyv. evaluate_type tenv t = SOME tyv ∧ value_has_type tyv v) vs arg_tys ∧
    EVERY ($= elem_ty) arg_tys ∧
    evaluate_type tenv elem_ty = SOME elem_tv ⇒
    EVERY (value_has_type elem_tv) vs
Proof
  Induct >> rw[LIST_REL_CONS1] >> gvs[] >>
  first_x_assum (qspecl_then [`t'`, `elem_ty`, `tenv`, `elem_tv`] mp_tac) >>
  simp[]
QED

Theorem SORTED_MAP_FST_enumerate_static_array[local]:
  !vs d n. SORTED $< (MAP FST (enumerate_static_array d n vs))
Proof
  Induct >> simp[enumerate_static_array_def, LET_THM] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  assume_tac arithmeticTheory.transitive_LESS >>
  simp[SORTED_EQ] >> rpt strip_tac >>
  gvs[MEM_MAP] >>
  rename1 `MEM kv (enumerate_static_array _ _ _)` >>
  Cases_on `kv` >> gvs[MEM_enumerate_static_array_iff]
QED

Theorem make_array_success_type[local]:
  well_typed_builtin_app ty (MakeArray o' bd) ts ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧
  evaluate_builtin cx acc ty (MakeArray o' bd) vs = INL v ==>
  value_has_type tv v
Proof
  rpt strip_tac >>
  drule LIST_REL_value_has_type_imp_combined >>
  disch_then (qspecl_then [`ts`, `get_tenv cx`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `o'` >> gvs[well_typed_builtin_app_def, evaluate_builtin_def]
  >- (drule evaluate_type_TupleT_cases >> strip_tac >> gvs[value_has_type_def] >>
      simp[values_have_types_LIST_REL] >>
      gvs[LIST_REL_EL_EQN, EL_MAP, EVERY_EL]) >>
  drule evaluate_type_ArrayT_SOME >> strip_tac >> gvs[] >>
  Cases_on `bd` >> gvs[make_array_value_def, value_has_type_def]
  >- (conj_tac >- (irule SORTED_MAP_FST_enumerate_static_array >> simp[]) >>
      ho_match_mp_tac sparse_has_type_enumerate >>
      conj_tac >- (irule LIST_REL_every_same_type_EVERY_vht >>
                   qexistsl [`ts`, `x`, `get_tenv cx`] >> simp[]) >>
      strip_tac >> gvs[compatible_bound_def] >>
      imp_res_tac LIST_REL_LENGTH >> simp[]) >>
  gvs[all_have_type_EVERY] >>
  conj_tac >- (imp_res_tac LIST_REL_LENGTH >> gvs[compatible_bound_def]) >>
  irule LIST_REL_every_same_type_EVERY_vht >>
  qexistsl [`ts`, `x`, `get_tenv cx`] >> simp[]
QED

Theorem addmod_no_type_error[local]:
  [SOME tv; SOME tv; SOME tv] = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) (BaseT (UintT 256)) = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc (BaseT (UintT 256)) AddMod vs <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  imp_res_tac evaluate_type_BaseT_SOME >>
  gvs[] >>
  Cases_on `tvs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[evaluate_builtin_def]
QED

Theorem mulmod_no_type_error[local]:
  [SOME tv; SOME tv; SOME tv] = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) (BaseT (UintT 256)) = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc (BaseT (UintT 256)) MulMod vs <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  imp_res_tac evaluate_type_BaseT_SOME >>
  gvs[] >>
  Cases_on `tvs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[evaluate_builtin_def]
QED

Theorem powmod256_no_type_error[local]:
  [SOME tv; SOME tv] = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) (BaseT (UintT 256)) = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc (BaseT (UintT 256)) PowMod256 vs <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  imp_res_tac evaluate_type_BaseT_SOME >>
  gvs[] >>
  Cases_on `tvs` >> gvs[] >>
  gvs[evaluate_builtin_def]
QED
Theorem addmod_success_type[local]:
  MAP SOME tvs = [SOME (BaseTV (UintT 256)); SOME (BaseTV (UintT 256)); SOME (BaseTV (UintT 256))] /\
  LIST_REL value_has_type tvs vs /\
  evaluate_builtin cx acc (BaseT (UintT 256)) AddMod vs = INL v ==>
  value_has_type (BaseTV (UintT 256)) v
Proof
  rpt strip_tac >>
  Cases_on `tvs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[value_has_type_def, evaluate_builtin_def] >>
  simp[] >>
  Cases_on `i'' = 0` >> gvs[] >>
  `0 < Num i''` by intLib.ARITH_TAC >>
  `((Num i + Num i') MOD Num i'') < Num i''` by simp[arithmeticTheory.MOD_LESS] >>
  intLib.ARITH_TAC
QED

Theorem mulmod_success_type[local]:
  MAP SOME tvs = [SOME (BaseTV (UintT 256)); SOME (BaseTV (UintT 256)); SOME (BaseTV (UintT 256))] /\
  LIST_REL value_has_type tvs vs /\
  evaluate_builtin cx acc (BaseT (UintT 256)) MulMod vs = INL v ==>
  value_has_type (BaseTV (UintT 256)) v
Proof
  rpt strip_tac >>
  Cases_on `tvs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[value_has_type_def, evaluate_builtin_def] >>
  simp[] >>
  Cases_on `i'' = 0` >> gvs[] >>
  `0 < Num i''` by intLib.ARITH_TAC >>
  `((Num i * Num i') MOD Num i'') < Num i''` by simp[arithmeticTheory.MOD_LESS] >>
  intLib.ARITH_TAC
QED

Theorem powmod256_success_type[local]:
  MAP SOME tvs = [SOME (BaseTV (UintT 256)); SOME (BaseTV (UintT 256))] /\
  LIST_REL value_has_type tvs vs /\
  evaluate_builtin cx acc (BaseT (UintT 256)) PowMod256 vs = INL v ==>
  value_has_type (BaseTV (UintT 256)) v
Proof
  rpt strip_tac >>
  Cases_on `tvs` >> gvs[] >>
  gvs[value_has_type_def, evaluate_builtin_def] >>
  simp[modexp_lt]
QED


(* Helper: ECRecover arg types imply ecrecover_arg_to_num returns SOME *)
Theorem ecrecover_arg_Uint256_not_none[local]:
  !v. value_has_type (BaseTV (UintT 256)) v ⇒ ecrecover_arg_to_num v ≠ NONE
Proof
  rpt strip_tac >> Cases_on `v` >> fs[value_has_type_def, ecrecover_arg_to_num_def]
QED

Theorem ecrecover_arg_BytesT32_not_none[local]:
  !v. value_has_type (BaseTV (BytesT (Fixed 32))) v ⇒ ecrecover_arg_to_num v ≠ NONE
Proof
  rpt strip_tac >> Cases_on `v` >> fs[value_has_type_def, ecrecover_arg_to_num_def]
QED

(* Boundary lemma: evaluate_ecrecover never produces TypeError when
   hash is 32 bytes and all arg converters return SOME *)
Theorem evaluate_ecrecover_no_type_error[local]:
  !hash_bytes v_arg r_arg s_arg msg.
    LENGTH hash_bytes = 32 ∧
    ecrecover_arg_to_num v_arg ≠ NONE ∧
    ecrecover_arg_to_num r_arg ≠ NONE ∧
    ecrecover_arg_to_num s_arg ≠ NONE ⇒
    evaluate_ecrecover [BytesV hash_bytes; v_arg; r_arg; s_arg] ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  Cases_on `ecrecover_arg_to_num v_arg` >- fs[] >>
  Cases_on `ecrecover_arg_to_num r_arg` >- fs[] >>
  Cases_on `ecrecover_arg_to_num s_arg` >- fs[] >>
  Cases_on `LENGTH hash_bytes = 32` >> fs[evaluate_ecrecover_def, AllCaseEqs()]
QED

(* Helper: decompose a 4-element list into EL components *)
Theorem list_el_decomp_4[local]:
  !l. LENGTH l = 4 ==> l = [EL 0 l; EL 1 l; EL 2 l; EL 3 l]
Proof
  gen_tac >> disch_tac >>
  Cases_on `l` >> fs[] >>
  Cases_on `t` >> fs[EL] >>
  Cases_on `t'` >> fs[EL] >>
  Cases_on `t''` >> fs[EL]
QED

Theorem ecrecover_value_list_no_type_error[local]:
  LENGTH vs = 4 ∧
  value_has_type (BaseTV (BytesT (Fixed 32))) (EL 0 vs) ∧
  (!i. 0 < i ∧ i < 4 ⇒
       value_has_type (BaseTV (UintT 256)) (EL i vs) ∨
       value_has_type (BaseTV (BytesT (Fixed 32))) (EL i vs)) ==>
  !msg. evaluate_builtin cx acc (BaseT AddressT) ECRecover vs <> INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  `ecrecover_arg_to_num (EL 1 vs) ≠ NONE` by (
    `value_has_type (BaseTV (UintT 256)) (EL 1 vs) ∨
     value_has_type (BaseTV (BytesT (Fixed 32))) (EL 1 vs)` by (
      qpat_assum `!i. 0 < i ∧ i < 4 ⇒ _` (qspec_then `1` mp_tac) >> simp[]) >>
    metis_tac[ecrecover_arg_Uint256_not_none, ecrecover_arg_BytesT32_not_none]) >>
  `ecrecover_arg_to_num (EL 2 vs) ≠ NONE` by (
    `value_has_type (BaseTV (UintT 256)) (EL 2 vs) ∨
     value_has_type (BaseTV (BytesT (Fixed 32))) (EL 2 vs)` by (
      qpat_assum `!i. 0 < i ∧ i < 4 ⇒ _` (qspec_then `2` mp_tac) >> simp[]) >>
    metis_tac[ecrecover_arg_Uint256_not_none, ecrecover_arg_BytesT32_not_none]) >>
  `ecrecover_arg_to_num (EL 3 vs) ≠ NONE` by (
    `value_has_type (BaseTV (UintT 256)) (EL 3 vs) ∨
     value_has_type (BaseTV (BytesT (Fixed 32))) (EL 3 vs)` by (
      qpat_assum `!i. 0 < i ∧ i < 4 ⇒ _` (qspec_then `3` mp_tac) >> simp[]) >>
    metis_tac[ecrecover_arg_Uint256_not_none, ecrecover_arg_BytesT32_not_none]) >>
  `?v0 v1 v2 v3. vs = [v0; v1; v2; v3]` by (
    map_every qexists [`EL 0 vs`, `EL 1 vs`, `EL 2 vs`, `EL 3 vs`] >>
    simp[list_el_decomp_4]) >>
  fs[EL] >>
  Cases_on `v0` >> fs[vht_BaseTV_BytesT_Fixed, evaluate_builtin_def] >>
  metis_tac[evaluate_ecrecover_no_type_error]
QED

Theorem evaluate_ecrecover_typed[local]:
  !vs v. evaluate_ecrecover vs = INL v ==> ?w. v = AddressV w
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = INL _` mp_tac >>
  Cases_on `vs` >> simp[evaluate_ecrecover_def] >>
  Cases_on `h` >> simp[evaluate_ecrecover_def] >>
  Cases_on `t` >> simp[evaluate_ecrecover_def] >>
  Cases_on `t'` >> simp[evaluate_ecrecover_def] >>
  Cases_on `t` >> simp[evaluate_ecrecover_def] >>
  Cases_on `t'` >> simp[evaluate_ecrecover_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ecrecover_success_type[local]:
  evaluate_builtin cx acc (BaseT AddressT) ECRecover vs = INL v ==>
  value_has_type (BaseTV AddressT) v
Proof
  rw[evaluate_builtin_def] >>
  imp_res_tac evaluate_ecrecover_typed >>
  gvs[value_has_type_def, LENGTH_word_to_bytes]
QED

(* Helper: decompose a 2-element list into EL components *)
Theorem list_el_decomp_2[local]:
  !l. LENGTH l = 2 ==> l = [EL 0 l; EL 1 l]
Proof
  gen_tac >> disch_tac >>
  Cases_on `l` >> fs[] >>
  Cases_on `t` >> fs[EL]
QED




(* Helper: ECRecover with well-typed args never produces TypeError.
   Uses extraction and runtime boundary lemmas; no fragile list destruct. *)
Theorem ecrecover_no_type_error[local]:
  LENGTH ts = 4 ∧ ty = BaseT AddressT ∧
  HD ts = BaseT (BytesT (Fixed 32)) ∧
  EVERY (λt. t = BaseT (UintT 256) ∨ t = BaseT (BytesT (Fixed 32))) (TL ts) ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty ECRecover vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  `LENGTH tvs = 4` by metis_tac[LENGTH_MAP, LIST_REL_LENGTH] >>
  `LENGTH vs = 4` by metis_tac[LIST_REL_LENGTH] >>
  fs[evaluate_builtin_def] >>
  (* Pre-derive per-element value typing facts *)
  `!i. i < 4:num ==> value_has_type (EL i tvs) (EL i vs)` by metis_tac[LIST_REL_EL_EQN] >>
  `!i. i < 4:num ==> evaluate_type (get_tenv cx) (EL i ts) = SOME (EL i tvs)` by (
    rpt strip_tac >> metis_tac[EL_MAP]) >>
  `EL 0 tvs = BaseTV (BytesT (Fixed 32))` by (
    `0 < 4:num` by decide_tac >>
    `evaluate_type (get_tenv cx) (EL 0 ts) = SOME (EL 0 tvs)` by metis_tac[] >>
    `EL 0 ts = HD ts` by simp[EL] >>
    metis_tac[evaluate_type_BaseT_SOME]) >>
  (* Remaining ts elements are Uint256 or BytesT32 *)
  `!i. 0 < i ∧ i < 4:num ⇒
    (EL i ts = BaseT (UintT 256) ∨ EL i ts = BaseT (BytesT (Fixed 32)))` by (
    rpt strip_tac >>
    `i - 1 < LENGTH (TL ts)` by (
      `LENGTH (TL ts) = 3` by (Cases_on `ts` >> fs[]) >> decide_tac) >>
    `EL (i - 1) (TL ts) = BaseT (UintT 256) ∨ EL (i - 1) (TL ts) = BaseT (BytesT (Fixed 32))` by (
      fs[EVERY_EL] >> first_assum (qspec_then `i - 1` mp_tac) >> simp[]) >>
    `EL i ts = EL (i - 1) (TL ts)` by (Cases_on `i` >> fs[EL]) >>
    metis_tac[]) >>
  (* So remaining tvs elements are BaseTV of Uint256 or BytesT32 *)
  `!i. 0 < i ∧ i < 4:num ⇒
    (EL i tvs = BaseTV (UintT 256) ∨ EL i tvs = BaseTV (BytesT (Fixed 32)))` by (
    rpt strip_tac >>
    `EL i ts = BaseT (UintT 256) ∨ EL i ts = BaseT (BytesT (Fixed 32))` by metis_tac[] >>
    Cases_on `EL i ts` >> fs[] >>
    `EL i tvs = BaseTV b` by (
      `evaluate_type (get_tenv cx) (BaseT b) = SOME (EL i tvs)` by metis_tac[] >>
      metis_tac[evaluate_type_BaseT_SOME]) >>
    metis_tac[]) >>
  (* Converter non-NONE for elements 1-3 *)
  `!i. 0 < i ∧ i < 4:num ⇒ ecrecover_arg_to_num (EL i vs) ≠ NONE` by (
    rpt strip_tac >>
    `value_has_type (EL i tvs) (EL i vs)` by (`i < 4:num` by decide_tac >> res_tac) >>
    `EL i tvs = BaseTV (UintT 256) ∨ EL i tvs = BaseTV (BytesT (Fixed 32))` by simp[] >>
    metis_tac[ecrecover_arg_Uint256_not_none, ecrecover_arg_BytesT32_not_none]) >>
  (* value_has_type for element 0: metis needs 0<4 explicitly since it can't do arithmetic *)
  `value_has_type (BaseTV (BytesT (Fixed 32))) (EL 0 vs)` by (
    `0 < 4:num` by decide_tac >>
    metis_tac[]) >>
  (* Derive specific converter non-NONE facts before list decomposition.
     After vs = [v0;v1;v2;v3], fs[EL] will simplify EL k vs to vk automatically. *)
  `ecrecover_arg_to_num (EL 1 vs) ≠ NONE` by (
    `0 < 1:num` by decide_tac >>
    `1 < 4:num` by decide_tac >>
    `value_has_type (EL 1 tvs) (EL 1 vs)` by metis_tac[] >>
    `EL 1 tvs = BaseTV (UintT 256) ∨ EL 1 tvs = BaseTV (BytesT (Fixed 32))` by metis_tac[] >>
    metis_tac[ecrecover_arg_Uint256_not_none, ecrecover_arg_BytesT32_not_none]) >>
  `ecrecover_arg_to_num (EL 2 vs) ≠ NONE` by (
    `0 < 2:num` by decide_tac >>
    `2 < 4:num` by decide_tac >>
    `value_has_type (EL 2 tvs) (EL 2 vs)` by metis_tac[] >>
    `EL 2 tvs = BaseTV (UintT 256) ∨ EL 2 tvs = BaseTV (BytesT (Fixed 32))` by metis_tac[] >>
    metis_tac[ecrecover_arg_Uint256_not_none, ecrecover_arg_BytesT32_not_none]) >>
  `ecrecover_arg_to_num (EL 3 vs) ≠ NONE` by (
    `0 < 3:num` by decide_tac >>
    `3 < 4:num` by decide_tac >>
    `value_has_type (EL 3 tvs) (EL 3 vs)` by metis_tac[] >>
    `EL 3 tvs = BaseTV (UintT 256) ∨ EL 3 tvs = BaseTV (BytesT (Fixed 32))` by metis_tac[] >>
    metis_tac[ecrecover_arg_Uint256_not_none, ecrecover_arg_BytesT32_not_none]) >>
  (* Remove assumptions that would conflict with list decomposition or fs[EL] *)
  qpat_x_assum `LIST_REL value_has_type tvs vs` kall_tac >>
  qpat_x_assum `MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `HD ts = _` kall_tac >>
  (* Decompose vs into 4 named elements using list_el_decomp_4 *)
  `?v0 v1 v2 v3. vs = [v0; v1; v2; v3]` by (
    map_every qexists [`EL 0 vs`, `EL 1 vs`, `EL 2 vs`, `EL 3 vs`] >>
    simp[list_el_decomp_4]) >>
  (* Simplify all EL references using concrete list positions *)
  fs[EL] >>
  Cases_on `v0` >> fs[vht_BaseTV_BytesT_Fixed] >>
  metis_tac[evaluate_ecrecover_no_type_error]
QED

Theorem ecrecover_dispatch_no_type_error[local]:
  (a = BaseT (UintT 256) ∨ a = BaseT (BytesT (Fixed 32))) ∧
  (b = BaseT (UintT 256) ∨ b = BaseT (BytesT (Fixed 32))) ∧
  (c = BaseT (UintT 256) ∨ c = BaseT (BytesT (Fixed 32))) ∧
  [evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed 32)));
   evaluate_type (get_tenv cx) a;
   evaluate_type (get_tenv cx) b;
   evaluate_type (get_tenv cx) c] = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc (BaseT AddressT) ECRecover vs <> INR (TypeError msg)
Proof
  strip_tac >> gvs[] >> gen_tac >>
  Cases_on `tvs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  irule ecrecover_value_list_no_type_error >>
  conj_tac >- (
    rpt strip_tac >>
    `i = 1 ∨ i = 2 ∨ i = 3` by decide_tac >>
    gvs[LIST_REL_EL_EQN, evaluate_type_def]) >>
  gvs[LIST_REL_EL_EQN, evaluate_type_def] >>
  rpt strip_tac >>
  rename1 `0 < j` >>
  `j = 1 ∨ j = 2 ∨ j = 3` by decide_tac >>
  gvs[]
QED


(* Boundary lemma: ALOOKUP into a sparse uint256[2] array yields an IntV value *)
Theorem ALOOKUP_sparse_uint256_is_IntV[local]:
  !l k v.
    ALOOKUP l k = SOME v ∧ k < 2 ∧
    sparse_has_type (BaseTV (UintT 256)) 2 l ⇒ ∃i. v = IntV i
Proof
  rpt strip_tac >>
  imp_res_tac ALOOKUP_sparse_has_type >>
  fs[vht_BaseTV_UintT]
QED

(* Boundary lemma: extract_ec_point succeeds on any typed uint256[2] value.
   Proof avoids gvs on the ≠ NONE goal; uses fs only on value_has_type assumptions
   and simp to expand extract_ec_point/array_index definitions. *)
Theorem extract_ec_point_uint256_2_not_none[local]:
  !v. value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v ⇒
      extract_ec_point v ≠ NONE
Proof
  rpt gen_tac >> strip_tac >>
  `∃av. v = ArrayV av` by metis_tac[vht_ArrayTV_exists] >>
  Cases_on `av` >> fs[value_has_type_def] >>
  (* Only SArrayV case survives *)
  simp[extract_ec_point_def, LET_THM, array_index_def, default_value_def] >>
  Cases_on `ALOOKUP l (0:num)` >> Cases_on `ALOOKUP l (1:num)` >>
  simp[CaseEq "option", CaseEq "value", vht_BaseTV_UintT] >>
  (* Remaining subgoals need ALOOKUP result = IntV, proven via sparse typing boundary *)
  TRY (
    `∃i. x = IntV i` by metis_tac[ALOOKUP_sparse_uint256_is_IntV, DECIDE ``0 < 2:num``] >>
    rw[]) >>
  TRY (
    `∃i. x = IntV i` by metis_tac[ALOOKUP_sparse_uint256_is_IntV, DECIDE ``1 < 2:num``] >>
    rw[]) >>
  TRY (
    `∃i. x' = IntV i` by metis_tac[ALOOKUP_sparse_uint256_is_IntV, DECIDE ``0 < 2:num``] >>
    rw[]) >>
  TRY (
    `∃i. x' = IntV i` by metis_tac[ALOOKUP_sparse_uint256_is_IntV, DECIDE ``1 < 2:num``] >>
    rw[])
QED

(* Helper: ECAdd with well-typed args never produces TypeError.
   Both args are ArrayV of uint256[2]. Uses extract_ec_point boundary lemma. *)
Theorem ecadd_no_type_error[local]:
  well_typed_builtin_app ty ECAdd ts ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧ context_well_typed cx ∧
  accounts_well_typed acc ==>
  !msg. evaluate_builtin cx acc ty ECAdd vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  gvs[well_typed_builtin_app_def] >>
  `LENGTH vs = 2` by metis_tac[LENGTH_MAP, LIST_REL_LENGTH] >>
  `LENGTH tvs = 2` by metis_tac[LENGTH_MAP, LIST_REL_LENGTH] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  Cases_on `t` >> gvs[LIST_REL_CONS1] >>
  (* Destruct ts to get concrete evaluate_type equations *)
  Cases_on `ts` >> gvs[] >>
  (* Now have evaluate_type (get_tenv cx) (ArrayT (BaseT (UintT 256)) (Fixed 2)) = SOME tv *)
  imp_res_tac evaluate_type_ArrayT_SOME >>
  imp_res_tac evaluate_type_BaseT_SOME >>
  fs[] >>
  `extract_ec_point h ≠ NONE` by metis_tac[extract_ec_point_uint256_2_not_none] >>
  `extract_ec_point h' ≠ NONE` by metis_tac[extract_ec_point_uint256_2_not_none] >>
  (* Move TypeError equation to goal and expand *)
  qpat_x_assum `_ = INR (TypeError msg)` mp_tac >>
  simp[evaluate_builtin_def, evaluate_ecadd_def] >>
  Cases_on `extract_ec_point h` >> gvs[] >>
  Cases_on `extract_ec_point h'` >> gvs[] >>
  Cases_on `x` >> Cases_on `x'` >> simp[] >>
  Cases_on `vfmExecution$ecadd (Num q,Num r) (Num q',Num r')` >> simp[]
QED

(* Helper: ECMul with well-typed args never produces TypeError *)
Theorem ecadd_dispatch_no_type_error[local]:
  [SOME tv; SOME tv] = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) (ArrayT (BaseT (UintT 256)) (Fixed 2)) = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd vs <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  Cases_on `tvs` >> gvs[] >>
  gvs[evaluate_type_def] >>
  `extract_ec_point y <> NONE` by metis_tac[extract_ec_point_uint256_2_not_none] >>
  `extract_ec_point y' <> NONE` by metis_tac[extract_ec_point_uint256_2_not_none] >>
  qpat_x_assum `_ = INR (TypeError msg)` mp_tac >>
  simp[evaluate_builtin_def, evaluate_ecadd_def] >>
  Cases_on `extract_ec_point y` >> gvs[] >>
  Cases_on `extract_ec_point y'` >> gvs[] >>
  Cases_on `x` >> Cases_on `x'` >> simp[] >>
  Cases_on `vfmExecution$ecadd (Num q,Num r) (Num q',Num r')` >> simp[]
QED

Theorem ecmul_no_type_error[local]:
  well_typed_builtin_app ty ECMul ts ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  LIST_REL value_has_type tvs vs ∧ context_well_typed cx ∧
  accounts_well_typed acc ==>
  !msg. evaluate_builtin cx acc ty ECMul vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  gvs[well_typed_builtin_app_def] >>
  `LENGTH vs = 2` by metis_tac[LENGTH_MAP, LIST_REL_LENGTH] >>
  `LENGTH tvs = 2` by metis_tac[LENGTH_MAP, LIST_REL_LENGTH] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1] >>
  Cases_on `t` >> gvs[LIST_REL_CONS1] >>
  (* Destruct ts to get concrete evaluate_type equations *)
  Cases_on `ts` >> gvs[] >>
  (* First arg is ArrayTV of uint256[2], second is BaseTV of uint256 *)
  imp_res_tac evaluate_type_ArrayT_SOME >>
  imp_res_tac evaluate_type_BaseT_SOME >>
  fs[] >>
  (* Derive extract_ec_point for first arg *)
  `extract_ec_point h ≠ NONE` by metis_tac[extract_ec_point_uint256_2_not_none] >>
  (* Move TypeError equation to goal, expand evaluator *)
  qpat_x_assum `_ = INR (TypeError msg)` mp_tac >>
  simp[evaluate_builtin_def] >>
  (* Now have evaluate_ecmul [h; IntV i] = INR (TypeError msg) as goal *)
  Cases_on `extract_ec_point h` >> gvs[] >>
  Cases_on `x` >> simp[evaluate_ecmul_def, LET_THM] >>
  Cases_on `vfmExecution$ecmul (Num q,Num r) (Num i)` >> simp[]
QED

Theorem ecmul_dispatch_no_type_error[local]:
  [SOME tv; evaluate_type (get_tenv cx) (BaseT (UintT 256))] = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) (ArrayT (BaseT (UintT 256)) (Fixed 2)) = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul vs <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  Cases_on `tvs` >> gvs[] >>
  gvs[evaluate_type_def] >>
  `extract_ec_point y <> NONE` by metis_tac[extract_ec_point_uint256_2_not_none] >>
  qpat_x_assum `_ = INR (TypeError msg)` mp_tac >>
  simp[evaluate_builtin_def] >>
  Cases_on `extract_ec_point y` >> gvs[] >>
  Cases_on `x` >> simp[evaluate_ecmul_def, LET_THM] >>
  Cases_on `vfmExecution$ecmul (Num q,Num r) (Num i)` >> simp[]
QED

Theorem bn254p_pos[local]:
   0 < bn254$bn254p
Proof
  EVAL_TAC
QED

Theorem bn254p_lt_2_256[local]:
   bn254$bn254p < 2 ** 256
Proof
  EVAL_TAC
QED

Theorem fmul_bounded[local]:
  !x y. bn254$fmul x y < bn254$bn254p
Proof
  simp[bn254Theory.fmul_def, MOD_LESS, bn254p_pos]
QED

Theorem fadd_bounded[local]:
  !x y. bn254$fadd x y < bn254$bn254p
Proof
  simp[bn254Theory.fadd_def, MOD_LESS, bn254p_pos]
QED

Theorem fsub_bounded[local]:
  !x y. x < bn254$bn254p /\ y < bn254$bn254p ==>
         bn254$fsub x y < bn254$bn254p
Proof
  rpt strip_tac >> simp[bn254Theory.fsub_def] >>
  IF_CASES_TAC >> simp[MOD_LESS, bn254p_pos]
QED

Definition fp_bounded_def:
  fp_bounded (x:num, y:num, z:num) <=> x < bn254$bn254p /\ y < bn254$bn254p /\ z < bn254$bn254p
End

Theorem add_bounded[local]:
  !p1 p2. fp_bounded (bn254$add p1 p2)
Proof
  rpt gen_tac >> PairCases_on `p1` >> PairCases_on `p2` >>
  simp[fp_bounded_def, bn254Theory.add_def, LET_THM] >>
  `!a b. a < bn254$bn254p /\ b < bn254$bn254p ==>
         bn254$fsub a b < bn254$bn254p` by simp[fsub_bounded] >>
  simp[fmul_bounded, fadd_bounded]
QED

Theorem dbl_bounded[local]:
  !p. fp_bounded (bn254$dbl p)
Proof
  gen_tac >> PairCases_on `p` >>
  simp[fp_bounded_def, bn254Theory.dbl_def, LET_THM] >>
  `!a b. a < bn254$bn254p /\ b < bn254$bn254p ==>
         bn254$fsub a b < bn254$bn254p` by simp[fsub_bounded] >>
  simp[fmul_bounded, fadd_bounded]
QED

Theorem mul_loop_bounded[local]:
  !a p n. fp_bounded a ==> fp_bounded (bn254$mul_loop a p n)
Proof
  ho_match_mp_tac bn254Theory.mul_loop_ind >> rpt strip_tac >>
  once_rewrite_tac[bn254Theory.mul_loop_def] >>
  IF_CASES_TAC >> simp[LET_THM] >>
  first_x_assum irule >>
  simp[dbl_bounded] >> IF_CASES_TAC >> simp[add_bounded]
QED

Theorem zero_bounded[local]:
   fp_bounded bn254$zero
Proof
  EVAL_TAC
QED

Theorem mul_bounded[local]:
  !p n. fp_bounded p ==> fp_bounded (bn254$mul p n)
Proof
  rpt strip_tac >> simp[bn254Theory.mul_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[zero_bounded, mul_loop_bounded]
QED

Theorem fromAffine_bounded[local]:
  !x y. x < bn254$bn254p /\ y < bn254$bn254p ==>
    fp_bounded (bn254$fromAffine (x, y))
Proof
  rpt strip_tac >> simp[bn254Theory.fromAffine_def, LET_THM] >>
  IF_CASES_TAC >> simp[zero_bounded, fp_bounded_def, bn254p_pos]
QED

Theorem toAffine_bounded[local]:
  !p. fp_bounded p ==>
    FST (bn254$toAffine p) < bn254$bn254p /\
    SND (bn254$toAffine p) < bn254$bn254p
Proof
  rpt strip_tac >> PairCases_on `p` >> gvs[fp_bounded_def] >>
  simp[bn254Theory.toAffine_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[fmul_bounded]
QED

Theorem lt_bn254p_lt_2_256[local]:
  !n. n < bn254$bn254p ==> n < 2 ** 256
Proof
  rpt strip_tac >> irule LESS_TRANS >> qexists `bn254$bn254p` >>
  rewrite_tac[bn254p_lt_2_256] >> simp[]
QED

Theorem addAffine_bounded[local]:
  !a b. FST (bn254$addAffine a b) < 2 ** 256 /\
        SND (bn254$addAffine a b) < 2 ** 256
Proof
  rpt gen_tac >>
  `fp_bounded (bn254$add (bn254$fromAffine a) (bn254$fromAffine b))`
    by simp[add_bounded] >>
  `FST (bn254$toAffine (bn254$add (bn254$fromAffine a) (bn254$fromAffine b))) < bn254$bn254p /\
   SND (bn254$toAffine (bn254$add (bn254$fromAffine a) (bn254$fromAffine b))) < bn254$bn254p`
    by (irule toAffine_bounded >> simp[]) >>
  rewrite_tac[bn254Theory.addAffine_def] >>
  conj_tac >> irule lt_bn254p_lt_2_256 >> simp[]
QED

Theorem mulAffine_bounded[local]:
  !a n. FST a < bn254$bn254p /\ SND a < bn254$bn254p ==>
        FST (bn254$mulAffine a n) < 2 ** 256 /\
        SND (bn254$mulAffine a n) < 2 ** 256
Proof
  rpt gen_tac >> PairCases_on `a` >> strip_tac >>
  `fp_bounded (bn254$fromAffine (a0, a1))` by simp[fromAffine_bounded] >>
  `fp_bounded (bn254$mul (bn254$fromAffine (a0, a1)) n)` by simp[mul_bounded] >>
  `FST (bn254$toAffine (bn254$mul (bn254$fromAffine (a0, a1)) n)) < bn254$bn254p /\
   SND (bn254$toAffine (bn254$mul (bn254$fromAffine (a0, a1)) n)) < bn254$bn254p`
    by (irule toAffine_bounded >> simp[]) >>
  rewrite_tac[bn254Theory.mulAffine_def] >>
  conj_tac >> irule lt_bn254p_lt_2_256 >>
  fs[bn254Theory.validAffine_def]
QED

Theorem mk_ec_result_well_typed[local]:
  !p. FST p < 2 ** 256 /\ SND p < 2 ** 256 ==>
    value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
                   (mk_ec_result p)
Proof
  Cases >> rpt strip_tac >>
  rewrite_tac[mk_ec_result_def, make_array_value_def] >>
  once_rewrite_tac[value_has_type_def] >>
  conj_tac >- simp[SORTED_MAP_FST_enumerate_static_array] >>
  irule sparse_has_type_enumerate >>
  fs[default_value_def, value_has_type_def]
QED

Theorem evaluate_ecadd_well_typed[local]:
  !vs v. evaluate_ecadd vs = INL v ==>
    value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v
Proof
  rpt strip_tac >> qpat_x_assum `_ = INL _` mp_tac >>
  Cases_on `vs` >> simp[evaluate_ecadd_def] >>
  Cases_on `t` >> simp[evaluate_ecadd_def] >>
  Cases_on `t'` >> simp[evaluate_ecadd_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[]
  >- (irule mk_ec_result_well_typed >> simp[]) >>
  gvs[vfmExecutionTheory.ecadd_def, AllCaseEqs()] >>
  irule mk_ec_result_well_typed >> simp[addAffine_bounded]
QED

Theorem evaluate_ecmul_well_typed[local]:
  !vs v. evaluate_ecmul vs = INL v ==>
    value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v
Proof
  rpt strip_tac >> qpat_x_assum `_ = INL _` mp_tac >>
  Cases_on `vs` >> simp[evaluate_ecmul_def] >>
  Cases_on `t` >> simp[evaluate_ecmul_def] >>
  Cases_on `h'` >> simp[evaluate_ecmul_def] >>
  Cases_on `t'` >> simp[evaluate_ecmul_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[]
  >- (irule mk_ec_result_well_typed >> simp[]) >>
  gvs[vfmExecutionTheory.ecmul_def, AllCaseEqs()] >>
  irule mk_ec_result_well_typed >>
  irule mulAffine_bounded >>
  fs[bn254Theory.validAffine_def]
QED

Theorem ecadd_success_type[local]:
  evaluate_builtin cx acc (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd vs = INL v ==>
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v
Proof
  rw[evaluate_builtin_def] >>
  imp_res_tac evaluate_ecadd_well_typed >> gvs[]
QED

Theorem ecmul_success_type[local]:
  evaluate_builtin cx acc (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul vs = INL v ==>
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v
Proof
  rw[evaluate_builtin_def] >>
  imp_res_tac evaluate_ecmul_well_typed >> gvs[]
QED


(* Helper: Not with bool type — no TypeError possible *)
Theorem bool_not_no_type_error[local]:
  is_bool_type ty ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  value_has_type tv v ==>
  !msg. evaluate_builtin cx acc ty Not [v] ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `is_bool_type _` mp_tac >>
  REWRITE_TAC[is_bool_type_inv] >> strip_tac >>
  gvs[] >>
  imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
  simp[evaluate_builtin_def]
QED

(* Helper: Not with uint type — no TypeError possible *)
Theorem uint_not_no_type_error[local]:
  is_uint_type ty ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  value_has_type tv v ==>
  !msg. evaluate_builtin cx acc ty Not [v] ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `is_uint_type _` mp_tac >>
  REWRITE_TAC[is_uint_type_def] >> strip_tac >>
  gvs[] >>
  imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
  simp[evaluate_builtin_def, type_to_int_bound_def, is_Unsigned_def] >>
  intLib.ARITH_TAC
QED

(* Helper: Uint Not result stays in the same unsigned range. *)
Theorem uint_not_result_bound[local]:
  0 ≤ i ∧ Num i < 2 ** n ==>
  0 ≤ (&(2 ** n):int) - 1 - i ∧ Num ((&(2 ** n):int) - 1 - i) < 2 ** n
Proof
  rpt strip_tac >>
  `i < (&(2 ** n):int)` by (
    `0 ≤ (&(2 ** n):int)` by simp[] >>
    fs[GSYM integerTheory.NUM_LT, integerTheory.NUM_OF_INT]) >>
  `0 ≤ (&(2 ** n):int) - 1 - i ∧ (&(2 ** n):int) - 1 - i < (&(2 ** n):int)`
    by intLib.ARITH_TAC >>
  `Num ((&(2 ** n):int) - 1 - i) < Num (&(2 ** n):int)` by (
    irule vyperArithTheory.Num_int_lt >> simp[]) >>
  pop_assum mp_tac >> simp[integerTheory.NUM_OF_INT]
QED

(* Helper: Not with bool type preserves the statically computed result type. *)
Theorem bool_not_success_type[local]:
  is_bool_type ty ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  value_has_type tv v ∧
  evaluate_builtin cx acc ty Not [v] = INL out ==>
  value_has_type tv out
Proof
  strip_tac >>
  qpat_x_assum `is_bool_type _` mp_tac >>
  REWRITE_TAC[is_bool_type_inv] >> strip_tac >>
  gvs[evaluate_type_def, value_has_type_def, evaluate_builtin_def]
QED

(* Helper: Not with uint type preserves the statically computed result type. *)
Theorem uint_not_success_type[local]:
  is_uint_type ty ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  value_has_type tv v ∧
  evaluate_builtin cx acc ty Not [v] = INL out ==>
  value_has_type tv out
Proof
  strip_tac >>
  qpat_x_assum `is_uint_type _` mp_tac >>
  REWRITE_TAC[is_uint_type_def] >> strip_tac >>
  gvs[] >>
  imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
  gvs[evaluate_builtin_def, type_to_int_bound_def, is_Unsigned_def] >>
  metis_tac[uint_not_result_bound]
QED

(* Helper: Not with flag type preserves the statically computed result type. *)
Theorem flag_Not_success_type[local]:
  context_well_typed cx ∧
  evaluate_type (get_tenv cx) (FlagT fid) = SOME tv ∧
  value_has_type tv y ∧
  evaluate_builtin cx acc (FlagT fid) Not [y] = INL out ==>
  value_has_type tv out
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  gvs[value_has_type_def, evaluate_type_def, evaluate_builtin_def] >>
  rewrite_tac[wordsTheory.WORD_NEG_1, GSYM wordsTheory.WORD_NOT_0] >>
  simp[w2n_and_low_mask_lt]
QED

(* Helper: Neg never returns TypeError *)
Theorem neg_no_type_error[local]:
  is_numeric_type ty ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  value_has_type tv v ==>
  !msg. evaluate_builtin cx acc ty Neg [v] ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `is_numeric_type _` mp_tac >>
  REWRITE_TAC[is_numeric_type_inv] >>
  strip_tac >- (
    qpat_x_assum `is_int_type _` mp_tac >>
    REWRITE_TAC[is_int_type_inv] >> strip_tac >>
    gvs[] >>
    imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
    simp[evaluate_builtin_def, type_to_int_bound_def, bounded_int_op_def] >>
    rw[] >>
    NO_TAC) >>
  TRY (
    gvs[] >>
    imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
    simp[evaluate_builtin_def, type_to_int_bound_def, bounded_int_op_def] >> NO_TAC) >>
  gvs[] >>
  imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
  simp[evaluate_builtin_def, bounded_decimal_op_def]
QED

(* Helper: Keccak256 with bytes or string input *)
Theorem keccak256_no_type_error[local]:
  is_bytes_or_string_type (HD ts) ∧
  ty = BaseT (BytesT (Fixed 32)) ∧
  LENGTH ts = 1 ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty Keccak256 vs ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  `LENGTH vs = 1` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `LENGTH tvs = 1` by metis_tac[LENGTH_MAP] >>
  Cases_on `vs` >> fs[LIST_REL_CONS1] >>
  Cases_on `ts` >> fs[] >>
  qpat_x_assum `is_bytes_or_string_type _` mp_tac >>
  REWRITE_TAC[is_bytes_or_string_type_inv] >> strip_tac >>
  TRY (
    (* BytesT branch *)
    first_x_assum strip_assume_tac >>
    gvs[] >> imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
    Cases_on `bd` >> gvs[evaluate_type_def, LET_THM] >>
    simp[evaluate_builtin_def] >> NO_TAC) >>
  (* StringT branch *)
  first_x_assum strip_assume_tac >>
  gvs[] >> imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
  gvs[evaluate_type_def] >>
  simp[evaluate_builtin_def]
QED

(* Helper: Sha256 with bytes or string input *)
Theorem sha256_no_type_error[local]:
  is_bytes_or_string_type (HD ts) ∧
  ty = BaseT (BytesT (Fixed 32)) ∧
  LENGTH ts = 1 ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty Sha256 vs ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  `LENGTH vs = 1` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `LENGTH tvs = 1` by metis_tac[LENGTH_MAP] >>
  Cases_on `vs` >> fs[LIST_REL_CONS1] >>
  Cases_on `ts` >> fs[] >>
  qpat_x_assum `is_bytes_or_string_type _` mp_tac >>
  REWRITE_TAC[is_bytes_or_string_type_inv] >> strip_tac >>
  TRY (
    (* BytesT branch *)
    first_x_assum strip_assume_tac >>
    gvs[] >> imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
    Cases_on `bd` >> gvs[evaluate_type_def, LET_THM] >>
    simp[evaluate_builtin_def] >> NO_TAC) >>
  (* StringT branch *)
  first_x_assum strip_assume_tac >>
  gvs[] >> imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
  gvs[evaluate_type_def] >>
  simp[evaluate_builtin_def]
QED

(* Helper: AsWeiValue with uint input *)
Theorem as_wei_value_no_type_error[local]:
  is_uint_type (HD ts) ∧
  ty = BaseT (UintT 256) ∧
  LENGTH ts = 1 ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty (AsWeiValue dn) vs ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  `LENGTH vs = 1` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  Cases_on `vs` >> gvs[LIST_REL_CONS1, is_uint_type_inv] >>
  first_x_assum strip_assume_tac >>
  gvs[evaluate_type_def] >>
  imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
  gvs[value_has_type_def] >>
  simp[evaluate_builtin_def, evaluate_as_wei_value_def, LET_THM] >>
  Cases_on `dn` >> simp[within_int_bound_def] >> intLib.ARITH_TAC
QED

(* Helper: Concat with bytes inputs — after gvs splits the well_typed_builtin_app disjunction *)
Theorem concat_bytes_no_type_error[local]:
  2 ≤ LENGTH ts ∧ ty = BaseT (BytesT (Dynamic n)) ∧
  EVERY (λt. ∃bd. t = BaseT (BytesT bd)) ts ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty (Concat n) vs ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  drule LIST_REL_value_has_type_imp_combined >>
  disch_then (qspecl_then [`ts`, `get_tenv cx`] mp_tac) >> simp[] >>
  strip_tac >>
  `EVERY (λv. ∃bs. v = BytesV bs) vs` by
    (drule (REWRITE_RULE[AND_IMP_INTRO] list_rel_bytes_all_bytesv) >> simp[]) >>
  `2 ≤ LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  simp[evaluate_builtin_def, evaluate_concat_def] >>
  Cases_on `vs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[init_concat_output_def] >>
  irule evaluate_concat_loop_bytes_no_type_error >> gvs[EVERY_DEF]
QED

Theorem concat_bytes_dispatch_no_type_error[local]:
  !ts cx n tvs tv vs acc msg.
  2 ≤ LENGTH ts ∧
  EVERY (λt. ∃bd. t = BaseT (BytesT bd)) ts ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  evaluate_builtin cx acc (BaseT (BytesT (Dynamic n))) (Concat n) vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  drule LIST_REL_value_has_type_imp_combined >>
  disch_then (qspecl_then [`ts`, `get_tenv cx`] mp_tac) >> simp[] >>
  strip_tac >>
  `EVERY (λv. ∃bs. v = BytesV bs) vs` by
    (drule (REWRITE_RULE[AND_IMP_INTRO] list_rel_bytes_all_bytesv) >> simp[]) >>
  `2 ≤ LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  simp[evaluate_builtin_def, evaluate_concat_def] >>
  Cases_on `vs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[init_concat_output_def] >>
  qpat_x_assum `evaluate_builtin _ _ _ _ _ = INR (TypeError msg)` mp_tac >>
  simp[evaluate_builtin_def, evaluate_concat_def, init_concat_output_def,
       evaluate_concat_loop_bytes_no_type_error]
QED

Theorem concat_string_builtin_no_type_error[local]:
  2 ≤ LENGTH ts ∧ ty = BaseT (StringT n) ∧
  EVERY (λt. ∃m. t = BaseT (StringT m)) ts ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty (Concat n) vs ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  drule LIST_REL_value_has_type_imp_combined >>
  disch_then (qspecl_then [`ts`, `get_tenv cx`] mp_tac) >> simp[] >>
  strip_tac >>
  `EVERY (λv. ∃s. v = StringV s) vs` by
    (drule (REWRITE_RULE[AND_IMP_INTRO] list_rel_string_all_stringv) >> simp[]) >>
  `2 ≤ LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  simp[evaluate_builtin_def, evaluate_concat_def] >>
  Cases_on `vs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[init_concat_output_def] >>
  irule evaluate_concat_loop_string_no_type_error >> gvs[EVERY_DEF]
QED

Theorem concat_string_dispatch_no_type_error[local]:
  !ts cx n tvs tv vs acc msg.
  2 ≤ LENGTH ts ∧
  EVERY (λt. ∃m. t = BaseT (StringT m)) ts ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) (BaseT (StringT n)) = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  evaluate_builtin cx acc (BaseT (StringT n)) (Concat n) vs ≠ INR (TypeError msg)
Proof
  rpt strip_tac >>
  drule LIST_REL_value_has_type_imp_combined >>
  disch_then (qspecl_then [`ts`, `get_tenv cx`] mp_tac) >> simp[] >>
  strip_tac >>
  `EVERY (λv. ∃s. v = StringV s) vs` by
    (drule (REWRITE_RULE[AND_IMP_INTRO] list_rel_string_all_stringv) >> simp[]) >>
  `2 ≤ LENGTH vs` by metis_tac[LIST_REL_LENGTH] >>
  simp[evaluate_builtin_def, evaluate_concat_def] >>
  Cases_on `vs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[init_concat_output_def] >>
  qpat_x_assum `evaluate_builtin _ _ _ _ _ = INR (TypeError msg)` mp_tac >>
  simp[evaluate_builtin_def, evaluate_concat_def, init_concat_output_def,
       evaluate_concat_loop_string_no_type_error]
QED

(* Helper: Slice with bytes input — wraps existing slice_no_type_error *)
Theorem slice_bytes_no_type_error[local]:
  LENGTH ts = 3 ∧ EL 1 ts = BaseT (UintT 256) ∧ EL 2 ts = BaseT (UintT 256) ∧
  ty = BaseT (BytesT (Dynamic n)) ∧ (?bd. HD ts = BaseT (BytesT bd)) ∧
  n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  type_slot_size (BaseTV (BytesT (Dynamic n))) ≤
    115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty (Slice n) vs ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  irule slice_no_type_error >> gvs[] >>
  qexistsl [`ts`, `tvs`] >> gvs[] >>
  imp_res_tac LIST_REL_LENGTH >> fs[evaluate_type_def, LET_THM] >> gvs[]
QED

Theorem slice_bytes_dispatch_no_type_error[local]:
  !cx n bd tvs tv vs acc msg.
    MAP (evaluate_type (get_tenv cx))
        [BaseT (BytesT bd); BaseT (UintT 256); BaseT (UintT 256)] = MAP SOME tvs ∧
    evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME tv ∧
    LIST_REL value_has_type tvs vs ==>
    evaluate_builtin cx acc (BaseT (BytesT (Dynamic n))) (Slice n) vs ≠ INR (TypeError msg)
Proof
  rpt gen_tac >> strip_tac >>
  irule slice_bytes_no_type_error >>
  gvs[evaluate_type_def, LET_THM] >>
  qexistsl [`[BaseT (BytesT bd); BaseT (UintT 256); BaseT (UintT 256)]`, `tvs`] >>
  gvs[evaluate_type_def, LET_THM]
QED

(* Helper: Slice with string input — wraps existing slice_string_no_type_error *)
Theorem slice_string_builtin_no_type_error[local]:
  LENGTH ts = 3 ∧ EL 1 ts = BaseT (UintT 256) ∧ EL 2 ts = BaseT (UintT 256) ∧
  ty = BaseT (StringT n) ∧ (?m. HD ts = BaseT (StringT m)) ∧
  n < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  type_slot_size (BaseTV (StringT n)) ≤
    115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ==>
  !msg. evaluate_builtin cx acc ty (Slice n) vs ≠ INR (TypeError msg)
Proof
  strip_tac >> gen_tac >>
  irule slice_string_no_type_error >> gvs[] >>
  qexistsl [`ts`, `tvs`] >> gvs[] >>
  imp_res_tac LIST_REL_LENGTH >> fs[evaluate_type_def, LET_THM] >> gvs[]
QED

Theorem slice_string_dispatch_no_type_error[local]:
  !cx n m tvs tv vs acc msg.
    MAP (evaluate_type (get_tenv cx))
        [BaseT (StringT m); BaseT (UintT 256); BaseT (UintT 256)] = MAP SOME tvs ∧
    evaluate_type (get_tenv cx) (BaseT (StringT n)) = SOME tv ∧
    LIST_REL value_has_type tvs vs ==>
    evaluate_builtin cx acc (BaseT (StringT n)) (Slice n) vs ≠ INR (TypeError msg)
Proof
  rpt gen_tac >> strip_tac >>
  irule slice_string_builtin_no_type_error >>
  gvs[evaluate_type_def, LET_THM] >>
  qexistsl [`[BaseT (StringT m); BaseT (UintT 256); BaseT (UintT 256)]`, `tvs`] >>
  gvs[evaluate_type_def, LET_THM]
QED

Theorem evaluate_block_hash_no_type_error[local,simp]:
  !txn n msg. evaluate_block_hash txn n <> INR (TypeError msg)
Proof
  rw[evaluate_block_hash_def, LET_THM]
QED

Theorem LENGTH_word_to_bytes_be_32[local,simp]:
  !w:bytes32. LENGTH (word_to_bytes_be w) = 32
Proof
  simp[word_to_bytes_be_def, LENGTH_word_to_bytes]
QED

Theorem evaluate_block_hash_success_type[local]:
  evaluate_block_hash txn n = INL v ==>
  ?bs. v = BytesV bs /\ LENGTH bs = 32
Proof
  rw[evaluate_block_hash_def, LET_THM]
QED

Theorem blockhash_success_type[local]:
  evaluate_builtin cx acc (BaseT (BytesT (Fixed 32))) BlockHash [IntV i] = INL v ==>
  ?bs. v = BytesV bs /\ LENGTH bs = 32
Proof
  rw[evaluate_builtin_def] >>
  imp_res_tac evaluate_block_hash_success_type >> gvs[]
QED

Theorem blobhash_success_type[local]:
  evaluate_builtin cx acc (BaseT (BytesT (Fixed 32))) BlobHash [IntV i] = INL v ==>
  ?bs. v = BytesV bs /\ LENGTH bs = 32
Proof
  rw[evaluate_builtin_def, evaluate_blob_hash_def]
QED

Theorem acc_builtin_success_type[local]:
  evaluate_type (get_tenv cx) (account_item_type item) = SOME tv /\
  LENGTH bs = 20 /\
  accounts_well_typed acc /\
  evaluate_builtin cx acc (account_item_type item) (Acc item) [BytesV bs] = INL v ==>
  value_has_type tv v
Proof
  rpt strip_tac >>
  `value_has_type (BaseTV AddressT) (BytesV bs)` by simp[value_has_type_def] >>
  drule_all Acc_builtin_sound >>
  disch_then (qspec_then `cx` strip_assume_tac) >> gvs[]
QED
Theorem methodid_success_type[local]:
  evaluate_builtin cx acc (BaseT (BytesT (Fixed 4))) MethodId [arg] = INL v ==>
  ?bs. v = BytesV bs /\ LENGTH bs = 4
Proof
  rpt strip_tac >>
  Cases_on `arg` >>
  gvs[evaluate_builtin_def, LENGTH_TAKE, LENGTH_Keccak_256_w64]
QED


Theorem blockhash_no_type_error[local]:
  evaluate_type (get_tenv cx) (BaseT (UintT 256)) = SOME arg_tv ∧
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed 32))) = SOME ret_tv ∧
  value_has_type arg_tv y ==>
  evaluate_builtin cx acc (BaseT (BytesT (Fixed 32))) BlockHash [y] <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  imp_res_tac evaluate_type_BaseT_SOME >>
  gvs[evaluate_builtin_def]
QED

Theorem well_typed_builtin_app_no_type_error:
  well_typed_builtin_app ty blt ts ∧ blt ≠ Len ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ∧ context_well_typed cx ∧ accounts_well_typed acc ∧
  (!item. blt = Env item ==> item ≠ MsgGas) ==>
  !msg. evaluate_builtin cx acc ty blt vs <> INR (TypeError msg)
Proof
  strip_tac >>
  Cases_on `blt` >>
  gvs[well_typed_builtin_app_def, LET_THM,
      LENGTH_EQ_NUM_compute,
      Excl "is_int_type_def", Excl "is_numeric_type_def", Excl "is_bool_type_def",
      Excl "is_flag_type_def", Excl "is_comparable_type_def",
      Excl "is_bytes_or_string_type_def",
      is_int_type_inv, is_numeric_type_inv, is_bool_type_inv,
      is_flag_type_inv, is_comparable_type_inv,
      is_bytes_or_string_type_inv] >>
  gen_tac >>
  (* Bop: delegate to well_typed_binop_no_type_error *)
  TRY (metis_tac[well_typed_builtin_bop_no_type_error] >> NO_TAC) >>
  (* Not: delegate to bool_not/uint_not/flag_Not helpers *)
  TRY (irule bool_not_no_type_error >> gvs[] >> NO_TAC) >>
  TRY (irule uint_not_no_type_error >> gvs[] >> NO_TAC) >>
  TRY (irule flag_Not_no_type_error >> gvs[] >> NO_TAC) >>
  (* Neg: delegate to neg_no_type_error *)
  TRY (irule neg_no_type_error >> gvs[] >> NO_TAC) >>
  (* Keccak256 *)
  TRY (irule keccak256_no_type_error >> gvs[] >> NO_TAC) >>
  (* Sha256 *)
  TRY (irule sha256_no_type_error >> gvs[] >> NO_TAC) >>
  (* Direct one-argument hash/simple cases whose list structure has already been simplified *)
  TRY (rename1 `evaluate_type _ (BaseT (BytesT bd)) = SOME _` >>
       Cases_on `bd` >> imp_res_tac evaluate_type_BaseT_SOME >>
       gvs[evaluate_type_def, LET_THM] >> simp[evaluate_builtin_def] >> NO_TAC) >>
  TRY (imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
       simp[evaluate_builtin_def] >> NO_TAC) >>
  (* AsWeiValue *)
  TRY (imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
       gvs[value_has_type_def] >>
       simp[evaluate_builtin_def, evaluate_as_wei_value_def, LET_THM] >>
       Cases_on `d` >> simp[within_int_bound_def] >> intLib.ARITH_TAC >> NO_TAC) >>
  TRY (irule as_wei_value_no_type_error >> gvs[] >> NO_TAC) >>
  (* Concat: bytes or string — try both *)
  TRY (unabbrev_all_tac >>
       qspecl_then [`ts`, `cx`, `n`, `tvs`, `tv`, `vs`, `acc`, `msg`] mp_tac
         concat_bytes_dispatch_no_type_error >>
       simp[] >> NO_TAC) >>
  TRY (unabbrev_all_tac >>
       qspecl_then [`ts`, `cx`, `n`, `tvs`, `tv`, `vs`, `acc`, `msg`] mp_tac
         concat_string_dispatch_no_type_error >>
       simp[] >> NO_TAC) >>
  TRY (irule concat_bytes_no_type_error >> gvs[] >> NO_TAC) >>
  TRY (irule concat_string_builtin_no_type_error >> gvs[] >> NO_TAC) >>
  (* Slice: bytes or string — try both *)
  TRY (qspecl_then [`cx`, `n`, `bd`, `tvs`, `tv`, `vs`, `acc`, `msg`] mp_tac
         slice_bytes_dispatch_no_type_error >>
       simp[] >> NO_TAC) >>
  TRY (qspecl_then [`cx`, `n`, `m`, `tvs`, `tv`, `vs`, `acc`, `msg`] mp_tac
         slice_string_dispatch_no_type_error >>
       simp[] >> NO_TAC) >>
  TRY (irule slice_bytes_no_type_error >> gvs[] >> NO_TAC) >>
  TRY (irule slice_string_builtin_no_type_error >> gvs[] >> NO_TAC) >>
  (* MakeArray *)
  TRY (qspecl_then [`ty`, `o'`, `b`, `ts`, `cx`, `tv`, `tvs`, `vs`, `acc`, `msg`] mp_tac
         make_array_dispatch_no_type_error >>
       simp[] >> NO_TAC) >>
  TRY (irule make_array_no_type_error >> gvs[] >> NO_TAC) >>
  (* AddMod *)
  TRY (mp_tac addmod_no_type_error >> simp[] >> NO_TAC) >>
  (* MulMod *)
  TRY (mp_tac mulmod_no_type_error >> simp[] >> NO_TAC) >>
  (* PowMod256 *)
  TRY (mp_tac powmod256_no_type_error >> simp[] >> NO_TAC) >>
  (* ECRecover *)
  TRY (metis_tac[ecrecover_dispatch_no_type_error] >> NO_TAC) >>
  (* ECAdd *)
  TRY (metis_tac[ecadd_dispatch_no_type_error] >> NO_TAC) >>
  TRY (irule ecadd_no_type_error >> gvs[] >> NO_TAC) >>
  (* ECMul *)
  TRY (metis_tac[ecmul_dispatch_no_type_error] >> NO_TAC) >>
  TRY (irule ecmul_no_type_error >> gvs[] >> NO_TAC) >>
  (* Env *)
  TRY (irule Env_builtin_no_type_error >> gvs[] >> NO_TAC) >>
  (* Acc *)
  TRY (drule_all Acc_builtin_sound >> rw[] >> NO_TAC) >>
  (* Simple builtins: resolve types/values then expand evaluate_builtin_def *)
  TRY (imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
       Cases_on `v` >> gvs[value_has_type_def] >>
       simp[evaluate_builtin_def] >> NO_TAC) >>
  TRY (imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
       Cases_on `v` >> gvs[value_has_type_def] >>
       Cases_on `b` >> gvs[] >>
       Cases_on `v'` >> gvs[value_has_type_def] >>
       simp[evaluate_builtin_def] >> NO_TAC) >>
  TRY (imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
       Cases_on `v` >> gvs[value_has_type_def] >>
       Cases_on `v'` >> gvs[value_has_type_def] >>
       simp[evaluate_builtin_def] >> NO_TAC) >>
  TRY (imp_res_tac evaluate_type_BaseT_SOME >> gvs[] >>
       Cases_on `v` >> gvs[value_has_type_def] >>
       Cases_on `v'` >> gvs[value_has_type_def] >>
       Cases_on `v''` >> gvs[value_has_type_def] >>
       simp[evaluate_builtin_def] >> NO_TAC) >>
  (* Abs *)
  gvs[evaluate_type_def] >>
  rw[evaluate_builtin_def, type_to_int_bound_def]
QED

(* Builtin success-type theorem: well-typed inputs produce well-typed outputs *)
Theorem well_typed_builtin_app_success_type:
  well_typed_builtin_app ty blt ts ∧ blt ≠ Len ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) ty = SOME tv ∧
  LIST_REL value_has_type tvs vs ∧ context_well_typed cx ∧ accounts_well_typed acc ∧
  evaluate_builtin cx acc ty blt vs = INL v ==>
  value_has_type tv v
Proof
  strip_tac >> Cases_on `blt` >>
  gvs[well_typed_builtin_app_def, LET_THM,
      LENGTH_EQ_NUM_compute,
      Excl "is_int_type_def", Excl "is_numeric_type_def", Excl "is_bool_type_def",
      Excl "is_flag_type_def", Excl "is_comparable_type_def",
      Excl "is_bytes_or_string_type_def",
      is_int_type_inv, is_numeric_type_inv, is_bool_type_inv,
      is_flag_type_inv, is_comparable_type_inv,
      is_bytes_or_string_type_inv] >>
  (* Phase 2: resolve type values *)
  gvs[evaluate_type_def] >>
    TRY (rename1 `evaluate_builtin _ _ (BaseT BoolT) Not [BoolV b] = INL v` >>
       gvs[evaluate_builtin_def, value_has_type_def] >>
       qexists_tac `¬b` >> gvs[] >> NO_TAC) >>
  TRY (rename1 `evaluate_builtin _ _ (BaseT (UintT n)) Not [IntV i] = INL v` >>
       gvs[evaluate_builtin_def, type_to_int_bound_def, is_Unsigned_def,
           int_bound_bits_def] >>
       gvs[] >> fs [evaluate_builtin_def] >>EVAL_TAC  >> gvs [bounded_int_op_def, type_to_int_bound_def,within_int_bound_def ] >> rw [type_to_int_bound_def,uint_not_result_bound,within_int_bound_def,bounded_int_op_def] >>   NO_TAC) >>
  
  TRY (rename1 `evaluate_builtin _ _ (FlagT fid) Not [_] = INL _` >>
       Cases_on `FLOOKUP (get_tenv cx) (type_key fid)` >> gvs[] >>
       Cases_on `x` >> gvs[] >>
       gvs[value_has_type_def, evaluate_builtin_def, evaluate_type_def] >>
       rewrite_tac[wordsTheory.WORD_NEG_1, GSYM wordsTheory.WORD_NOT_0] >>
       simp[w2n_and_low_mask_lt] >> NO_TAC)
    >> TRY (rename1 `evaluate_builtin _ _ _ Neg [_] = INL _` >>
   gvs[evaluate_builtin_def, type_to_int_bound_def] >>
   pop_assum mp_tac >> rw[] >>
   imp_res_tac bounded_decimal_op_INL >> gvs[] >>
   imp_res_tac bounded_int_op_INL >> gvs[within_int_bound_def] >> NO_TAC)
  
  (* Hash builtins return fixed 32-byte values. *)
  >> TRY (rename1 `evaluate_builtin _ _ _ Keccak256 [arg] = INL _` >>
       Cases_on `arg` >>
       gvs[evaluate_builtin_def, value_has_type_def, LENGTH_Keccak_256_w64] >>
       NO_TAC) >>
  TRY (rename1 `evaluate_builtin _ _ _ Sha256 [arg] = INL _` >>
       Cases_on `arg` >>
       gvs[evaluate_builtin_def, value_has_type_def, LENGTH_word_to_bytes] >>
       NO_TAC) >>
  (* AsWeiValue returns Uint256 on successful evaluation by construction. *)
  TRY (rename1 `evaluate_builtin _ _ _ (AsWeiValue d) [_] = INL _` >>
       gvs[evaluate_builtin_def, evaluate_as_wei_value_def, LET_THM,
           value_has_type_def, within_int_bound_def, AllCaseEqs()] >>
       NO_TAC) >>
  (* Concat success preserves the dynamic bytes/string bound. *)
  TRY (rename1 `EVERY (λt. ∃bd. t = BaseT (BytesT bd)) ts` >>
       rename1 `evaluate_builtin _ _ _ (Concat n) vs = INL v` >>
       drule LIST_REL_value_has_type_imp_combined >>
       disch_then (qspecl_then [`ts`, `get_tenv cx`] mp_tac) >> simp[] >> strip_tac >>
       `EVERY (λv. ∃bs. v = BytesV bs) vs` by
         (drule (REWRITE_RULE[AND_IMP_INTRO] list_rel_bytes_all_bytesv) >> simp[]) >>
       gvs[evaluate_builtin_def, evaluate_concat_def] >>
       Cases_on `vs` >> gvs[] >>
       Cases_on `t` >> gvs[] >>
       gvs[init_concat_output_def] >>
       imp_res_tac evaluate_concat_loop_bytes_success_type >> gvs[] >> NO_TAC) >>
  TRY (rename1 `EVERY (λt. ∃m. t = BaseT (StringT m)) ts` >>
       rename1 `evaluate_builtin _ _ _ (Concat n) vs = INL v` >>
       drule LIST_REL_value_has_type_imp_combined >>
       disch_then (qspecl_then [`ts`, `get_tenv cx`] mp_tac) >> simp[] >> strip_tac >>
       `EVERY (λv. ∃s. v = StringV s) vs` by
         (drule (REWRITE_RULE[AND_IMP_INTRO] list_rel_string_all_stringv) >> simp[]) >>
       gvs[evaluate_builtin_def, evaluate_concat_def] >>
       Cases_on `vs` >> gvs[] >>
       Cases_on `t` >> gvs[] >>
       gvs[init_concat_output_def] >>
       imp_res_tac evaluate_concat_loop_string_success_type >> gvs[] >> NO_TAC) >>
  (* Slice success preserves the dynamic bytes/string bound. *)
  TRY (rename1 `evaluate_builtin _ _ (BaseT (BytesT (Dynamic n))) (Slice n) vs = INL v` >>
       metis_tac[slice_bytes_builtin_success_type] >> NO_TAC) >>
  TRY (rename1 `evaluate_builtin _ _ (BaseT (StringT n)) (Slice n) vs = INL v` >>
       metis_tac[slice_string_builtin_success_type] >> NO_TAC) >>
  (* MakeArray success produces the tuple/array value requested by the static rule. *)
  TRY (rename1 `evaluate_builtin _ _ ty (MakeArray o' b) vs = INL v` >>
       metis_tac[make_array_success_type] >> NO_TAC) >>
  (* Uint2Str success returns a string within the statically required bound. *)
  TRY (rename1 `evaluate_builtin _ _ (BaseT (StringT n)) (Uint2Str n) [IntV i] = INL v` >>
       gvs[evaluate_builtin_def, compatible_bound_def] >>
       `STRLEN (toString (Num i)) <= 78` by
         (irule uint2str_strlen_bound >>
          qexists `BaseTV (UintT k)` >>
          gvs[value_has_type_def, well_formed_type_value_def]) >>
       gvs[] >> NO_TAC) >>
  (* Floor/Ceil success returns Int256 by the decimal division bounds. *)
  TRY (rename1 `evaluate_builtin _ _ (BaseT (IntT 256)) Ceil [DecimalV d] = INL v` >>
       metis_tac[ceil_builtin_success_type] >> NO_TAC) >>
  TRY (rename1 `evaluate_builtin _ _ (BaseT (IntT 256)) Floor [DecimalV d] = INL v` >>
       metis_tac[floor_builtin_success_type] >> NO_TAC) >>
  (* Modular arithmetic builtins return Uint256 results. *)
  TRY (rename1 `evaluate_builtin _ _ (BaseT (UintT 256)) AddMod vs = INL v` >>
       `value_has_type (BaseTV (UintT 256)) v` by
         metis_tac[addmod_success_type] >>
       gvs[value_has_type_def] >> NO_TAC) >>
  TRY (rename1 `evaluate_builtin _ _ (BaseT (UintT 256)) MulMod vs = INL v` >>
       `value_has_type (BaseTV (UintT 256)) v` by
         metis_tac[mulmod_success_type] >>
       gvs[value_has_type_def] >> NO_TAC) >>
  TRY (rename1 `evaluate_builtin _ _ (BaseT (UintT 256)) PowMod256 vs = INL v` >>
       `value_has_type (BaseTV (UintT 256)) v` by
         metis_tac[powmod256_success_type] >>
       gvs[value_has_type_def] >> NO_TAC) >>
  (* BlockHash/BlobHash success returns fixed bytes32 values. *)
  TRY (rename1 `evaluate_builtin _ _ (BaseT (BytesT (Fixed 32))) BlockHash [IntV i] = INL v` >>
       metis_tac[blockhash_success_type] >> NO_TAC) >>
  TRY (rename1 `evaluate_builtin _ _ (BaseT (BytesT (Fixed 32))) BlobHash [IntV i] = INL v` >>
       metis_tac[blobhash_success_type] >> NO_TAC) >>
  (* Phase 3: resolve builtin execution + related defs *)
  TRY (gvs[evaluate_builtin_def, type_to_int_bound_def,
           int_bound_bits_def, is_Unsigned_def, LET_THM] >> NO_TAC) >>
  (* INL inversions for bounded/wrapped ops *)
  TRY (imp_res_tac bounded_int_op_INL >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac bounded_decimal_op_INL >> gvs[] >> NO_TAC) >>
  TRY (
    `0 < int_bound_bits u` by (Cases_on `u` >> simp[int_bound_bits_def] >> intLib.ARITH_TAC) >>
    imp_res_tac wrapped_int_op_INL >> gvs[] >> NO_TAC) >>
  (* Crypto/bytes length lemmas *)
  TRY (gvs[LENGTH_Keccak_256_w64] >> NO_TAC) >>
  (* AsWeiValue: expand and use within_int_bound + evaluate_as_wei_value *)
  TRY (gvs[evaluate_as_wei_value_def, LET_THM] >> NO_TAC) >>
  (* Bop: delegate to the binary-operation boundary helper. *)
  TRY (rename1 `evaluate_builtin _ _ ty (Bop b) vs = INL v` >>
       metis_tac[builtin_bop_success_type] >> NO_TAC) >>
  (* Env: delegate to Env_builtin_success_type *)
  TRY (metis_tac[Env_builtin_success_type] >> NO_TAC) >>
  (* Acc: delegate to account builtin success helper. *)
  TRY (rename1 `evaluate_builtin _ _ (account_item_type a) (Acc a) [BytesV bs] = INL v` >>
       metis_tac[acc_builtin_success_type] >> NO_TAC) >>
  (* MethodId returns fixed bytes4. *)
  TRY (rename1 `evaluate_builtin _ _ (BaseT (BytesT (Fixed 4))) MethodId [arg] = INL v` >>
       metis_tac[methodid_success_type] >> NO_TAC) >>~
  (* MethodId returns dynamic Bytes[4]. *)
  [`evaluate_builtin _ _ (BaseT (BytesT (Dynamic 4))) MethodId [arg] = INL v`]
  >- (Cases_on `arg` >> gvs[evaluate_builtin_def, LENGTH_TAKE_EQ])
  >- (Cases_on `arg` >> gvs[evaluate_builtin_def, LENGTH_TAKE_EQ]) >>
  (* ECRecover returns an address on success. *)
  TRY (rename1 `evaluate_builtin _ _ (BaseT AddressT) ECRecover vs = INL v` >>
       `value_has_type (BaseTV AddressT) v` by metis_tac[ecrecover_success_type] >>
       gvs[value_has_type_def] >> NO_TAC) >>
  (* ECAdd/ECMul return uint256[2] arrays on success. *)
  TRY (rename1 `evaluate_builtin _ _ (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd vs = INL v` >>
       metis_tac[ecadd_success_type] >> NO_TAC) >>
  TRY (rename1 `evaluate_builtin _ _ (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul vs = INL v` >>
       metis_tac[ecmul_success_type] >> NO_TAC) >>
  (* Flag bitwise not: use w2n_and_low_mask_lt *)
  TRY (gvs[w2n_and_low_mask_lt] >> NO_TAC)
  (* Abs *)
  >>~ [`evaluate_builtin _ _ _ Abs _`] >- (
    gvs[evaluate_builtin_def, type_to_int_bound_def,
        bounded_int_op_def] ) >>
  (* Arithmetic cleanup *)
  intLib.ARITH_TAC
QED

Theorem return_INL_value[local]:
  return x st = (INL y, st') ==> y = x
Proof
  simp[vyperStateTheory.return_def, pairTheory.PAIR_EQ, sumTheory.INL_11]
QED

Theorem Len_result_fits_uint256:
  well_typed_builtin_app ty Len [arg_ty] ∧
  evaluate_type tenv arg_ty = SOME arg_runtime_tv ∧
  well_formed_type_value arg_runtime_tv ∧
  toplevel_value_typed arg_tv arg_runtime_tv ∧
  toplevel_array_length cx arg_tv st = (INL n, st') ==>
  n < dimword(:256)
Proof
  strip_tac >> gvs[well_typed_builtin_app_def] >>
  Cases_on `arg_ty` >> gvs[is_sized_type_def, evaluate_type_def]
  >- (
    rename1 `BaseT bt` >> Cases_on `bt` >>
    gvs[is_sized_type_def, evaluate_type_def, AllCaseEqs(), LET_THM]
    >- (
      rename1 `StringT max` >>
      Cases_on `arg_tv` >>
      gvs[toplevel_value_typed_def, oneline toplevel_array_length_def,
          raise_def, value_has_type_def, AllCaseEqs(), bind_def,
          get_storage_backend_def, get_accounts_def, value_CASE_rator,
          get_transient_storage_def] >>
      drule return_INL_value >> strip_tac >> gvs[] >>
      irule LESS_EQ_LESS_TRANS >>
      qexists `max` >> simp[]) >>
    gvs[evaluate_type_def, compatible_bound_def, AllCaseEqs(), LET_THM] >>
    Cases_on `arg_tv` >>
    gvs[toplevel_value_typed_def, oneline toplevel_array_length_def,
        return_def, raise_def, value_has_type_def, AllCaseEqs(), bind_def,
        get_storage_backend_def, get_accounts_def, get_transient_storage_def,
        value_CASE_rator] >>
    TRY (drule return_INL_value >> strip_tac >> gvs[] >> decide_tac >> NO_TAC) >>
    gvs[well_formed_type_value_def]
  ) >>
  gvs[AllCaseEqs()] >>
  Cases_on `arg_tv` >>
  gvs[toplevel_value_typed_def, oneline toplevel_array_length_def, return_def,
      raise_def, value_has_type_def, AllCaseEqs(), bind_def,
      ignore_bind_def, value_CASE_rator, array_value_CASE_rator,
      get_storage_backend_def, get_accounts_def, get_transient_storage_def,
      well_formed_type_value_def, type_slot_size_def] >>
  qmatch_asmsub_rename_tac`ArrayTV _ bd` >> Cases_on`bd` >>
  gvs[value_has_type_def, vyperStateTheory.return_def, type_slot_size_def]
  >- (
    qmatch_asmsub_rename_tac`sparse_has_type tv len sparse` >>
    qmatch_assum_abbrev_tac`len * slot < bound` >>
    `LENGTH sparse <= len` by metis_tac[sparse_has_type_length] >>
    `len <= len * slot` by gvs[] >>
    irule LESS_EQ_LESS_TRANS >>
    qexists `len` >> simp[] >>
    irule LESS_EQ_LESS_TRANS >>
    qexists `len * slot` >> simp[Abbr`bound`]
  ) >>
  gvs[vyperStateTheory.bind_def, AllCaseEqs(), vyperStateTheory.return_def] >>
  TRY (drule return_INL_value >> strip_tac >> gvs[] >>
       qmatch_assum_abbrev_tac`len * slot < bound` >>
       `len <= len * slot` by gvs[] >>
       irule LESS_EQ_LESS_TRANS >>
       qexists `len * slot` >> simp[Abbr`bound`] >> NO_TAC) >>
  TRY (qmatch_assum_abbrev_tac`n * slot < bound` >>
       `n <= n * slot` by gvs[] >>
       irule LESS_EQ_LESS_TRANS >>
       qexists `n * slot` >> simp[Abbr`bound`] >> NO_TAC) >>
  TRY (qmatch_asmsub_abbrev_tac`w2n w` >>
       Q.ISPEC_THEN`w`mp_tac w2n_lt >> simp[] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac`w2n w` >>
  Q.ISPEC_THEN`w`mp_tac w2n_lt >>
  simp[]
QED

Theorem Len_toplevel_array_length_no_type_error:
  well_typed_builtin_app ty Len [arg_ty] ∧
  evaluate_type tenv arg_ty = SOME arg_runtime_tv ∧
  well_formed_type_value arg_runtime_tv ∧
  toplevel_value_typed arg_tv arg_runtime_tv ∧
  toplevel_array_length cx arg_tv st = (INR (Error (TypeError err)), st') ==>
  F
Proof
  strip_tac >> gvs[well_typed_builtin_app_def] >>
  Cases_on `arg_ty` >> gvs[is_sized_type_def, evaluate_type_def]
  >- (
    rename1 `BaseT bt` >> Cases_on `bt` >>
    gvs[is_sized_type_def, evaluate_type_def, AllCaseEqs(), LET_THM]
    >- (
      Cases_on `arg_tv` >>
      gvs[toplevel_value_typed_def, oneline toplevel_array_length_def,
          vyperStateTheory.return_def, raise_def, value_has_type_def,
          AllCaseEqs(), bind_def, get_storage_backend_def, get_accounts_def,
          value_CASE_rator, get_transient_storage_def]) >>
    gvs[evaluate_type_def, compatible_bound_def, AllCaseEqs(), LET_THM] >>
    Cases_on `arg_tv` >>
    gvs[toplevel_value_typed_def, oneline toplevel_array_length_def,
        vyperStateTheory.return_def, raise_def, value_has_type_def,
        AllCaseEqs(), bind_def, get_storage_backend_def, get_accounts_def,
        get_transient_storage_def, value_CASE_rator, well_formed_type_value_def]
  ) >>
  gvs[AllCaseEqs()] >>
  Cases_on `arg_tv` >>
  gvs[toplevel_value_typed_def, oneline toplevel_array_length_def,
      vyperStateTheory.return_def, raise_def, value_has_type_def, AllCaseEqs(),
      bind_def, ignore_bind_def, value_CASE_rator, array_value_CASE_rator,
      get_storage_backend_def, get_accounts_def, get_transient_storage_def,
      well_formed_type_value_def, type_slot_size_def] >>
  Cases_on `b` >>
  gvs[vyperStateTheory.return_def, bind_def, bind_apply, get_storage_backend_def,
      vyperStateTheory.get_transient_storage_def, vyperStateTheory.get_accounts_def] >>
  Cases_on `b'` >>
  gvs[vyperStateTheory.return_def, bind_def, bind_apply, get_storage_backend_def,
      vyperStateTheory.get_transient_storage_def, vyperStateTheory.get_accounts_def]
QED

Theorem Len_builtin_sound:
  well_typed_builtin_app ty Len [arg_ty] ∧
  evaluate_type tenv ty = SOME tv ∧ evaluate_type tenv arg_ty = SOME arg_runtime_tv ∧
  toplevel_value_typed arg_tv arg_runtime_tv ∧
  toplevel_array_length cx arg_tv st = (INL n, st') ==>
  value_has_type tv (IntV (&n))
Proof
  strip_tac >>
  `well_formed_type_value arg_runtime_tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  `n < dimword(:256)` by (drule_all Len_result_fits_uint256 >> simp[]) >>
  gvs[well_typed_builtin_app_def, evaluate_type_def, value_has_type_def]
QED

(* ===== Type builtins ===== *)

Theorem typed_bytes_value_is_BytesV[local]:
  evaluate_type tenv (BaseT (BytesT bd)) = SOME tv ∧ value_has_type tv v ==>
  ∃bs. v = BytesV bs
Proof
  rpt strip_tac >>
  Cases_on `bd` >> gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem typed_int_value_is_IntV[local]:
  is_int_type ty ∧ evaluate_type tenv ty = SOME tv ∧ value_has_type tv v ==>
  ∃i. v = IntV i
Proof
  rpt strip_tac >>
  qpat_x_assum `is_int_type _` mp_tac >>
  rewrite_tac[is_int_type_inv] >> strip_tac >>
  gvs[evaluate_type_def]
QED

Theorem extract32_bool_not_well_typed_type_builtin_args[local]:
  ¬ well_typed_type_builtin_args Extract32 (BaseT BoolT)
      [BaseT (BytesT (Fixed 32)); BaseT (UintT 256)]
Proof
  simp[well_typed_type_builtin_args_def, extract32_result_base_ok_def]
QED

Theorem evaluate_extract32_supported_no_type_error[local]:
  extract32_result_base_ok bt ∧
  evaluate_type (get_tenv cx) (BaseT (BytesT bd)) = SOME bytes_tv ∧
  value_has_type bytes_tv bytes_v ∧
  is_int_type idx_ty ∧
  evaluate_type (get_tenv cx) idx_ty = SOME idx_tv ∧
  value_has_type idx_tv idx_v ==>
  evaluate_type_builtin cx Extract32 (BaseT bt) [bytes_v; idx_v] <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  drule_all typed_bytes_value_is_BytesV >> strip_tac >> gvs[] >>
  drule_all typed_int_value_is_IntV >> strip_tac >> gvs[] >>
  Cases_on `bt` >>
  gvs[extract32_result_base_ok_def, evaluate_type_builtin_def,
      evaluate_extract32_def, evaluate_convert_def, AllCaseEqs(), LET_THM]
QED

Theorem evaluate_abi_decode_no_type_error[local]:
  evaluate_type (get_tenv cx) (BaseT (BytesT bd)) = SOME bytes_tv ∧
  value_has_type bytes_tv bytes_v ==>
  evaluate_type_builtin cx (AbiDecode b) result_ty [bytes_v] <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  drule_all typed_bytes_value_is_BytesV >> strip_tac >> gvs[] >>
  gvs[evaluate_type_builtin_def, AllCaseEqs(), LET_THM]
QED

Theorem well_typed_type_builtin_args_length:
  well_typed_type_builtin_args tb target_ty ts ==> type_builtin_args_length_ok tb (LENGTH ts)
Proof
  simp[oneline well_typed_type_builtin_args_def] >>
  CASE_TAC >> rw[type_builtin_args_length_ok_def] >>
  Cases_on`ts` >> gvs[]
QED

Theorem evaluate_convert_no_type_error[local]:
  valid_conversion from_ty to_ty /\
  evaluate_type (get_tenv cx) from_ty = SOME from_tv /\
  evaluate_type (get_tenv cx) to_ty = SOME to_tv /\
  value_has_type from_tv v ==>
  !msg. evaluate_convert (get_tenv cx) v to_ty <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  `evaluate_type_builtin cx Convert to_ty [v] <> INR (TypeError msg)`
    by (drule_all valid_conversion_no_type_error >> simp[]) >>
  fs[Once evaluate_type_builtin_def]
QED

Theorem well_typed_type_builtin_no_type_error:
  type_builtin_result_ok (get_tenv cx) tb result_ty target_ty ts ∧
  well_typed_type_builtin_args tb target_ty ts ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) result_ty = SOME result_tv ∧
  LIST_REL value_has_type tvs vs ∧ context_well_typed cx ==>
  !msg. evaluate_type_builtin cx tb target_ty vs <> INR (TypeError msg)
Proof
  Cases_on `tb` >>
  rw[type_builtin_result_ok_def, well_typed_type_builtin_args_def,
     evaluate_type_builtin_def, LET_THM] >>
  gvs[LENGTH_EQ_NUM_compute, AllCaseEqs()]
  >- (qpat_x_assum `is_int_type _` mp_tac >>
      rewrite_tac[is_int_type_inv] >> strip_tac >>
      gvs[evaluate_type_def, evaluate_max_value_def])
  >- simp[evaluate_max_value_def]
  >- (qpat_x_assum `is_int_type _` mp_tac >>
      rewrite_tac[is_int_type_inv] >> strip_tac >>
      gvs[evaluate_type_def, evaluate_min_value_def])
  >- simp[evaluate_min_value_def]
  >- simp[evaluate_type_builtin_def]
  >- (drule_all evaluate_convert_no_type_error >> gvs[evaluate_type_builtin_def])
  >- suspend"extract32"
  >- suspend"abi_decode"
QED

Resume well_typed_type_builtin_no_type_error[extract32]:
  gvs[LENGTH_EQ_NUM_compute] >>
  Cases_on `tvs` >> gvs[] >>
  drule_all typed_bytes_value_is_BytesV >> strip_tac >> gvs[] >>
  drule_all typed_int_value_is_IntV >> strip_tac >> gvs[] >>
  drule_all evaluate_extract32_supported_no_type_error >>
  fs[evaluate_type_builtin_def] >>
  simp[AllCaseEqs(), LET_THM]
QED

Resume well_typed_type_builtin_no_type_error[abi_decode]:
  gvs[LENGTH_EQ_NUM_compute, AllCaseEqs()] >>
  drule_all typed_bytes_value_is_BytesV >> strip_tac >> gvs[] >>
  drule_all evaluate_abi_decode_no_type_error >>
  simp[]
QED

Finalise well_typed_type_builtin_no_type_error

Theorem well_typed_convert_success[local]:
  valid_conversion from_ty to_ty /\
  evaluate_type (get_tenv cx) from_ty = SOME from_tv /\
  evaluate_type (get_tenv cx) to_ty = SOME to_tv /\
  value_has_type from_tv v_in /\
  evaluate_convert (get_tenv cx) v_in to_ty = INL v_out ==>
  value_has_type to_tv v_out
Proof
  rpt strip_tac >>
  `evaluate_type_builtin cx Convert to_ty [v_in] = INL v_out` by
    (simp[Once evaluate_type_builtin_def]) >>
  drule_all valid_conversion_success_type >> simp[]
QED

(* ===== ABI encode success typing bound helpers ===== *)

Theorem evaluate_abi_encode_bytes_success_type_bound[local]:
  evaluate_abi_encode_bytes tenv typ vin = INL bs ∧
  evaluate_type tenv typ = SOME tv ∧
  value_has_type tv vin ∧
  evaluate_type tenv (BaseT (BytesT (Dynamic n))) = SOME result_tv ∧
  abi_encode_method_id_size method_id +
    vyper_abi_size_bound tenv typ ≤ n ==>
  value_has_type result_tv
    (BytesV (abi_encode_method_id_bytes method_id ++ bs))
Proof
  rw[evaluate_abi_encode_bytes_def, AllCaseEqs(), LET_THM] >>
  gvs[evaluate_type_def, value_has_type_def,
      abi_encode_method_id_size_def] >>
  drule (cj 1 vyper_to_abi_enc_length_bound) >>
  disch_then drule >> simp[]
QED

Theorem MAP_evaluate_type_LIST_REL[local]:
  !tenv ts tvs.
    MAP (evaluate_type tenv) ts = MAP SOME tvs ==>
    LIST_REL (λty tv. evaluate_type tenv ty = SOME tv) ts tvs
Proof
  Induct_on `ts` >> rpt strip_tac >-
    (Cases_on `tvs` >> gvs[]) >>
  Cases_on `tvs` >> gvs[LIST_REL_CONS1]
QED

Theorem evaluate_abi_encode_tuple_bytes_success_type_bound[local]:
  evaluate_abi_encode_bytes tenv (TupleT ts) (ArrayV (TupleV vs)) = INL bs ∧
  LIST_REL (λty tv. evaluate_type tenv ty = SOME tv) ts tvs ∧
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) ∧
  evaluate_type tenv (BaseT (BytesT (Dynamic n))) = SOME result_tv ∧
  abi_encode_method_id_size method_id +
    vyper_abi_size_bound tenv (TupleT ts) ≤ n ==>
  value_has_type result_tv
    (BytesV (abi_encode_method_id_bytes method_id ++ bs))
Proof
  rw[evaluate_abi_encode_bytes_def, AllCaseEqs(), LET_THM] >>
  gvs[evaluate_type_def, value_has_type_def, vyper_abi_size_bound_def,
      abi_encode_method_id_size_def] >>
  qspecl_then [`tenv`, `ts`, `vs`, `avs`, `tvs`] mp_tac
    (cj 2 vyper_to_abi_enc_length_bound) >> simp[] >> decide_tac
QED

Theorem well_typed_abi_encode_tuple_success[local]:
  abi_encode_size_ok (get_tenv cx) (TupleT ts) o' n /\
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME result_tv /\
  LIST_REL value_has_type tvs vs /\
  evaluate_abi_encode_bytes (get_tenv cx) (TupleT ts) (ArrayV (TupleV vs)) = INL bs ==>
  value_has_type result_tv (BytesV (abi_encode_method_id_bytes o' ++ bs))
Proof
  rpt strip_tac >>
  `LIST_REL (λty tv. evaluate_type (get_tenv cx) ty = SOME tv) ts tvs` by
    (irule MAP_evaluate_type_LIST_REL >> simp[]) >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV vs))` by
    simp[value_has_type_def, values_have_types_LIST_REL] >>
  `vyper_abi_size_bound (get_tenv cx) (TupleT ts) +
   abi_encode_method_id_size o' <= n` by
    gvs[abi_encode_size_ok_def] >>
  `abi_encode_method_id_size o' +
   vyper_abi_size_bound (get_tenv cx) (TupleT ts) <= n` by
    decide_tac >>
  drule_all evaluate_abi_encode_tuple_bytes_success_type_bound >>
  simp[]
QED

Theorem well_typed_type_builtin_success_type:
  type_builtin_result_ok (get_tenv cx) tb result_ty target_ty ts ∧
  well_typed_type_builtin_args tb target_ty ts ∧
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs ∧
  evaluate_type (get_tenv cx) result_ty = SOME result_tv ∧
  LIST_REL value_has_type tvs vs ∧ context_well_typed cx ∧
  evaluate_type_builtin cx tb target_ty vs = INL v ==>
  value_has_type result_tv v
Proof
  Cases_on `tb` >>
  rw[type_builtin_result_ok_def, well_typed_type_builtin_args_def,
     evaluate_type_builtin_def, AllCaseEqs(), LET_THM] >>
  gvs[LENGTH_EQ_NUM_compute]
  >- (drule default_value_has_type_thm >> simp[])
  >- metis_tac[evaluate_max_value_well_typed]
  >- metis_tac[evaluate_max_value_well_typed]
  >- metis_tac[evaluate_min_value_well_typed]
  >- metis_tac[evaluate_min_value_well_typed]
  >- gvs[evaluate_type_def, evaluate_type_builtin_def,
         within_int_bound_def, value_has_type_def]
  >- (gvs[evaluate_type_builtin_def, LENGTH_EQ_NUM_compute] >>
      drule_all well_typed_convert_success >> simp[])
  >- (gvs[LENGTH_EQ_NUM_compute] >>
      Cases_on `tvs` >> gvs[] >>
      drule_all typed_bytes_value_is_BytesV >> strip_tac >> gvs[] >>
      drule_all typed_int_value_is_IntV >> strip_tac >> gvs[] >>
      gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
      drule_all evaluate_extract32_well_typed >> simp[])
  >- (`evaluate_type (get_tenv cx) (TupleT [result_ty]) =
        SOME (TupleTV [result_tv])` by
       (simp[evaluate_type_def, type_slot_size_def] >>
        drule evaluate_type_well_formed_type_value >> strip_tac >>
        drule well_formed_type_value_slot_size >> simp[]) >>
      drule_all typed_bytes_value_is_BytesV >> strip_tac >> gvs[] >>
      gvs[evaluate_type_builtin_def, AllCaseEqs(), LET_THM] >>
      drule_all evaluate_abi_decode_well_typed >>
      simp[evaluate_type_def, value_has_type_def])
  >| [ (`abi_encode_method_id_size o' +
         vyper_abi_size_bound (get_tenv cx) t <= n` by
          (gvs[abi_encode_size_ok_def, vyper_abi_size_bound_def] >>
           Cases_on `vyper_is_dynamic (get_tenv cx) t` >> gvs[] >> decide_tac) >>
        irule evaluate_abi_encode_bytes_success_type_bound >>
        qexistsl [`n`, `get_tenv cx`, `x0`, `t`, `v'`] >> simp[])
     , metis_tac[well_typed_abi_encode_tuple_success]
     , metis_tac[well_typed_abi_encode_tuple_success] ]
QED

(* ===== Calls / special targets ===== *)

(* TODO(cleanup): word_size arithmetic facts are general VFM/word-size support
   lemmas and should move to a shared arithmetic/support theory when consumers
   are reorganized. *)
Theorem raw_call_return_type_well_formed:
  flags.rcf_max_outsize < dimword(:256) ==>
  well_formed_type tenv (raw_call_return_type flags)
Proof
  Cases_on `flags` >>
  rw[raw_call_return_type_def, well_formed_type_def, evaluate_type_def,
     type_slot_size_def] >> rw[] >>
  `word_size n ≤ n` by (irule word_size_le >> rw[]) >>
  Cases_on`word_size n < n` >> gvs[type_slot_size_def] >>
  rw[] >>
  `n = 1` by (irule word_size_not_lt_self >> rw[]) >>
  gvs[vfmConstantsTheory.word_size_def]
QED

Theorem internal_call_signature_sound:
  fn_sigs_consistent fn_sigs cx ∧
  FLOOKUP fn_sigs (src,fn) = SOME sig ==>
  ∃ts fm nr params dflts body.
    get_module_code cx src = SOME ts ∧
    lookup_callable_function cx.in_deploy fn ts = SOME (fm,nr,params,dflts,sig.ret_ty,body) ∧
    sig.param_types = MAP SND params ∧ sig.num_defaults = LENGTH dflts
Proof
  rw[fn_sigs_consistent_def]
QED

Theorem ext_call_args_typed:
  well_typed_expr env (Call ty (ExtCall stat fsig) args drv) ==>
  well_typed_exprs env args ∧ well_typed_opt env drv
Proof
  Cases_on `fsig` >> Cases_on `r` >> rw[well_typed_expr_def]
QED



(* ===== ABI encode result-bound gap (RESOLVED) ===== *)
(* type_builtin_result_ok now includes vyper_abi_size_bound condition.
   Old probes confirmed the gap; repair adds the bound.
   New probe below verifies the repair correctly rejects the too-small bound. *)

(* Probe: with the repaired definition, n=1 is correctly REJECTED for uint256 encoding
   because vyper_abi_size_bound FEMPTY (TupleT [BaseT (UintT 256)]) = 32 > 1 *)
Theorem abi_encode_probe_result_ok_rejects_small_bound:
  ¬type_builtin_result_ok FEMPTY (AbiEncode T NONE) (BaseT (BytesT (Dynamic 1)))
    (TupleT [BaseT (UintT 256)]) [BaseT (UintT 256)]
Proof
  simp[type_builtin_result_ok_def, abi_encode_size_ok_def] >> EVAL_TAC >> decide_tac
QED

(* Probe: with n=32, the result_ok predicate is satisfied *)
Theorem abi_encode_probe_result_ok_accepts_correct_bound:
  type_builtin_result_ok FEMPTY (AbiEncode T NONE) (BaseT (BytesT (Dynamic 32)))
    (TupleT [BaseT (UintT 256)]) [BaseT (UintT 256)]
Proof
  simp[type_builtin_result_ok_def, abi_encode_size_ok_def] >> EVAL_TAC >> decide_tac
QED

(* Probe: vyper_abi_size_bound gives the correct minimum bound (32) *)
Theorem abi_encode_probe_size_bound:
  vyper_abi_size_bound FEMPTY (TupleT [BaseT (UintT 256)]) = 32
Proof
  EVAL_TAC
QED


(* UNPROVABILITY PROBE: AsWeiValue with IntT can return TypeError *)
Theorem as_wei_value_IntT_TypeError_probe[local]:
  evaluate_as_wei_value Kwei (IntV (-(&1))) = INR (TypeError "ewv neg")
Proof
  EVAL_TAC
QED
