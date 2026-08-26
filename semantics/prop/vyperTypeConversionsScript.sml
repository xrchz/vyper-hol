(*
 * Conversion, max/min value, and extract32 typing lemmas.
 *)

Theory vyperTypeConversions
Ancestors
  list rich_list arithmetic finite_map option pair words byte
  vyperAST vyperValue vyperValueOperation vyperMisc vyperContext
  vyperTyping vyperArith vyperTypeSystem vyperTypeValues vyperTypeDefaults
Libs
  wordsLib

Theorem bounded_decimal_op_no_type_error[simp]:
  bounded_decimal_op x <> INR (TypeError s)
Proof
  rw[bounded_decimal_op_def]
QED

Triviality uint_value_is_int[local]:
  !m v. value_has_type (BaseTV (UintT m)) v ==> ?i. v = IntV i
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Triviality sint_value_is_int[local]:
  !m v. value_has_type (BaseTV (IntT m)) v ==> ?i. v = IntV i
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Triviality bool_value_is_bool[local]:
  !v. value_has_type (BaseTV BoolT) v ==> ?b. v = BoolV b
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Triviality decimal_value_is_decimal[local]:
  !v. value_has_type (BaseTV DecimalT) v ==> ?d. v = DecimalV d
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Triviality bytes_value_is_bytes[local]:
  !bd v. value_has_type (BaseTV (BytesT bd)) v ==> ?bs. v = BytesV bs
Proof
  Cases_on `bd` >> Cases_on `v` >> simp[value_has_type_def]
QED

Triviality address_value_is_bytes[local]:
  !v. value_has_type (BaseTV AddressT) v ==> ?bs. v = BytesV bs
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Triviality string_value_is_string[local]:
  !n v. value_has_type (BaseTV (StringT n)) v ==> ?s. v = StringV s
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Triviality flag_value_is_flag[local]:
  !m v. value_has_type (FlagTV m) v ==> ?k. v = FlagV k
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Triviality evaluate_type_BaseT_SOME[local]:
  !tenv bt tv. evaluate_type tenv (BaseT bt) = SOME tv ==> tv = BaseTV bt
Proof
  Cases_on `bt` >> gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `b` >> gvs[]
QED

Triviality evaluate_type_FlagT_SOME[local]:
  !tenv fid tv. evaluate_type tenv (FlagT fid) = SOME tv ==>
  ?m. tv = FlagTV m
Proof
  gvs[evaluate_type_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem valid_conversion_no_type_error:
  valid_conversion from_ty to_ty /\
  evaluate_type (get_tenv cx) from_ty = SOME from_tv /\
  evaluate_type (get_tenv cx) to_ty = SOME to_tv /\
  value_has_type from_tv v ==>
  !msg. evaluate_type_builtin cx Convert to_ty [v] <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  gvs[evaluate_type_builtin_def] >>
  Cases_on`from_ty` >> Cases_on`to_ty` >>
  gvs[valid_conversion_def] >>
  imp_res_tac evaluate_type_BaseT_SOME >>
  imp_res_tac evaluate_type_FlagT_SOME >>
  TRY (qpat_x_assum `from_tv = _` SUBST_ALL_TAC) >>
  TRY (qpat_x_assum `to_tv = _` SUBST_ALL_TAC) >>
  Cases_on `b` >> gvs[valid_conversion_def] >>
  TRY (qpat_x_assum `valid_conversion (BaseT _) (BaseT b')` mp_tac >>
       Cases_on `b'` >> strip_tac) >>
  gvs[valid_conversion_def] >>
  TRY (qpat_x_assum `evaluate_convert _ _ (BaseT (BytesT b)) = _` mp_tac >>
       Cases_on `b` >> strip_tac) >>
  TRY (qpat_x_assum `evaluate_type _ (FlagT _) = SOME _` mp_tac >>
       simp[evaluate_type_def, AllCaseEqs()] >> strip_tac) >>
  TRY (drule_all uint_value_is_int >> strip_tac >> gvs[]) >>
  TRY (drule_all sint_value_is_int >> strip_tac >> gvs[]) >>
  TRY (drule_all bool_value_is_bool >> strip_tac >> gvs[]) >>
  TRY (drule_all decimal_value_is_decimal >> strip_tac >> gvs[]) >>
  TRY (drule_all bytes_value_is_bytes >> strip_tac >> gvs[]) >>
  TRY (drule_all address_value_is_bytes >> strip_tac >> gvs[]) >>
  TRY (drule_all string_value_is_string >> strip_tac >> gvs[]) >>
  TRY (drule_all flag_value_is_flag >> strip_tac >> gvs[]) >>
  gvs[oneline value_has_type_def, evaluate_convert_def]
QED

Theorem evaluate_max_value_well_typed:
  !typ tv. evaluate_type tenv typ = SOME tv /\
           evaluate_max_value typ = INL v ==>
           value_has_type tv v
Proof
  Cases >> simp[evaluate_max_value_def, evaluate_type_def] >>
  Cases_on `b` >> simp[evaluate_max_value_def, evaluate_type_def,
                        AllCaseEqs(), value_has_type_def,
                        within_int_bound_def] >>
  rpt strip_tac >> gvs[value_has_type_def, within_int_bound_def] >>
  `1 <= 2 ** n /\ 1 <= 2 ** (n - 1)` by simp[ONE_LE_EXP] >>
  simp[integerTheory.INT_SUB, integerTheory.NUM_OF_INT]
QED

Theorem evaluate_min_value_well_typed:
  !typ tv. evaluate_type tenv typ = SOME tv /\
           evaluate_min_value typ = INL v ==>
           value_has_type tv v
Proof
  Cases >> simp[evaluate_min_value_def, evaluate_type_def] >>
  Cases_on `b` >> simp[evaluate_min_value_def, evaluate_type_def,
                        AllCaseEqs(), value_has_type_def,
                        within_int_bound_def]
QED

Theorem evaluate_convert_well_typed:
  !tenv v typ v' tv.
    evaluate_convert tenv v typ = INL v' /\
    evaluate_type tenv typ = SOME tv ==>
    value_has_type tv v'
Proof
  ho_match_mp_tac evaluate_convert_ind >>
  rpt strip_tac >>
  gvs[evaluate_convert_def, AllCaseEqs(), evaluate_type_def,
      value_has_type_def, bounded_decimal_op_def,
      within_int_bound_def, compatible_bound_def] >>
  gvs[LENGTH_TAKE, listTheory.PAD_RIGHT,
      LENGTH_word_to_bytes, word_to_bytes_be_def] >>
  TRY (Cases_on `b` >> gvs[ONE_LT_EXP])
QED

Theorem evaluate_extract32_well_typed:
  !bs n bt v tenv tv.
    evaluate_extract32 bs n bt = INL v /\
    evaluate_type tenv (BaseT bt) = SOME tv ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  gvs[evaluate_extract32_def, AllCaseEqs()] >>
  TRY (drule evaluate_convert_well_typed >>
       disch_then irule >>
       gvs[evaluate_type_def, AllCaseEqs()] >> NO_TAC) >>
  gvs[value_has_type_def, evaluate_type_def, AllCaseEqs(),
      LENGTH_TAKE, LENGTH_DROP]
QED

Theorem valid_conversion_success_type:
  valid_conversion from_ty to_ty /\
  evaluate_type (get_tenv cx) from_ty = SOME from_tv /\
  evaluate_type (get_tenv cx) to_ty = SOME to_tv /\
  value_has_type from_tv v /\
  evaluate_type_builtin cx Convert to_ty [v] = INL v' ==>
  value_has_type to_tv v'
Proof
  rw[evaluate_type_builtin_def] >>
  drule_all evaluate_convert_well_typed >> simp[]
QED
