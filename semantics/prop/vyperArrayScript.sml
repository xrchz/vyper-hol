Theory vyperArray

Ancestors
  vyperValue vyperValueOperation vyperState vyperInterpreter vyperLookupStorageScopes

Libs
  BasicProvers

Definition array_is_mutable_def[simp]:
  array_is_mutable (DynArrayV _) = T ∧
  array_is_mutable (SArrayV _) = T ∧
  array_is_mutable (TupleV _) = F
End

Definition array_is_dynamic_def[simp]:
  array_is_dynamic (DynArrayV _) = T ∧
  array_is_dynamic (SArrayV _) = F ∧
  array_is_dynamic (TupleV _) = F
End

Definition valid_index_def[simp]:
  valid_index tv a (i:int) ⇔ 0 ≤ i ∧ i < &array_length tv a
End

(* ============================================================
   array_set: extract the resulting array_value from array_set_index

   When array_is_mutable a ∧ valid_index tv a k, we have:
     array_set_index tv a k v = INL (ArrayV (array_set tv a k v))

   This lets the simplifier eliminate case expressions over
   array_set_index without introducing existentials.
   ============================================================ *)

Definition array_set_def:
  array_set tv a k v =
    case array_set_index tv a k v of
      INL (ArrayV a') => a'
    | _ => a
End

(* ===== Helper Lemmas for insert_sarray ===== *)

Theorem ALOOKUP_insert_sarray_same[local]:
  ∀k v al. ALOOKUP (insert_sarray k v al) k = SOME v
Proof
  ho_match_mp_tac insert_sarray_ind
  \\ rw[insert_sarray_def]
QED

Theorem ALOOKUP_insert_sarray_other[local]:
  ∀k v al k'. k ≠ k' ⇒ ALOOKUP (insert_sarray k v al) k' = ALOOKUP al k'
Proof
  ho_match_mp_tac insert_sarray_ind
  \\ rw[insert_sarray_def]
QED

Theorem TAKE_DROP_LUPDATE[local]:
  ∀ls k e. k < LENGTH ls ⇒ TAKE k ls ++ [e] ++ DROP (SUC k) ls = LUPDATE e k ls
Proof
  Induct \\ simp[]
  \\ rpt gen_tac \\ Cases_on`k`
  \\ simp[listTheory.LUPDATE_DEF]
QED

Theorem array_index_valid:
  ∀tv a i. valid_index tv a i ⇒ IS_SOME (array_index tv a i)
Proof
  rpt gen_tac \\ simp[valid_index_def] \\ strip_tac
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ Cases_on `a`
  \\ gvs[array_index_def, array_length_def, listTheory.oEL_THM]
  (* SArrayV *)
  \\ Cases_on `tv`
  \\ gvs[array_length_def, array_index_def]
  \\ Cases_on `b`
  \\ gvs[array_length_def, array_index_def]
  \\ CASE_TAC \\ simp[]
QED

Theorem array_set_index_valid:
  ∀tv a i v. array_is_mutable a ∧ valid_index tv a i ⇒ ∃a'. array_set_index tv a i v = INL (ArrayV a')
Proof
  rpt gen_tac \\ simp[valid_index_def] \\ strip_tac
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ Cases_on `a`
  \\ gvs[array_set_index_def, array_length_def, AllCaseEqs()]
  \\ Cases_on `tv`
  \\ gvs[array_length_def, array_set_index_def, AllCaseEqs()]
  \\ Cases_on `b`
  \\ gvs[array_length_def, array_set_index_def, AllCaseEqs()]
QED

Theorem array_length_after_set:
  ∀tv a a' i v. array_set_index tv a i v = INL (ArrayV a') ⇒ array_length tv a' = array_length tv a
Proof
  gen_tac \\ Cases \\ rw[array_set_index_def, array_length_def]
  \\ gvs[AllCaseEqs(), array_length_def]
  \\ Cases_on `v = default_value t` \\ gvs[]
QED

Theorem array_index_after_set_same:
  ∀tv a a' i v. array_set_index tv a i v = INL (ArrayV a') ⇒ array_index tv a' i = SOME v
Proof
  gen_tac \\ Cases \\ simp[array_set_index_def, AllCaseEqs()]
  \\ rw[] \\ simp[array_index_def, listTheory.oEL_THM,
                   listTheory.EL_APPEND_EQN, listTheory.LENGTH_TAKE_EQ,
                   ALOOKUP_insert_sarray_same, alistTheory.ALOOKUP_ADELKEY]
  \\ Cases_on `v = default_value t`
  \\ gvs[alistTheory.ALOOKUP_ADELKEY, ALOOKUP_insert_sarray_same]
QED

Theorem array_index_after_set_other:
  ∀tv a a' i j v. i ≠ j ∧ array_set_index tv a i v = INL (ArrayV a') ⇒ array_index tv a' j = array_index tv a j
Proof
  gen_tac \\ Cases \\ simp[array_set_index_def, AllCaseEqs()]
  \\ rpt gen_tac \\ strip_tac
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ simp[array_index_def, TAKE_DROP_LUPDATE,
          listTheory.oEL_LUPDATE, alistTheory.ALOOKUP_ADELKEY,
          ALOOKUP_insert_sarray_other]
  \\ rw[] \\ gvs[]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ simp[alistTheory.ALOOKUP_ADELKEY, ALOOKUP_insert_sarray_other]
QED

Theorem array_length_after_pop:
  ∀tv a a'. pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_length tv a' = array_length tv a - 1
Proof
  gen_tac \\ Cases \\ simp[pop_element_def, array_length_def]
  \\ rw[] \\ gvs[rich_listTheory.LENGTH_FRONT]
QED

Theorem array_index_after_pop:
  ∀tv a a' i. valid_index tv a' i ∧ pop_element (ArrayV a) = INL (ArrayV a') ⇒ array_index tv a i = array_index tv a' i
Proof
  gen_tac \\ Cases \\ simp[pop_element_def]
  \\ rw[] \\ gvs[array_index_def, array_length_def]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ Cases_on`l`
  \\ gvs[listTheory.oEL_THM, rich_listTheory.LENGTH_FRONT,
         rich_listTheory.EL_FRONT, listTheory.NULL_EQ]
QED

Theorem array_pop_valid:
  ∀tv a. array_is_dynamic a ∧ array_length tv a ≠ 0 ⇒ ∃a'. pop_element (ArrayV a) = INL (ArrayV a')
Proof
  gen_tac \\ Cases \\ rw[pop_element_def, array_length_def]
QED

Theorem array_length_after_append:
  ∀tv a a' v. append_element tv (ArrayV a) v = INL (ArrayV a') ⇒ array_length tv a' = array_length tv a + 1
Proof
  gen_tac \\ Cases \\ simp[append_element_def, array_length_def, AllCaseEqs()]
  \\ rw[]
QED

Theorem array_index_after_append:
  ∀tv a a' v. append_element tv (ArrayV a) v = INL (ArrayV a') ⇒ ∃ty v'. safe_cast ty v = SOME v' ∧ array_index tv a' &(array_length tv a) = SOME v'
Proof
  gen_tac \\ Cases \\ simp[append_element_def, AllCaseEqs()]
  \\ rw[] \\ gvs[]
  \\ qexists_tac`elem_tv` \\ qexists_tac`v'`
  \\ simp[array_index_def, array_length_def,
          listTheory.oEL_EQ_EL, listTheory.LENGTH_SNOC,
          listTheory.EL_LENGTH_SNOC]
QED

Theorem array_index_after_append_other:
  ∀tv a a' i v. valid_index tv a i ∧ append_element tv (ArrayV a) v = INL (ArrayV a') ⇒ array_index tv a' i = array_index tv a i
Proof
  gen_tac \\ Cases \\ simp[append_element_def, AllCaseEqs()]
  \\ rw[] \\ gvs[array_index_def, array_length_def]
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ simp[listTheory.oEL_THM, listTheory.LENGTH_SNOC, listTheory.EL_SNOC]
QED

Theorem array_elements_length_dyn:
  ∀tv vs. LENGTH (array_elements tv (DynArrayV vs)) = array_length tv (DynArrayV vs)
Proof
  simp[array_elements_def, array_length_def]
QED

Theorem array_elements_length_tuple:
  ∀tv vs. LENGTH (array_elements tv (TupleV vs)) = array_length tv (TupleV vs)
Proof
  simp[array_elements_def, array_length_def]
QED

Theorem array_elements_length_sarray:
  ∀t n al. LENGTH (array_elements (ArrayTV t (Fixed n)) (SArrayV al)) = array_length (ArrayTV t (Fixed n)) (SArrayV al)
Proof
  simp[array_elements_def, array_length_def]
QED

Theorem array_elements_index:
  ∀tv a i v. valid_index tv a i ⇒ (EL (Num i) (array_elements tv a) = v ⇔ array_index tv a i = SOME v)
Proof
  rpt gen_tac \\ simp[valid_index_def] \\ strip_tac
  \\ drule integerTheory.NUM_POSINT_EXISTS \\ strip_tac \\ gvs[]
  \\ Cases_on `a`
  \\ gvs[array_elements_def, array_index_def, array_length_def,
         listTheory.oEL_EQ_EL, EQ_SYM_EQ]
  (* SArrayV *)
  \\ Cases_on `tv`
  \\ gvs[array_elements_def, array_index_def, array_length_def]
  \\ Cases_on `b`
  \\ gvs[array_elements_def, array_index_def, array_length_def]
  \\ CASE_TAC
QED

Theorem array_elements_after_set:
  ∀tv a a' i v.
    array_set_index tv a i v = INL (ArrayV a') ⇒
    array_elements tv a' = (TAKE (Num i) (array_elements tv a) ++ [v] ++ DROP (SUC (Num i)) (array_elements tv a))
Proof
  gen_tac \\ Cases \\ simp[array_set_index_def, array_elements_def, AllCaseEqs()]
  \\ rw[]
  \\ simp[TAKE_DROP_LUPDATE, listTheory.LENGTH_GENLIST,
          listTheory.LUPDATE_GENLIST, listTheory.GENLIST_FUN_EQ]
  \\ rw[combinTheory.APPLY_UPDATE_THM]
  \\ gvs[alistTheory.ALOOKUP_ADELKEY,
         ALOOKUP_insert_sarray_same, ALOOKUP_insert_sarray_other]
QED

Theorem array_elements_after_pop:
  ∀tv a a'.
    pop_element (ArrayV a) = INL (ArrayV a') ⇒
    array_elements tv a' = FRONT (array_elements tv a)
Proof
  gen_tac \\ Cases \\ simp[pop_element_def, array_elements_def]
QED

Theorem array_elements_after_append:
  ∀tv a a' v.
    append_element tv (ArrayV a) v = INL (ArrayV a') ⇒
    ∃ty v'. safe_cast ty v = SOME v' ∧ array_elements tv a' = array_elements tv a ++ [v']
Proof
  gen_tac \\ Cases \\ simp[append_element_def, AllCaseEqs()]
  \\ rpt strip_tac \\ gvs[]
  \\ qexists_tac`elem_tv` \\ qexists_tac`v'`
  \\ simp[array_elements_def, listTheory.SNOC_APPEND]
QED

Theorem assign_subscripts_array_replace:
  ∀tv a k v.
    array_is_mutable a ∧ valid_index tv a k ⇒
    assign_subscripts tv (ArrayV a) [ValueSubscript (IntV k)] (Replace v) =
    array_set_index tv a k v
Proof
  rpt strip_tac >>
  simp[Once assign_subscripts_def] >>
  `IS_SOME (array_index tv a k)` by metis_tac[array_index_valid] >>
  Cases_on `array_index tv a k` >> gvs[assign_subscripts_def]
QED

Theorem array_length_sarray[simp]:
  array_length (ArrayTV t (Fixed n)) (SArrayV al) = n
Proof
  simp[array_length_def]
QED

Theorem assign_array_read_same:
  ∀tv av i v.
    array_is_mutable av ∧ valid_index tv av i ⇒
    ∃av'. assign_subscripts tv (ArrayV av) [ValueSubscript (IntV i)] (Replace v) =
            INL (ArrayV av') ∧
          array_index tv av' i = SOME v
Proof
  rpt strip_tac >>
  `IS_SOME (array_index tv av i)` by metis_tac[array_index_valid] >>
  Cases_on `array_index tv av i` >> gvs[] >>
  `∃av'. array_set_index tv av i v = INL (ArrayV av')` by (
    irule array_set_index_valid >> simp[]) >>
  qexists_tac `av'` >>
  simp[Once assign_subscripts_def, assign_subscripts_def] >>
  metis_tac[array_index_after_set_same]
QED

Theorem array_set_index_is_mutable:
  ∀tv a i v a'.
    array_set_index tv a i v = INL (ArrayV a') ⇒
    array_is_mutable a'
Proof
  rpt gen_tac >> Cases_on `a` >>
  FULL_SIMP_TAC (srw_ss()) [array_set_index_def, LET_THM, array_is_mutable_def] >>
  rpt (PURE_TOP_CASE_TAC >> FULL_SIMP_TAC (srw_ss()) [array_is_mutable_def])
QED

Theorem valid_index_after_set_index:
  ∀tv a a' i j v.
    valid_index tv a j ∧
    array_set_index tv a i v = INL (ArrayV a') ⇒
    valid_index tv a' j
Proof
  rw[valid_index_def] >>
  drule array_length_after_set >> simp[]
QED

(* Key theorem: array_set_index returns INL (ArrayV (array_set ...)) *)
Theorem array_set_index_INL:
  ∀tv a k v.
    array_is_mutable a ∧ valid_index tv a k ⇒
    array_set_index tv a k v = INL (ArrayV (array_set tv a k v))
Proof
  rpt strip_tac >>
  drule_all array_set_index_valid >>
  disch_then (qspec_then `v` strip_assume_tac) >>
  gvs[array_set_def]
QED

(* Properties of array_set *)
Theorem array_set_is_mutable:
  ∀tv a k v.
    array_is_mutable a ∧ valid_index tv a k ⇒
    array_is_mutable (array_set tv a k v)
Proof
  rpt strip_tac >>
  drule_all array_set_index_INL >>
  metis_tac[array_set_index_is_mutable]
QED

Theorem array_set_valid_index:
  ∀tv a k v j.
    array_is_mutable a ∧ valid_index tv a k ∧ valid_index tv a j ⇒
    valid_index tv (array_set tv a k v) j
Proof
  rpt strip_tac >>
  irule valid_index_after_set_index >>
  qexists_tac `a` >> qexists_tac `k` >> qexists_tac `v` >>
  simp[array_set_index_INL]
QED

Theorem array_set_length:
  ∀tv a k v.
    array_is_mutable a ∧ valid_index tv a k ⇒
    array_length tv (array_set tv a k v) = array_length tv a
Proof
  rpt strip_tac >>
  irule array_length_after_set >>
  qexists_tac `k` >> qexists_tac `v` >>
  simp[array_set_index_INL]
QED

Theorem array_set_index_same:
  ∀tv a k v.
    array_is_mutable a ∧ valid_index tv a k ⇒
    array_index tv (array_set tv a k v) k = SOME v
Proof
  rpt strip_tac >>
  drule_all array_set_index_INL >>
  disch_then (qspec_then `v` mp_tac) >>
  metis_tac[array_index_after_set_same]
QED

Theorem array_set_index_other:
  ∀tv a k v j.
    array_is_mutable a ∧ valid_index tv a k ∧ j ≠ k ⇒
    array_index tv (array_set tv a k v) j = array_index tv a j
Proof
  rpt strip_tac >>
  drule_all array_set_index_INL >>
  strip_tac >>
  irule array_index_after_set_other >>
  metis_tac[]
QED

(* ============================================================
   Constructor-specific evaluation for concrete arrays.

   Unlike array_index_def / array_set_index_def, these only fire when the
   array argument is a concrete SArrayV or DynArrayV constructor, so
   they are safe to include in the simplifier for mixed abstract/concrete
   goals.
   ============================================================ *)

Theorem array_index_sarray:
  ∀t n al i.
    array_index (ArrayTV t (Fixed n)) (SArrayV al) i =
    if 0 ≤ i ∧ Num i < n then
      case ALOOKUP al (Num i) of NONE => SOME (default_value t) | SOME v => SOME v
    else NONE
Proof
  rw[array_index_def, LET_THM] >>
  every_case_tac >> gvs[]
QED

Theorem array_index_dyn:
  ∀tv ls i.
    array_index tv (DynArrayV ls) i =
    if 0 ≤ i then oEL (Num i) ls else NONE
Proof
  rw[array_index_def, LET_THM]
QED

Theorem array_set_sarray:
  ∀t n al k v.
    0 ≤ k ∧ Num k < n ⇒
    array_set (ArrayTV t (Fixed n)) (SArrayV al) k v =
    SArrayV (if v = default_value t then ADELKEY (Num k) al
             else insert_sarray (Num k) v al)
Proof
  rw[array_set_def, array_set_index_def, LET_THM]
QED

Theorem array_set_dyn:
  ∀tv ls k v.
    0 ≤ k ∧ Num k < LENGTH ls ⇒
    array_set tv (DynArrayV ls) k v =
    DynArrayV (TAKE (Num k) ls ++ [v] ++ DROP (SUC (Num k)) ls)
Proof
  rw[array_set_def, array_set_index_def, LET_THM]
QED

(* assign_subscripts with Replace reduces to INL (ArrayV (array_set ...)) *)
Theorem assign_subscripts_replace_INL:
  ∀tv a k v.
    array_is_mutable a ∧ valid_index tv a k ⇒
    assign_subscripts tv (ArrayV a) [ValueSubscript (IntV k)] (Replace v) =
    INL (ArrayV (array_set tv a k v))
Proof
  simp[assign_subscripts_array_replace, array_set_index_INL]
QED

(* assign_subscripts with Update — computes everything inline, no existentials *)
val assign_subscripts_int_sub_clause = cj 5 assign_subscripts_def;
val assign_subscripts_update_clause = cj 2 assign_subscripts_def;

Theorem assign_subscripts_update_INL:
  ∀tv a k ty bop v.
    array_is_mutable a ∧ valid_index tv a k ∧
    IS_SOME (type_to_int_bound ty) ∧
    ISL (evaluate_binop (THE (type_to_int_bound ty))
           (case tv of ArrayTV t _ => t | _ => NoneTV) bop
           (THE (array_index tv a k)) v) ⇒
    assign_subscripts tv (ArrayV a) [ValueSubscript (IntV k)] (Update ty bop v) =
    INL (ArrayV (array_set tv a k
           (OUTL (evaluate_binop (THE (type_to_int_bound ty))
                    (case tv of ArrayTV t _ => t | _ => NoneTV) bop
                    (THE (array_index tv a k)) v))))
Proof
  rpt strip_tac >>
  `IS_SOME (array_index tv a k)` by simp[array_index_valid] >>
  ONCE_REWRITE_TAC [assign_subscripts_int_sub_clause] >>
  REWRITE_TAC [assign_subscripts_update_clause] >>
  simp[LET_THM, array_set_index_INL] >>
  Cases_on `array_index tv a k` >> fs[] >>
  Cases_on `type_to_int_bound ty` >> fs[] >>
  CASE_TAC >> fs[] >> CASE_TAC >> fs[]
QED

(* ============================================================
   make_array_value properties — abstract characterization

   These lemmas let callers reason about make_array_value results
   (mutability, length) without expanding into the sparse SArrayV
   representation, preventing unwanted interaction with
   array_set_sarray / insert_sarray_def.
   ============================================================ *)

Theorem make_array_value_is_mutable:
  ∀t n vs. array_is_mutable (make_array_value t (Fixed n) vs)
Proof
  simp[make_array_value_def]
QED

Theorem make_array_value_length:
  ∀t n vs. array_length (ArrayTV t (Fixed n)) (make_array_value t (Fixed n) vs) = n
Proof
  simp[make_array_value_def]
QED

Theorem array_index_bounds:
  ∀tv a i v.
    array_index tv a i = SOME v ∧
    (∀al. a = SArrayV al ⇒ ∃t n. tv = ArrayTV t (Fixed n)) ⇒
    valid_index tv a i
Proof
  rpt gen_tac >> strip_tac
  >> `0 <= i` by (Cases_on `a` >> gvs[array_index_def])
  >> drule integerTheory.NUM_POSINT_EXISTS >> strip_tac >> gvs[]
  >> Cases_on `a`
  >> gvs[array_index_def, array_length_def, listTheory.oEL_THM,
         AllCaseEqs()]
QED

Theorem evaluate_subscript_array_bounds:
  ∀tenv tv av i x.
    evaluate_subscript tenv tv (Value (ArrayV av)) (IntV i) = INL x ∧
    (∀al. av = SArrayV al ⇒ ∃t n. tv = ArrayTV t (Fixed n)) ⇒
    valid_index tv av i
Proof
  rw[evaluate_subscript_def, AllCaseEqs()]
  >> drule_all array_index_bounds >> simp[]
QED
