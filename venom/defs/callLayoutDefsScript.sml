(*
 * Canonical physical call-parameter layout.
 *
 * This theory is deliberately below venomWf and static-layout theories.
 *)

Theory callLayoutDefs
Ancestors
  venomInst
  dretShapeDefs

Definition fn_entry_insts_def:
  fn_entry_insts fn =
    case entry_block fn of
      NONE => []
    | SOME bb => bb.bb_instructions
End

Definition fn_hidden_fmp_param_def:
  fn_hidden_fmp_param fn =
    FIND (\inst. inst.inst_opcode = FMP_PARAM) (fn_entry_insts fn)
End

Definition fn_retpc_param_def:
  fn_retpc_param fn =
    FIND (\inst. inst.inst_opcode = RETPC_PARAM) (fn_entry_insts fn)
End

Definition fn_user_param_insts_def:
  fn_user_param_insts fn =
    FILTER (\inst. inst.inst_opcode = PARAM) (fn_entry_insts fn)
End

(* The literal operand is the physical position in the complete parameter
 * prefix.  Every physical parameter also defines exactly one SSA value. *)
Definition param_inst_at_def:
  param_inst_at k inst <=>
    is_param_opcode inst.inst_opcode /\
    inst.inst_operands = [Lit (n2w k)] /\
    LENGTH inst.inst_outputs = 1
End

Definition erase_param_index_def:
  erase_param_index inst =
    if is_param_opcode inst.inst_opcode then
      inst with inst_operands := []
    else inst
End
Definition param_insts_from_def:
  param_insts_from k [] = T /\
  param_insts_from k (inst::insts) =
    (param_inst_at k inst /\ param_insts_from (SUC k) insts)
End

Definition no_param_insts_def:
  no_param_insts insts <=>
    EVERY (\inst. ~is_param_opcode inst.inst_opcode) insts
End

Definition canonical_after_fmp_def:
  canonical_after_fmp k [] = T /\
  canonical_after_fmp k (inst::insts) =
    if inst.inst_opcode = RETPC_PARAM then
      param_inst_at k inst /\ no_param_insts insts
    else
      no_param_insts (inst::insts)
End

Definition canonical_entry_params_from_def:
  canonical_entry_params_from k [] = T /\
  canonical_entry_params_from k (inst::insts) =
    if inst.inst_opcode = PARAM then
      param_inst_at k inst /\
      canonical_entry_params_from (SUC k) insts
    else if inst.inst_opcode = FMP_PARAM then
      param_inst_at k inst /\ canonical_after_fmp (SUC k) insts
    else if inst.inst_opcode = RETPC_PARAM then
      param_inst_at k inst /\ no_param_insts insts
    else
      no_param_insts (inst::insts)
End

Definition canonical_param_prefix_def:
  canonical_param_prefix fn <=>
    case fn.fn_blocks of
      [] => F
    | entry::rest =>
        canonical_entry_params_from 0 entry.bb_instructions /\
        EVERY (\bb. no_param_insts bb.bb_instructions) rest
End

Theorem canonical_after_fmp_iff:
  !k insts.
    canonical_after_fmp k insts <=>
    ?retpc body.
      insts = retpc ++ body /\
      (retpc = [] \/ ?inst. retpc = [inst] /\
                              inst.inst_opcode = RETPC_PARAM) /\
      param_insts_from k retpc /\
      no_param_insts body
Proof
  rpt gen_tac >> Cases_on `insts` >-
    simp[canonical_after_fmp_def, param_insts_from_def, no_param_insts_def]
  >> rename1 `inst::insts`
  >> Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (simp[canonical_after_fmp_def] >> eq_tac
      >- (strip_tac >> qexistsl [`[inst]`, `insts`] >>
          simp[param_insts_from_def])
      >> strip_tac
      >> gvs[param_insts_from_def, no_param_insts_def,
             is_param_opcode_def])
  >> simp[canonical_after_fmp_def] >> eq_tac
  >- (strip_tac >> qexistsl [`[]`, `inst::insts`] >>
      simp[param_insts_from_def, no_param_insts_def])
  >> strip_tac
  >> gvs[param_insts_from_def, no_param_insts_def, is_param_opcode_def]
QED


Theorem canonical_entry_params_from_sound:
  !k insts.
    canonical_entry_params_from k insts ==>
    ?users fmp retpc body.
      insts = users ++ fmp ++ retpc ++ body /\
      EVERY (\inst. inst.inst_opcode = PARAM) users /\
      (fmp = [] \/ ?inst. fmp = [inst] /\
                           inst.inst_opcode = FMP_PARAM) /\
      (retpc = [] \/ ?inst. retpc = [inst] /\
                              inst.inst_opcode = RETPC_PARAM) /\
      param_insts_from k (users ++ fmp ++ retpc) /\
      no_param_insts body
Proof
  Induct_on `insts` >-
    simp[canonical_entry_params_from_def, param_insts_from_def,
         no_param_insts_def]
  >> rpt gen_tac
  >> rename1 `inst::insts`
  >> Cases_on `inst.inst_opcode = PARAM`
  >- (simp[canonical_entry_params_from_def] >> strip_tac
      >> qpat_x_assum `!k. canonical_entry_params_from k insts ==> _`
           (qspec_then `SUC k` mp_tac)
      >> simp[] >> strip_tac
      >> qexistsl [`inst::users`, `fmp`, `retpc`, `body`]
      >> qpat_x_assum `fmp = _` SUBST_ALL_TAC
      >> qpat_x_assum `retpc = _` SUBST_ALL_TAC
      >> fs[listTheory.APPEND_NIL]
      >> simp[param_insts_from_def])
  >> Cases_on `inst.inst_opcode = FMP_PARAM`
  >- (simp[canonical_entry_params_from_def, canonical_after_fmp_iff]
      >> strip_tac
      >> qexistsl [`[]`, `[inst]`, `retpc`, `body`]
      >> qpat_x_assum `retpc = _` SUBST_ALL_TAC
      >> fs[listTheory.APPEND_NIL]
      >> simp[param_insts_from_def])
  >> Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (simp[canonical_entry_params_from_def] >> strip_tac
      >> qexistsl [`[]`, `[]`, `[inst]`, `insts`]
      >> simp[param_insts_from_def])
  >> simp[canonical_entry_params_from_def] >> strip_tac
  >> qexistsl [`[]`, `[]`, `[]`, `inst::insts`]
  >> simp[param_insts_from_def, no_param_insts_def]
QED


Theorem param_insts_from_append:
  !k xs ys.
    param_insts_from k (xs ++ ys) <=>
    param_insts_from k xs /\
    param_insts_from (k + LENGTH xs) ys
Proof
  Induct_on `xs`
  >> simp[param_insts_from_def, arithmeticTheory.ADD_CLAUSES]
  >> metis_tac[]
QED

Theorem canonical_entry_params_from_prepend_users:
  !k users suffix.
    EVERY (\inst. inst.inst_opcode = PARAM) users /\
    param_insts_from k users /\
    canonical_entry_params_from (k + LENGTH users) suffix ==>
    canonical_entry_params_from k (users ++ suffix)
Proof
  Induct_on `users`
  >> simp[canonical_entry_params_from_def, param_insts_from_def,
          arithmeticTheory.ADD_CLAUSES]
QED

Theorem canonical_entry_params_from_hidden_suffix:
  !k fmp retpc body.
    (fmp = [] \/ ?inst. fmp = [inst] /\
                         inst.inst_opcode = FMP_PARAM) /\
    (retpc = [] \/ ?inst. retpc = [inst] /\
                            inst.inst_opcode = RETPC_PARAM) /\
    param_insts_from k (fmp ++ retpc) /\
    no_param_insts body ==>
    canonical_entry_params_from k (fmp ++ retpc ++ body)
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >> simp[canonical_entry_params_from_def, canonical_after_fmp_def,
          param_insts_from_def, no_param_insts_def, is_param_opcode_iff,
          listTheory.APPEND_NIL]
  >> Cases_on `body`
  >> gvs[canonical_entry_params_from_def, canonical_after_fmp_def,
         no_param_insts_def, param_insts_from_def, is_param_opcode_iff]
QED

Theorem canonical_entry_params_from_complete:
  !k users fmp retpc body.
    EVERY (\inst. inst.inst_opcode = PARAM) users /\
    (fmp = [] \/ ?inst. fmp = [inst] /\
                         inst.inst_opcode = FMP_PARAM) /\
    (retpc = [] \/ ?inst. retpc = [inst] /\
                            inst.inst_opcode = RETPC_PARAM) /\
    param_insts_from k (users ++ fmp ++ retpc) /\
    no_param_insts body ==>
    canonical_entry_params_from k (users ++ fmp ++ retpc ++ body)
Proof
  rpt gen_tac >> strip_tac
  >> `param_insts_from k (users ++ (fmp ++ retpc))` by
       gvs[listTheory.APPEND_ASSOC]
  >> drule (iffLR param_insts_from_append)
  >> strip_tac
  >> `canonical_entry_params_from (k + LENGTH users)
        (fmp ++ retpc ++ body)` by
       (irule canonical_entry_params_from_hidden_suffix >> simp[])
  >> `canonical_entry_params_from k
        (users ++ (fmp ++ retpc ++ body))` by
       (irule canonical_entry_params_from_prepend_users
        >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >> qpat_x_assum
       `canonical_entry_params_from k (users ++ (fmp ++ retpc ++ body))`
       mp_tac
  >> pure_rewrite_tac[listTheory.APPEND_ASSOC]
  >> simp[]
QED
Theorem canonical_entry_params_from_iff:
  !k insts.
    canonical_entry_params_from k insts <=>
    ?users fmp retpc body.
      insts = users ++ fmp ++ retpc ++ body /\
      EVERY (\inst. inst.inst_opcode = PARAM) users /\
      (fmp = [] \/ ?inst. fmp = [inst] /\
                           inst.inst_opcode = FMP_PARAM) /\
      (retpc = [] \/ ?inst. retpc = [inst] /\
                              inst.inst_opcode = RETPC_PARAM) /\
      param_insts_from k (users ++ fmp ++ retpc) /\
      no_param_insts body
Proof
  rpt gen_tac >> eq_tac
  >- (strip_tac
      >> drule canonical_entry_params_from_sound
      >> simp[])
  >> strip_tac
  >> qpat_x_assum `insts = _` SUBST_ALL_TAC
  >> irule canonical_entry_params_from_complete
  >> metis_tac[]
QED

Theorem canonical_param_prefix_iff:
  canonical_param_prefix fn <=>
  ?entry rest users fmp retpc body.
    fn.fn_blocks = entry::rest /\
    entry.bb_instructions = users ++ fmp ++ retpc ++ body /\
    EVERY (\inst. inst.inst_opcode = PARAM) users /\
    (fmp = [] \/ ?inst. fmp = [inst] /\
                         inst.inst_opcode = FMP_PARAM) /\
    (retpc = [] \/ ?inst. retpc = [inst] /\
                            inst.inst_opcode = RETPC_PARAM) /\
    param_insts_from 0 (users ++ fmp ++ retpc) /\
    no_param_insts body /\
    EVERY (\bb. no_param_insts bb.bb_instructions) rest
Proof
  Cases_on `fn.fn_blocks`
  >> simp[canonical_param_prefix_def, canonical_entry_params_from_iff]
  >> metis_tac[]
QED


Definition OPTION_TO_LIST_def:
  (OPTION_TO_LIST (NONE : 'a option) = []) /\
  (OPTION_TO_LIST (SOME x) = [x])
End

Theorem FIND_APPEND_CASE:
  !P xs ys.
    FIND P (xs ++ ys) =
      case FIND P xs of
        NONE => FIND P ys
      | SOME x => SOME x
Proof
  Induct_on `xs` >> simp[listTheory.FIND_thm]
  >> rpt gen_tac >> Cases_on `P h` >> simp[]
QED

Theorem every_user_param_queries:
  !insts.
    EVERY (\inst. inst.inst_opcode = PARAM) insts ==>
    FILTER (\inst. inst.inst_opcode = PARAM) insts = insts /\
    FIND (\inst. inst.inst_opcode = FMP_PARAM) insts = NONE /\
    FIND (\inst. inst.inst_opcode = RETPC_PARAM) insts = NONE
Proof
  Induct >> simp[listTheory.FIND_thm]
QED

Theorem no_param_insts_queries:
  !insts.
    no_param_insts insts ==>
    FILTER (\inst. inst.inst_opcode = PARAM) insts = [] /\
    FIND (\inst. inst.inst_opcode = FMP_PARAM) insts = NONE /\
    FIND (\inst. inst.inst_opcode = RETPC_PARAM) insts = NONE
Proof
  Induct >> simp[no_param_insts_def, listTheory.FIND_thm]
  >> rpt gen_tac >> Cases_on `h.inst_opcode`
  >> simp[is_param_opcode_def]
QED
Theorem canonical_phase_queries:
  !insts users fmp retpc body.
    insts = users ++ fmp ++ retpc ++ body /\
    EVERY (\inst. inst.inst_opcode = PARAM) users /\
    (fmp = [] \/ ?inst. fmp = [inst] /\
                         inst.inst_opcode = FMP_PARAM) /\
    (retpc = [] \/ ?inst. retpc = [inst] /\
                            inst.inst_opcode = RETPC_PARAM) /\
    no_param_insts body ==>
    FILTER (\inst. inst.inst_opcode = PARAM) insts = users /\
    OPTION_TO_LIST (FIND (\inst. inst.inst_opcode = FMP_PARAM) insts) = fmp /\
    OPTION_TO_LIST (FIND (\inst. inst.inst_opcode = RETPC_PARAM) insts) = retpc
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >> drule every_user_param_queries
  >> drule no_param_insts_queries
  >> simp[FIND_APPEND_CASE, listTheory.FIND_thm,
          listTheory.FILTER_APPEND_DISTRIB, OPTION_TO_LIST_def]
QED

Theorem canonical_phase_split_unique:
  !insts users fmp retpc body users' fmp' retpc' body'.
    insts = users ++ fmp ++ retpc ++ body /\
    EVERY (\inst. inst.inst_opcode = PARAM) users /\
    (fmp = [] \/ ?inst. fmp = [inst] /\
                         inst.inst_opcode = FMP_PARAM) /\
    (retpc = [] \/ ?inst. retpc = [inst] /\
                            inst.inst_opcode = RETPC_PARAM) /\
    no_param_insts body /\
    insts = users' ++ fmp' ++ retpc' ++ body' /\
    EVERY (\inst. inst.inst_opcode = PARAM) users' /\
    (fmp' = [] \/ ?inst. fmp' = [inst] /\
                          inst.inst_opcode = FMP_PARAM) /\
    (retpc' = [] \/ ?inst. retpc' = [inst] /\
                             inst.inst_opcode = RETPC_PARAM) /\
    no_param_insts body' ==>
    users = users' /\ fmp = fmp' /\ retpc = retpc' /\ body = body'
Proof
  rpt gen_tac >> strip_tac
  >> `FILTER (\inst. inst.inst_opcode = PARAM) insts = users /\
      OPTION_TO_LIST (FIND (\inst. inst.inst_opcode = FMP_PARAM) insts) = fmp /\
      OPTION_TO_LIST (FIND (\inst. inst.inst_opcode = RETPC_PARAM) insts) = retpc` by
       (irule canonical_phase_queries >> metis_tac[])
  >> `FILTER (\inst. inst.inst_opcode = PARAM) insts = users' /\
      OPTION_TO_LIST (FIND (\inst. inst.inst_opcode = FMP_PARAM) insts) = fmp' /\
      OPTION_TO_LIST (FIND (\inst. inst.inst_opcode = RETPC_PARAM) insts) = retpc'` by
       (irule canonical_phase_queries >> metis_tac[])
  >> gvs[]
QED

Theorem canonical_param_prefix_queries:
  !fn entry rest users fmp retpc body.
    canonical_param_prefix fn /\
    fn.fn_blocks = entry::rest /\
    entry.bb_instructions = users ++ fmp ++ retpc ++ body /\
    EVERY (\inst. inst.inst_opcode = PARAM) users /\
    (fmp = [] \/ ?inst. fmp = [inst] /\
                         inst.inst_opcode = FMP_PARAM) /\
    (retpc = [] \/ ?inst. retpc = [inst] /\
                            inst.inst_opcode = RETPC_PARAM) /\
    no_param_insts body ==>
    fn_user_param_insts fn = users /\
    OPTION_TO_LIST (fn_hidden_fmp_param fn) = fmp /\
    OPTION_TO_LIST (fn_retpc_param fn) = retpc /\
    LENGTH (fn_user_param_insts fn) = LENGTH users
Proof
  rpt gen_tac >> strip_tac
  >> `FILTER (\inst. inst.inst_opcode = PARAM)
             (users ++ fmp ++ retpc ++ body) = users /\
      OPTION_TO_LIST
        (FIND (\inst. inst.inst_opcode = FMP_PARAM)
              (users ++ fmp ++ retpc ++ body)) = fmp /\
      OPTION_TO_LIST
        (FIND (\inst. inst.inst_opcode = RETPC_PARAM)
              (users ++ fmp ++ retpc ++ body)) = retpc` by
       (irule canonical_phase_queries >> metis_tac[])
  >> `fn_entry_insts fn = users ++ fmp ++ retpc ++ body` by
       simp[fn_entry_insts_def, entry_block_def]
  >> `fn_user_param_insts fn = users` by
       (rewrite_tac[fn_user_param_insts_def]
        >> qpat_assum `fn_entry_insts fn = _` (fn th => rewrite_tac[th])
        >> qpat_assum `FILTER (\inst. inst.inst_opcode = PARAM) _ = users`
             ACCEPT_TAC)
  >> `OPTION_TO_LIST (fn_hidden_fmp_param fn) = fmp` by
       (rewrite_tac[fn_hidden_fmp_param_def]
        >> qpat_assum `fn_entry_insts fn = _` (fn th => rewrite_tac[th])
        >> qpat_assum `OPTION_TO_LIST (FIND (\inst. inst.inst_opcode = FMP_PARAM) _) = fmp`
             ACCEPT_TAC)
  >> `OPTION_TO_LIST (fn_retpc_param fn) = retpc` by
       (rewrite_tac[fn_retpc_param_def]
        >> qpat_assum `fn_entry_insts fn = _` (fn th => rewrite_tac[th])
        >> qpat_assum `OPTION_TO_LIST (FIND (\inst. inst.inst_opcode = RETPC_PARAM) _) = retpc`
             ACCEPT_TAC)
  >> simp[]
QED

Theorem param_insts_from_erase:
  !k insts.
    param_insts_from k insts ==>
    MAP erase_param_index insts =
      MAP (\inst. inst with inst_operands := []) insts
Proof
  Induct_on `insts` >- simp[param_insts_from_def]
  >> rpt gen_tac >> simp[param_insts_from_def] >> strip_tac
  >> first_x_assum drule >> disch_then assume_tac
  >> gvs[param_inst_at_def, erase_param_index_def]
QED

Theorem canonical_phase_erase:
  !k users fmp retpc.
    param_insts_from k (users ++ fmp ++ retpc) ==>
    MAP erase_param_index (users ++ fmp ++ retpc) =
      MAP (\inst. inst with inst_operands := [])
          (users ++ fmp ++ retpc)
Proof
  metis_tac[param_insts_from_erase]
QED


Theorem take_length_append_eq:
  !xs ys. TAKE (LENGTH xs) (xs ++ ys) = xs
Proof
  Induct >> simp[]
QED
Theorem canonical_param_prefix_erase:
  !fn entry rest users fmp retpc body.
    canonical_param_prefix fn /\
    fn.fn_blocks = entry::rest /\
    entry.bb_instructions = users ++ fmp ++ retpc ++ body /\
    param_insts_from 0 (users ++ fmp ++ retpc) ==>
    MAP erase_param_index
        (TAKE (LENGTH (users ++ fmp ++ retpc))
              (fn_entry_insts fn)) =
      MAP (\inst. inst with inst_operands := [])
          (users ++ fmp ++ retpc)
Proof
  rpt gen_tac >> strip_tac
  >> `fn_entry_insts fn = users ++ fmp ++ retpc ++ body` by
       simp[fn_entry_insts_def, entry_block_def]
  >> `TAKE (LENGTH (users ++ fmp ++ retpc)) (fn_entry_insts fn) =
      users ++ fmp ++ retpc` by
       (qpat_x_assum `fn_entry_insts fn = _` (fn th => rewrite_tac[th])
        >> irule take_length_append_eq)
  >> drule canonical_phase_erase >> disch_then assume_tac
  >> simp[]
QED

Definition is_raw_return_opcode_def:
  is_raw_return_opcode op <=>
    op = RET \/ op = RETFMP \/ op = DRET
End

Definition raw_return_user_arity_def:
  raw_return_user_arity inst =
    case inst.inst_opcode of
      RET => if NULL inst.inst_operands then NONE
             else SOME (LENGTH inst.inst_operands - 1)
    | RETFMP => if NULL inst.inst_operands then NONE
                else SOME (LENGTH inst.inst_operands - 1)
    | DRET => OPTION_MAP (\p. FST p + SND p) (parse_dret_shape inst)
    | _ => NONE
End

Definition fn_return_insts_def:
  fn_return_insts fn =
    FILTER (\inst. is_raw_return_opcode inst.inst_opcode)
      (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks))
End

Definition fn_unique_return_arity_def:
  fn_unique_return_arity fn =
    case fn_return_insts fn of
      [] => NONE
    | first::rest =>
        case raw_return_user_arity first of
          NONE => NONE
        | SOME n =>
            if EVERY (\inst. raw_return_user_arity inst = SOME n) rest
            then SOME n else NONE
End

Definition fn_memory_return_buffer_param_def:
  fn_memory_return_buffer_param fn =
    if fn.fn_call_abi.ica_has_memory_return_buffer = SOME T then
      case fn_user_param_insts fn of
        [] => NONE
      | inst::_ => SOME inst
    else NONE
End

Definition fn_return_abi_matches_def:
  fn_return_abi_matches fn <=>
    case fn_unique_return_arity fn of
      NONE => F
    | SOME n =>
        (fn.fn_call_abi.ica_user_return_count = NONE \/
         fn.fn_call_abi.ica_user_return_count = SOME n) /\
        (fn.fn_call_abi.ica_has_memory_return_buffer = SOME T ==>
         fn_memory_return_buffer_param fn <> NONE)
End

Theorem raw_return_user_arity_RET:
  raw_return_user_arity (inst with inst_opcode := RET) =
    if NULL inst.inst_operands then NONE
    else SOME (LENGTH inst.inst_operands - 1)
Proof
  simp[raw_return_user_arity_def]
QED

Theorem raw_return_user_arity_RETFMP:
  raw_return_user_arity (inst with inst_opcode := RETFMP) =
    if NULL inst.inst_operands then NONE
    else SOME (LENGTH inst.inst_operands - 1)
Proof
  simp[raw_return_user_arity_def]
QED

Theorem raw_return_user_arity_DRET:
  raw_return_user_arity (inst with inst_opcode := DRET) =
    OPTION_MAP (\p. FST p + SND p)
      (parse_dret_shape (inst with inst_opcode := DRET))
Proof
  simp[raw_return_user_arity_def]
QED

Theorem raw_return_user_arity_DRET_some:
  parse_dret_shape (inst with inst_opcode := DRET) = SOME (ordinary,dynamic) ==>
  raw_return_user_arity (inst with inst_opcode := DRET) =
    SOME (ordinary + dynamic)
Proof
  simp[raw_return_user_arity_DRET]
QED
Theorem raw_return_user_arity_DRET_length:
  raw_return_user_arity (inst with inst_opcode := DRET) = SOME n ==>
  ?ordinary dynamic.
    n = ordinary + dynamic /\
    LENGTH inst.inst_operands = 2 + ordinary + 2 * dynamic
Proof
  simp[raw_return_user_arity_DRET]
  >> Cases_on `parse_dret_shape (inst with inst_opcode := DRET)`
  >> simp[] >> PairCases_on `x` >> simp[] >> strip_tac
  >> drule parse_dret_shape_length >> strip_tac
  >> qexistsl [`x0`, `x1`] >> gvs[] >> decide_tac
QED

Theorem fn_memory_return_buffer_param_some:
  fn_memory_return_buffer_param fn = SOME inst ==>
  fn.fn_call_abi.ica_has_memory_return_buffer = SOME T /\
  ?rest. fn_user_param_insts fn = inst::rest
Proof
  simp[fn_memory_return_buffer_param_def]
  >> Cases_on `fn.fn_call_abi.ica_has_memory_return_buffer = SOME T`
  >> simp[]
  >> Cases_on `fn_user_param_insts fn` >> simp[]
QED

Theorem fn_return_abi_matches_iff:
  fn_return_abi_matches fn <=>
    ?n. fn_unique_return_arity fn = SOME n /\
        (fn.fn_call_abi.ica_user_return_count = NONE \/
         fn.fn_call_abi.ica_user_return_count = SOME n) /\
        (fn.fn_call_abi.ica_has_memory_return_buffer = SOME T ==>
         IS_SOME (fn_memory_return_buffer_param fn))
Proof
  Cases_on `fn_unique_return_arity fn`
  >> Cases_on `fn_memory_return_buffer_param fn`
  >> simp[fn_return_abi_matches_def]
QED

Definition fn_expected_user_return_arity_def:
  fn_expected_user_return_arity fn =
    case fn.fn_call_abi.ica_user_return_count of
      SOME n => SOME n
    | NONE => fn_unique_return_arity fn
End

Definition invoke_input_arity_ok_def:
  invoke_input_arity_ok callee sig inst <=>
    inst.inst_opcode = INVOKE /\
    case inst.inst_operands of
      Label callee_name::args =>
        LENGTH args = LENGTH (fn_user_param_insts callee) +
          (if sig.fms_has_fmp_param then 1 else 0)
    | _ => F
End

Definition invoke_output_arity_ok_def:
  invoke_output_arity_ok callee sig inst <=>
    inst.inst_opcode = INVOKE /\
    (case inst.inst_operands of Label callee_name::args => T | _ => F) /\
    case fn_expected_user_return_arity callee of
      NONE => F
    | SOME n =>
        LENGTH inst.inst_outputs =
          n + (if sig.fms_publishes then 1 else 0)
End

Theorem invoke_input_arity_ok_iff:
  invoke_input_arity_ok callee sig inst <=>
    inst.inst_opcode = INVOKE /\
    ?callee_name args.
      inst.inst_operands = Label callee_name::args /\
      LENGTH args = LENGTH (fn_user_param_insts callee) +
        (if sig.fms_has_fmp_param then 1 else 0)
Proof
  simp[invoke_input_arity_ok_def]
  >> Cases_on `inst.inst_operands` >> simp[]
  >> Cases_on `h` >> simp[]
QED

Theorem invoke_output_arity_ok_iff:
  invoke_output_arity_ok callee sig inst <=>
    inst.inst_opcode = INVOKE /\
    (?callee_name args. inst.inst_operands = Label callee_name::args) /\
    ?n. fn_expected_user_return_arity callee = SOME n /\
        LENGTH inst.inst_outputs =
          n + (if sig.fms_publishes then 1 else 0)
Proof
  simp[invoke_output_arity_ok_def]
  >> Cases_on `inst.inst_operands` >> simp[]
  >> Cases_on `h` >> simp[]
  >> Cases_on `fn_expected_user_return_arity callee` >> simp[]
QED

(* A lowered return has an exact user prefix of length [n], followed by
 * either just RETPC or an adopted-FMP value immediately before RETPC.
 * TAKE/DROP keep this predicate executable while exposing an append witness
 * through the interface theorems below. *)
Definition lowered_return_inst_layout_wf_def:
  lowered_return_inst_layout_wf publishes n inst <=>
    inst.inst_opcode = RET /\
    LENGTH (TAKE n inst.inst_operands) = n /\
    DROP n inst.inst_operands =
      if publishes then
        [EL n inst.inst_operands; LAST inst.inst_operands]
      else
        [LAST inst.inst_operands]
End

Definition lowered_return_layout_wf_def:
  lowered_return_layout_wf sig fn <=>
    case fn_expected_user_return_arity fn of
      NONE => F
    | SOME n =>
        EVERY (lowered_return_inst_layout_wf sig.fms_publishes n)
          (fn_return_insts fn)
End

Theorem lowered_return_inst_layout_wf_nonpublishing:
  lowered_return_inst_layout_wf F n inst ==>
  ?users rpc.
    inst.inst_operands = users ++ [rpc] /\ LENGTH users = n
Proof
  simp[lowered_return_inst_layout_wf_def] >> strip_tac
  >> qexistsl [`TAKE n inst.inst_operands`, `LAST inst.inst_operands`]
  >> simp[]
  >> metis_tac[listTheory.TAKE_DROP]
QED

Theorem lowered_return_inst_layout_wf_publishing:
  lowered_return_inst_layout_wf T n inst ==>
  ?users adopted_fmp rpc.
    inst.inst_operands = users ++ [adopted_fmp; rpc] /\ LENGTH users = n
Proof
  simp[lowered_return_inst_layout_wf_def] >> strip_tac
  >> qexistsl [`TAKE n inst.inst_operands`, `EL n inst.inst_operands`,
               `LAST inst.inst_operands`]
  >> simp[]
  >> metis_tac[listTheory.TAKE_DROP]
QED

Theorem lowered_return_inst_layout_wf_length:
  lowered_return_inst_layout_wf publishes n inst ==>
  LENGTH inst.inst_operands = n + (if publishes then 2 else 1)
Proof
  Cases_on `publishes`
  >- (strip_tac >> drule lowered_return_inst_layout_wf_publishing
      >> strip_tac >> simp[])
  >> strip_tac >> drule lowered_return_inst_layout_wf_nonpublishing
  >> strip_tac >> simp[]
QED

Theorem lowered_return_layout_wf_iff:
  lowered_return_layout_wf sig fn <=>
  ?n. fn_expected_user_return_arity fn = SOME n /\
      !inst. MEM inst (fn_return_insts fn) ==>
             lowered_return_inst_layout_wf sig.fms_publishes n inst
Proof
  Cases_on `fn_expected_user_return_arity fn`
  >> simp[lowered_return_layout_wf_def, listTheory.EVERY_MEM]
QED

Theorem lowered_return_layout_wf_inst:
  lowered_return_layout_wf sig fn /\
  MEM inst (fn_return_insts fn) ==>
  ?n. fn_expected_user_return_arity fn = SOME n /\
      lowered_return_inst_layout_wf sig.fms_publishes n inst
Proof
  metis_tac[lowered_return_layout_wf_iff]
QED

Theorem lowered_return_layout_wf_length:
  lowered_return_layout_wf sig fn /\
  MEM inst (fn_return_insts fn) ==>
  ?n. fn_expected_user_return_arity fn = SOME n /\
      LENGTH inst.inst_operands =
        n + (if sig.fms_publishes then 2 else 1)
Proof
  strip_tac
  >> drule (iffLR lowered_return_layout_wf_iff) >> strip_tac
  >> qexists `n` >> simp[]
  >> irule lowered_return_inst_layout_wf_length
  >> first_x_assum irule >> simp[]
QED
val _ = export_theory();
