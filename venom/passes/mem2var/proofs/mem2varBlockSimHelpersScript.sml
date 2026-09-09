Theory mem2varBlockSimHelpers
Ancestors
  mem2varProofs passSharedFrame passSharedTransfer passSharedField instIdxIndep
  venomMemProps venomMemProofs venomExecProofs venomInstProofs
  mem2varDefs
  venomExecSemantics venomState venomWf
  venomInst
  stateEquiv
  passSimulationDefs passSimulationProps
  analysisSimDefs
  dfgDefs dfgCorrectnessProof
  basePtrDefs basePtrProofs
  pointerConfinedDefs memLocDefs
  venomEffects venomMemDefs
  finite_map list rich_list pred_set pair
Libs
  HolKernel boolLib bossLib BasicProvers dep_rewrite markerLib

(* ================================================================
   FLAT MAP INDEX LEMMAS
   ================================================================ *)

Theorem FLAT_MAP_SING_EL:
  !f xs i. EVERY (\x. LENGTH (f x) = 1) xs /\ i < LENGTH xs ==>
    EL i (FLAT (MAP f xs)) = HD (f (EL i xs))
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  Cases_on `i` >> simp[]
  >- (Cases_on `f h` >> gvs[]) >>
  `LENGTH (f h) = 1` by gvs[] >>
  Cases_on `f h` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem FLAT_MAP_SING_LENGTH:
  !f xs. EVERY (\x. LENGTH (f x) = 1) xs ==>
    LENGTH (FLAT (MAP f xs)) = LENGTH xs
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  `LENGTH (f h) = 1` by gvs[] >>
  Cases_on `f h` >> gvs[]
QED

Theorem FLAT_MAP_FRONT_SING_EL:
  !f xs i. i < LENGTH xs - 1 /\
    EVERY (\x. LENGTH (f x) = 1) (FRONT xs) /\ xs <> [] ==>
    EL i (FLAT (MAP f xs)) = HD (f (EL i xs))
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  Cases_on `i`
  >- (Cases_on `f h` >> gvs[FRONT_DEF] >>
      Cases_on `xs` >> gvs[]) >>
  rename1 `SUC n < LENGTH xs` >>
  `LENGTH (f h) = 1` by
    (Cases_on `xs` >> gvs[FRONT_DEF]) >>
  Cases_on `f h` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  Cases_on `xs` >> gvs[FRONT_DEF]
QED

(* FRONT all singletons, every element >= 1: total length >= list length *)
Theorem FLAT_MAP_FRONT_SING_LENGTH_GE:
  !f xs. EVERY (\x. LENGTH (f x) = 1) (FRONT xs) /\ xs <> [] /\
    EVERY (\x. 1 <= LENGTH (f x)) xs ==>
    LENGTH xs <= LENGTH (FLAT (MAP f xs))
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  Cases_on `xs`
  >- gvs[] >>
  `LENGTH (f h) = 1` by gvs[FRONT_DEF] >>
  Cases_on `f h` >> gvs[] >>
  first_x_assum (qspec_then `f` mp_tac) >>
  impl_tac >- (Cases_on `t` >> gvs[FRONT_DEF]) >>
  simp[]
QED

(* ================================================================
   m2v_rewrite_inst: the per-instruction rewrite function
   ================================================================ *)

Definition m2v_rewrite_inst_def:
  m2v_rewrite_inst fn (i : instruction) =
    case FIND (\(ao, _, _). MEM (Var ao) i.inst_operands) (m2v_promo_list fn) of
      SOME (ao, pvar, sz) => m2v_promote_inst pvar ao sz i
    | NONE => [i]
End

Theorem m2v_bt_instructions:
  !fn bb.
    (m2v_bt fn bb).bb_instructions =
    FLAT (MAP (m2v_rewrite_inst fn) bb.bb_instructions)
Proof
  rpt gen_tac >> simp[m2v_bt_def, LET_THM] >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, m2v_rewrite_inst_def]
QED

(* Non-terminal instructions always rewrite to exactly 1 instruction *)
Theorem m2v_rewrite_inst_len1_nonterm:
  !fn i. ~is_terminator i.inst_opcode ==>
    LENGTH (m2v_rewrite_inst fn i) = 1
Proof
  rpt strip_tac >> simp[m2v_rewrite_inst_def] >>
  CASE_TAC >> simp[] >>
  PairCases_on `x` >> simp[] >>
  simp[m2v_promote_inst_def] >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[is_terminator_def]) >>
  gvs[is_terminator_def]
QED

(* FRONT of a well-formed block's instructions are non-terminators *)
Theorem wf_block_front_nonterm:
  !bb. bb_well_formed bb ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  simp[EVERY_EL, LENGTH_FRONT] >> rpt strip_tac >>
  `EL n (FRONT bb.bb_instructions) = EL n bb.bb_instructions` by
    (irule EL_FRONT >> simp[LENGTH_FRONT, NULL_EQ]) >>
  gvs[] >>
  `n < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  res_tac >> gvs[]
QED

(* Every rewrite produces at least 1 instruction *)
Theorem m2v_rewrite_inst_len_ge1:
  !fn i. 1 <= LENGTH (m2v_rewrite_inst fn i)
Proof
  rpt strip_tac >> simp[m2v_rewrite_inst_def] >>
  CASE_TAC >> simp[] >>
  PairCases_on `x` >> simp[] >>
  simp[m2v_promote_inst_def] >>
  rpt (CASE_TAC >> gvs[])
QED

(* For a well-formed block, all non-terminal rewrites are singletons *)
Theorem m2v_rewrite_front_sing:
  !fn bb. bb_well_formed bb ==>
    EVERY (\i. LENGTH (m2v_rewrite_inst fn i) = 1)
      (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  drule wf_block_front_nonterm >> strip_tac >>
  irule EVERY_MONOTONIC >> qexists `\i. ~is_terminator i.inst_opcode` >>
  simp[] >> metis_tac[m2v_rewrite_inst_len1_nonterm]
QED

(* When FRONT elements map to singletons, index into the LAST element's expansion *)
Theorem FLAT_MAP_FRONT_SING_LAST_EL:
  !f xs j. xs <> [] /\
    EVERY (\x. LENGTH (f x) = 1) (FRONT xs) /\
    j < LENGTH (f (LAST xs)) ==>
    EL (LENGTH xs - 1 + j) (FLAT (MAP f xs)) = EL j (f (LAST xs))
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  Cases_on `xs = []`
  >- gvs[FRONT_DEF, LAST_DEF] >>
  `LENGTH (f h) = 1` by (Cases_on `xs` >> gvs[FRONT_DEF]) >>
  Cases_on `f h` >> gvs[] >>
  `LAST (h::xs) = LAST xs` by (Cases_on `xs` >> gvs[LAST_DEF]) >>
  gvs[] >>
  `EVERY (\x. LENGTH (f x) = 1) (FRONT xs)` by
    (Cases_on `xs` >> gvs[FRONT_DEF]) >>
  first_x_assum drule >> disch_then drule >>
  `j + LENGTH xs = SUC (LENGTH xs - 1 + j)` by
    (Cases_on `xs` >> gvs[]) >>
  pop_assum SUBST1_TAC >> simp[]
QED

(* In a well-formed block, get_instruction on m2v_bt matches for
   non-terminal indices (0 .. LENGTH - 2) *)
Theorem m2v_bt_get_inst_nonterm:
  !fn bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions - 1 ==>
    get_instruction (m2v_bt fn bb) i =
    SOME (HD (m2v_rewrite_inst fn (EL i bb.bb_instructions)))
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by
    (fs[bb_well_formed_def] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EVERY (\x. LENGTH (m2v_rewrite_inst fn x) = 1)
    (FRONT bb.bb_instructions)` by
    metis_tac[m2v_rewrite_front_sing] >>
  `EL i (FLAT (MAP (m2v_rewrite_inst fn) bb.bb_instructions)) =
   HD (m2v_rewrite_inst fn (EL i bb.bb_instructions))` by
    (irule FLAT_MAP_FRONT_SING_EL >> simp[]) >>
  `LENGTH bb.bb_instructions <=
   LENGTH (FLAT (MAP (m2v_rewrite_inst fn) bb.bb_instructions))` by
    (irule FLAT_MAP_FRONT_SING_LENGTH_GE >>
     simp[EVERY_MEM, m2v_rewrite_inst_len_ge1]) >>
  `i < LENGTH (FLAT (MAP (m2v_rewrite_inst fn) bb.bb_instructions))` by
    simp[] >>
  simp[get_instruction_def, m2v_bt_instructions]
QED

(* For well-formed blocks, get_instruction on m2v_bt at the terminal index:
   index (LENGTH bb.bb_instructions - 1 + j) gives EL j of the
   terminal instruction's rewrite. *)
Theorem m2v_bt_get_inst_term:
  !fn bb j. bb_well_formed bb /\
    j < LENGTH (m2v_rewrite_inst fn (LAST bb.bb_instructions)) ==>
    get_instruction (m2v_bt fn bb) (LENGTH bb.bb_instructions - 1 + j) =
    SOME (EL j (m2v_rewrite_inst fn (LAST bb.bb_instructions)))
Proof
  rpt strip_tac >>
  (SUBGOAL_THEN ``bb.bb_instructions <> []`` assume_tac
   >- (fs[bb_well_formed_def] >> Cases_on `bb.bb_instructions` >> gvs[])) >>
  drule m2v_rewrite_front_sing >> disch_then (qspec_then `fn` assume_tac) >>
  rewrite_tac[get_instruction_def, m2v_bt_instructions] >> simp[] >>
  SUBGOAL_THEN ``LENGTH (FLAT (MAP (m2v_rewrite_inst fn)
    bb.bb_instructions)) = LENGTH bb.bb_instructions - 1 +
    LENGTH (m2v_rewrite_inst fn (LAST bb.bb_instructions))``
    assume_tac
  >- (SUBGOAL_THEN ``bb.bb_instructions = FRONT bb.bb_instructions ++
        [LAST bb.bb_instructions]``
        (fn th => ONCE_REWRITE_TAC[th])
      >- metis_tac[APPEND_FRONT_LAST] >>
      simp[MAP_APPEND, FLAT_APPEND, FLAT_MAP_SING_LENGTH, LENGTH_FRONT]) >>
  conj_tac >- simp[] >>
  irule FLAT_MAP_FRONT_SING_LAST_EL >> simp[]
QED

(* PRE-based variant of m2v_bt_get_inst_term: avoids PRE vs minus-1 mismatch *)
Theorem m2v_bt_get_inst_pre:
  !fn bb j. bb_well_formed bb /\
    j < LENGTH (m2v_rewrite_inst fn (LAST bb.bb_instructions)) ==>
    get_instruction (m2v_bt fn bb) (PRE (LENGTH bb.bb_instructions) + j) =
    SOME (EL j (m2v_rewrite_inst fn (LAST bb.bb_instructions)))
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by
    (gvs[bb_well_formed_def] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `PRE (LENGTH bb.bb_instructions) = LENGTH bb.bb_instructions - 1` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  mp_tac (Q.SPECL [`fn`,`bb`,`j`] m2v_bt_get_inst_term) >> simp[]
QED

(* ================================================================
   EXEC_BLOCK PREFIX FACTORING
   ================================================================ *)

(* step_inst idx independence for non-terminator non-INVOKE *)
Theorem step_inst_idx_indep_local:
  !fuel ctx inst s n.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (step_inst fuel ctx inst s)
Proof
  rw[step_inst_non_invoke, step_inst_inst_idx_indep]
QED

(* Skip prefix: if run_insts returns OK, exec_block can skip ahead *)
Theorem exec_block_skip_prefix:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      prefix /\
    (!k. k < LENGTH prefix ==>
         EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s' ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep_local] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`,
    `SUC j`, `s'`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac >- (rw[] >>
    first_x_assum (qspec_then `SUC k` mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES]) >>
  simp[]
QED

(* Error propagation: if run_insts returns Error, exec_block does too *)
Theorem exec_block_prefix_error:
  !prefix fuel ctx bb s j e.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      prefix /\
    (!k. k < LENGTH prefix ==>
         EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Error e ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) = Error e
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `h :: prefix` >>
  fs[EVERY_DEF] >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep_local] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[exec_result_map_def, Once run_insts_def] >>
  rename1 `step_inst _ _ h s = OK s'` >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s'`,
    `SUC j`, `e`] mp_tac) >>
  simp[] >> impl_tac >- (simp[] >> rpt strip_tac >>
    first_x_assum (qspec_then `SUC k` mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES]) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

(* ================================================================
   INTRA-BLOCK INVARIANT
   Like m2v_inv but without vs_inst_idx constraint.
   ================================================================ *)

Definition m2v_inv_noix_def:
  m2v_inv_noix fn s1 s2 <=>
    (!v. v NOTIN m2v_fresh_vars fn ==>
         lookup_var v s1 = lookup_var v s2) /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_transient = s2.vs_transient /\
    (s1.vs_halted <=> s2.vs_halted) /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    allocas_non_overlapping s1 /\
    (!i. ~in_promoted_region fn s1 i ==>
         mem_byte i s1 = mem_byte i s2) /\
    (* Bridge: each promo entry's ao maps to its alloca's inst_id in vs_allocas *)
    (!ao pvar sz inst.
       MEM (ao, pvar, sz) (m2v_promo_list fn) /\
       MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_outputs = [ao] ==>
       !addr. lookup_var ao s1 = SOME addr ==>
       FLOOKUP s1.vs_allocas inst.inst_id = SOME (w2n addr, sz)) /\
    (* Sync: promoted variable tracks memory cell *)
    (!ao pvar sz.
       MEM (ao, pvar, sz) (m2v_promo_list fn) ==>
       !addr. lookup_var ao s1 = SOME addr ==>
         IS_SOME (lookup_var pvar s2) ==>
         lookup_var pvar s2 = SOME (mload (w2n addr) s1))
End

(* Tracks which promoted pvars have been set via dominating MSTOREs.
   Two parts:
   1. Cross-block: if a dominating block has MSTORE to ao, pvar is set
   2. Same-block: if MSTORE to ao at j < idx in bb, pvar is set
   Vacuously true at idx=0 IF no cross-block stores (which holds at fn entry). *)
Definition m2v_pvars_set_def:
  m2v_pvars_set fn bb idx s <=>
    !ao pvar sz.
      MEM (ao,pvar,sz) (m2v_promo_list fn) /\ sz = 32 ==>
      (* Cross-block domination: dominating block has a store *)
      ((!store_bb store_inst.
         MEM store_bb fn.fn_blocks /\
         MEM store_inst store_bb.bb_instructions /\
         store_inst.inst_opcode = MSTORE /\
         MEM (Var ao) store_inst.inst_operands /\
         fn_dominates fn store_bb.bb_label bb.bb_label /\
         store_bb <> bb ==>
         IS_SOME (lookup_var pvar s)) /\
      (* Same-block: store before index *)
      (!j. j < idx /\ j < LENGTH bb.bb_instructions /\
           (EL j bb.bb_instructions).inst_opcode = MSTORE /\
           MEM (Var ao) (EL j bb.bb_instructions).inst_operands ==>
           IS_SOME (lookup_var pvar s)))
End

(* m2v_pvars_set at idx=0 with no cross-block stores *)
Theorem m2v_pvars_set_init:
  !fn bb s.
    (!ao pvar sz.
       MEM (ao,pvar,sz) (m2v_promo_list fn) /\ sz = 32 ==>
       !store_bb store_inst.
         MEM store_bb fn.fn_blocks /\
         MEM store_inst store_bb.bb_instructions /\
         store_inst.inst_opcode = MSTORE /\
         MEM (Var ao) store_inst.inst_operands /\
         fn_dominates fn store_bb.bb_label bb.bb_label /\
         store_bb <> bb ==>
         IS_SOME (lookup_var pvar s)) ==>
    m2v_pvars_set fn bb 0 s
Proof rw[m2v_pvars_set_def]
QED

(* m2v_pvars_set steps from idx to SUC idx *)
Theorem m2v_pvars_set_step:
  !fn bb idx s s'.
    m2v_pvars_set fn bb idx s /\
    (* Existing pvars (sz=32) preserved *)
    (!ao pvar. MEM (ao,pvar,32) (m2v_promo_list fn) ==>
       IS_SOME (lookup_var pvar s) ==> IS_SOME (lookup_var pvar s')) /\
    (* If idx is a promoted MSTORE to ao with sz=32, pvar is set *)
    (!ao pvar. MEM (ao,pvar,32) (m2v_promo_list fn) /\
       idx < LENGTH bb.bb_instructions /\
       (EL idx bb.bb_instructions).inst_opcode = MSTORE /\
       MEM (Var ao) (EL idx bb.bb_instructions).inst_operands ==>
       IS_SOME (lookup_var pvar s')) ==>
    m2v_pvars_set fn bb (SUC idx) s'
Proof
  rw[m2v_pvars_set_def]
  >- metis_tac[]
  >> (Cases_on `j = idx`
      >- metis_tac[]
      >> (`j < idx` by decide_tac >> metis_tac[]))
QED

(* m2v_pvars_set preserved across a non-terminal step *)
Theorem m2v_pvars_set_preserved_step:
  !fn bb i s s' fuel ctx inst.
    m2v_pvars_set fn bb i s /\
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (* All sz=32 pvars not in inst outputs *)
    (!ao pvar. MEM (ao,pvar,32) (m2v_promo_list fn) ==>
       ~MEM pvar inst.inst_outputs) /\
    (* If EL i is MSTORE to ao with sz=32, then pvar IS_SOME in s' *)
    (!ao pvar. MEM (ao,pvar,32) (m2v_promo_list fn) /\
       i < LENGTH bb.bb_instructions /\
       (EL i bb.bb_instructions).inst_opcode = MSTORE /\
       MEM (Var ao) (EL i bb.bb_instructions).inst_operands ==>
       IS_SOME (lookup_var pvar s')) ==>
    m2v_pvars_set fn bb (SUC i) s'
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`,`bb`,`i`,`s`,`s'`] m2v_pvars_set_step) >>
  simp[] >> disch_then irule >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  SUBGOAL_THEN ``lookup_var pvar s' = lookup_var pvar s``
    (fn th => gvs[th])
  >- (drule venomInstProofsTheory.step_preserves_non_output_vars >>
      simp[] >> metis_tac[])
QED


(* m2v_pvars_set is insensitive to vs_inst_idx *)
Theorem m2v_pvars_set_update_idx:
  !fn bb idx s k.
    m2v_pvars_set fn bb idx s ==>
    m2v_pvars_set fn bb idx (s with vs_inst_idx := k)
Proof
  rw[m2v_pvars_set_def, lookup_var_def]
QED

(* Helper: ALL_DISTINCT (FLAT (MAP f xs)) /\ MEM x xs ==> ALL_DISTINCT (f x) *)
Theorem ALL_DISTINCT_FLAT_MAP_MEM:
  !f xs x. ALL_DISTINCT (FLAT (MAP f xs)) /\ MEM x xs ==>
    ALL_DISTINCT (f x)
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

(* Helper: within a wf block, EL i = EL j implies i = j
   (instruction IDs are globally distinct, so within a block too) *)
Theorem wf_bb_EL_inj:
  !fn bb i j.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\
    j < LENGTH bb.bb_instructions /\
    EL i bb.bb_instructions = EL j bb.bb_instructions ==>
    i = j
Proof
  rpt gen_tac >> strip_tac >>
  SUBGOAL_THEN ``ALL_DISTINCT (MAP (\i:instruction. i.inst_id)
    bb.bb_instructions)`` assume_tac
  >- (gvs[wf_function_def, fn_inst_ids_distinct_def] >>
      ho_match_mp_tac ALL_DISTINCT_FLAT_MAP_MEM >>
      qexists `MAP (\bb. bb.bb_instructions) fn.fn_blocks` >>
      simp[MAP_MAP_o, MEM_MAP] >> metis_tac[]) >>
  gvs[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >> metis_tac[]
QED

(* Helper: promo_list membership + promotable_wf ==> stores_dominate_loads *)
Theorem m2v_promo_stores_dominate:
  !fn ao pvar sz.
    m2v_promotable_wf fn /\ MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    m2v_stores_dominate_loads fn ao
Proof
  rpt strip_tac >>
  gvs[m2v_promotable_wf_def, LET_THM] >>
  first_x_assum irule >>
  drule m2v_promo_list_is_alloca >> strip_tac >>
  drule m2v_promo_list_can_promote >> strip_tac >>
  metis_tac[]
QED

(* IS_SOME (lookup_var pvar s) from pvars_set + stores_dominate.
   Works for any opcode covered by m2v_stores_dominate_loads (MLOAD or RETURN). *)
Theorem m2v_pvars_set_use_is_some:
  !fn bb i s ao pvar.
    wf_function fn /\
    m2v_promotable_wf fn /\
    MEM (ao,pvar,32) (m2v_promo_list fn) /\
    MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\
    ((EL i bb.bb_instructions).inst_opcode = MLOAD \/
     (EL i bb.bb_instructions).inst_opcode = RETURN) /\
    MEM (Var ao) (EL i bb.bb_instructions).inst_operands /\
    m2v_pvars_set fn bb i s ==>
    IS_SOME (lookup_var pvar s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all m2v_promo_stores_dominate >> strip_tac >>
  fs[m2v_stores_dominate_loads_def] >>
  first_x_assum (qspecl_then [`bb`, `EL i bb.bb_instructions`] mp_tac) >>
  (impl_tac >- (simp[MEM_EL] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`store_bb`,`store_inst`] strip_assume_tac) >>
  Cases_on `store_bb = bb` >> fs[] >> (
    TRY (SUBGOAL_THEN ``j = i:num`` SUBST_ALL_TAC
         >- (irule wf_bb_EL_inj >> metis_tac[])) >>
    fs[m2v_pvars_set_def] >>
    first_x_assum (qspecl_then [`ao`,`pvar`] mp_tac) >> simp[] >>
    strip_tac >>
    TRY (first_x_assum (qspec_then `i'` mp_tac) >> simp[] >> NO_TAC) >>
    first_x_assum (qspecl_then [`store_bb`,`store_inst`] mp_tac) >> simp[])
QED

(* Backwards compatibility alias *)
val m2v_pvars_set_mload_is_some = m2v_pvars_set_use_is_some;

Theorem m2v_inv_implies_noix:
  !fn s1 s2.
    m2v_inv fn s1 s2 /\
    allocas_non_overlapping s1 /\
    (!ao pvar sz inst.
       MEM (ao, pvar, sz) (m2v_promo_list fn) /\
       MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_outputs = [ao] ==>
       !addr. lookup_var ao s1 = SOME addr ==>
       FLOOKUP s1.vs_allocas inst.inst_id = SOME (w2n addr, sz)) ==>
    m2v_inv_noix fn s1 s2
Proof
  rw[m2v_inv_def, m2v_inv_noix_def, m2v_equiv_def] >> metis_tac[]
QED

Theorem m2v_inv_noix_with_idx:
  !fn s1 s2. m2v_inv_noix fn s1 s2 ==>
    !n. m2v_inv fn (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  rw[m2v_inv_def, m2v_inv_noix_def, m2v_equiv_def, lookup_var_def,
     in_promoted_region_def, mem_byte_def, mload_def]
QED

(* ================================================================
   m2v_sz_undef: for sz≠32 promo entries, pvar is undefined in s2.
   Separate from m2v_inv_noix to avoid blast radius.
   Preserved by all steps: only promoted MSTOREs with sz=32 assign to pvars.
   ================================================================ *)

(* With in_promoted_region narrowed to sz=32 only, m2v_inv_noix's memory
   clause covers sz≠32 alloca regions. We only need pvar=NONE. *)
Definition m2v_non32_ok_def:
  m2v_non32_ok fn s1 s2 <=>
    !ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) /\ sz <> 32 ==>
      lookup_var pvar s2 = NONE
End

Theorem m2v_non32_ok_refl:
  !fn s. m2v_fresh_undef fn s ==> m2v_non32_ok fn s s
Proof
  rw[m2v_non32_ok_def, m2v_fresh_undef_def] >>
  first_x_assum irule >>
  irule m2v_promo_list_in_fresh_vars >> metis_tac[]
QED

Theorem m2v_non32_ok_update_idx:
  !fn s1 s2 j k. m2v_non32_ok fn s1 s2 ==>
    m2v_non32_ok fn (s1 with vs_inst_idx := j) (s2 with vs_inst_idx := k)
Proof
  simp[m2v_non32_ok_def, lookup_var_def]
QED

(* ao undefined in s1 implies pvar undefined in s2.
   Preserved because: (a) ao only goes NONE→SOME (making antecedent false),
   (b) pvar only set by promoted MSTORE which requires ao defined. *)
Definition m2v_ao_undef_sync_def:
  m2v_ao_undef_sync fn s1 s2 <=>
    !ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
      lookup_var ao s1 = NONE ==> lookup_var pvar s2 = NONE
End

Theorem m2v_ao_undef_sync_refl:
  !fn s. m2v_fresh_undef fn s ==> m2v_ao_undef_sync fn s s
Proof
  rw[m2v_ao_undef_sync_def, m2v_fresh_undef_def] >>
  first_x_assum irule >>
  irule m2v_promo_list_in_fresh_vars >> metis_tac[]
QED

Theorem m2v_ao_undef_sync_update_idx:
  !fn s1 s2 j k. m2v_ao_undef_sync fn s1 s2 ==>
    m2v_ao_undef_sync fn (s1 with vs_inst_idx := j) (s2 with vs_inst_idx := k)
Proof
  simp[m2v_ao_undef_sync_def, lookup_var_def]
QED

(* Frame lemma: ao_undef_sync preserved by any state change that
   preserves lookup_var on both sides. *)
Theorem m2v_ao_undef_sync_frame:
  !fn s1 s2 s1' s2'.
    m2v_ao_undef_sync fn s1 s2 /\
    (!v. lookup_var v s1' = lookup_var v s1) /\
    (!v. lookup_var v s2' = lookup_var v s2) ==>
    m2v_ao_undef_sync fn s1' s2'
Proof
  simp[m2v_ao_undef_sync_def] >> metis_tac[]
QED

(* If pvar ends up in (HD (m2v_rewrite_inst fn inst)).inst_outputs,
   then FIND matched (ao,pvar,sz) with inst.inst_opcode=MSTORE and
   Var ao in inst.inst_operands. *)
Theorem m2v_rewrite_pvar_in_outputs:
  !fn inst ao pvar sz.
    MEM (ao,pvar,sz) (m2v_promo_list fn) /\
    ssa_form fn /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\
    ~is_terminator inst.inst_opcode /\
    MEM pvar (HD (m2v_rewrite_inst fn inst)).inst_outputs ==>
    inst.inst_opcode = MSTORE /\ MEM (Var ao) inst.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  gvs[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao',_,_). MEM (Var ao') inst.inst_operands)
                  (m2v_promo_list fn)` >> gvs[]
  >- ((* FIND=NONE: pvar in original outputs contradicts freshness *)
      imp_res_tac m2v_promo_list_in_fresh_vars >>
      gvs[m2v_fresh_names_disjoint_def] >> res_tac >> gvs[]) >>
  PairCases_on `x` >> rename1 `SOME (ao2, pvar2, sz2)` >> gvs[] >>
  (* Only MSTORE+sz2=32+offset match puts pvar2 in outputs *)
  gvs[m2v_promote_inst_def] >>
  reverse (Cases_on `inst.inst_opcode = MSTORE /\ sz2 = 32`) >> gvs[]
  >- ((* Not MSTORE+32: promote_inst keeps original outputs *)
      EVERY_CASE_TAC >> gvs[] >>
      imp_res_tac m2v_promo_list_in_fresh_vars >>
      gvs[m2v_fresh_names_disjoint_def] >> res_tac >> gvs[]) >>
  (* MSTORE+32: outputs=[pvar2] when offset matches, else original *)
  EVERY_CASE_TAC >> gvs[] >>
  TRY (imp_res_tac m2v_promo_list_in_fresh_vars >>
       gvs[m2v_fresh_names_disjoint_def] >> res_tac >> gvs[] >> NO_TAC) >>
  (* Remaining: pvar in [pvar2] → pvar=pvar2 → (ao,sz)=(ao2,sz2) *)
  qpat_x_assum `FIND _ _ = SOME _` (mp_tac o MATCH_MP venomExecProofsTheory.FIND_MEM) >>
  strip_tac >>
  `(ao,pvar,sz) = (ao2,pvar,32n)` by metis_tac[m2v_promo_list_pvar_unique] >>
  gvs[]
QED

(* m2v_ao_undef_sync preserved by dispatch.
   If lookup_var ao v1 = NONE after original step, then ao wasn't set:
   step_inst_fdom says outputs ⊂ FDOM, so ao ∉ outputs.
   step_inst_preserves_non_output gives ao s1 = NONE.
   Sync gives pvar s2 = NONE. pvar not in rewritten outputs
   (only MSTORE promotion adds pvar, requiring ao defined — contradiction).
   So pvar v2 = pvar s2 = NONE. *)
Theorem m2v_ao_undef_sync_preserved_step:
  !fn bb i fuel ctx s1 s2 v1 v2.
    m2v_ao_undef_sync fn s1 s2 /\
    m2v_fresh_names_disjoint fn /\
    ssa_form fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\
    ~is_terminator (EL i bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL i bb.bb_instructions) s1 = OK v1 /\
    step_inst fuel ctx
      (HD (m2v_rewrite_inst fn (EL i bb.bb_instructions))) s2 = OK v2 ==>
    m2v_ao_undef_sync fn v1 v2
Proof
  rw[m2v_ao_undef_sync_def] >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  `MEM inst (fn_insts fn)` by
    (simp[Abbr `inst`] >> metis_tac[MEM_fn_insts, MEM_EL]) >>
  (* ao not in inst outputs: step_inst_fdom says outputs ⊂ FDOM v1,
     but lookup_var ao v1 = NONE means ao ∉ FDOM v1 *)
  `~MEM ao inst.inst_outputs` by
    (strip_tac >>
     `inst_wf inst` by metis_tac[fn_inst_wf_MEM] >>
     `inst.inst_opcode ≠ PHI` by metis_tac[step_inst_ok_imp_not_phi] >>
     drule_all step_inst_fdom >> strip_tac >>
     `ao IN FDOM v1.vs_vars` by simp[EXTENSION] >>
     gvs[lookup_var_def, FLOOKUP_DEF]) >>
  `lookup_var ao s1 = NONE` by
    metis_tac[step_inst_preserves_non_output] >>
  `lookup_var pvar s2 = NONE` by metis_tac[] >>
  (* pvar not in rewritten outputs — if it were, m2v_rewrite_pvar_in_outputs
     gives MSTORE + Var ao in operands, but step_inst MSTORE w/ ao=NONE fails *)
  Cases_on `MEM pvar (HD (m2v_rewrite_inst fn inst)).inst_outputs`
  >- suspend "pvar_in_outputs"
  >> metis_tac[step_inst_preserves_non_output]
QED

Resume m2v_ao_undef_sync_preserved_step[pvar_in_outputs]:
  (* Contradiction: pvar in rewritten outputs → MSTORE + Var ao as operand,
     but lookup_var ao s1 = NONE means eval_operand fails → step_inst Error *)
  `F` suffices_by simp[] >>
  `inst.inst_opcode = MSTORE /\ MEM (Var ao) inst.inst_operands` by
    (mp_tac (Q.SPECL [`fn`,`inst`,`ao`,`pvar`,`sz`]
               m2v_rewrite_pvar_in_outputs) >> simp[]) >>
  `eval_operand (Var ao) s1 = NONE` by simp[eval_operand_def] >>
  qpat_x_assum `step_inst _ _ inst _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  EVERY_CASE_TAC >> gvs[MEM]
QED

Finalise m2v_ao_undef_sync_preserved_step

(* m2v_non32_ok preserved through any nonterminal step.
   For pvar part: pvar (sz≠32) is never in outputs of transformed instruction.
   For mem part: memory agreement preserved by m2v_inv. *)
(* Helper: pvar from sz≠32 entry is NOT in outputs of rewritten instruction *)
Theorem m2v_non32_pvar_not_in_rewrite_outputs:
  !fn inst ao pvar sz.
    ssa_form fn /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\ ~is_terminator inst.inst_opcode /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\ sz <> 32 ==>
    ~MEM pvar (HD (m2v_rewrite_inst fn inst)).inst_outputs
Proof
  rpt gen_tac >> strip_tac >> CCONTR_TAC >> gvs[] >>
  mp_tac (Q.SPECL [`fn`,`ao`,`pvar`,`sz`] m2v_promo_list_in_fresh_vars) >>
  simp[] >> strip_tac >>
  qpat_x_assum `MEM pvar _` mp_tac >>
  simp[m2v_rewrite_inst_def] >>
  CASE_TAC >> simp[]
  >- (simp[m2v_fresh_names_disjoint_def] >>
      gvs[m2v_fresh_names_disjoint_def] >> res_tac) >>
  PairCases_on `x` >>
  rename1 `SOME (ao2, pvar2, sz2)` >> simp[] >>
  simp[m2v_promote_inst_def] >>
  rpt (CASE_TAC >> simp[is_terminator_def] >> gvs[is_terminator_def]) >>
  TRY (gvs[m2v_fresh_names_disjoint_def] >> res_tac >> NO_TAC) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `FIND _ _ = SOME _` (strip_assume_tac o
    MATCH_MP venomExecProofsTheory.FIND_MEM) >>
  imp_res_tac m2v_promo_list_pvar_unique >> fs[]
QED

(* Moved before m2v_non32_ok_preserved_step — needed as dependency *)
Theorem m2v_rewrite_nonterm:
  !fn inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (HD (m2v_rewrite_inst fn inst)).inst_opcode
Proof
  rpt strip_tac >>
  gvs[m2v_rewrite_inst_def] >>
  every_case_tac >> gvs[m2v_promote_inst_def] >>
  every_case_tac >> gvs[is_terminator_def]
QED

Theorem m2v_rewrite_not_invoke:
  !fn inst. inst.inst_opcode <> INVOKE ==>
    (HD (m2v_rewrite_inst fn inst)).inst_opcode <> INVOKE
Proof
  rpt strip_tac >>
  gvs[m2v_rewrite_inst_def] >>
  every_case_tac >> gvs[m2v_promote_inst_def] >>
  every_case_tac >> gvs[]
QED

(* m2v_non32_ok ignores its first state arg.
    Conclusion avoids mentioning it so callers don't hit type issues. *)
Theorem m2v_non32_ok_preserved_step:
  !fn inst s2 v2 fuel ctx.
    (!ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) /\ sz <> 32 ==>
       lookup_var pvar s2 = NONE) /\
    ssa_form fn /\
    m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx (HD (m2v_rewrite_inst fn inst)) s2 = OK v2 ==>
    !ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) /\ sz <> 32 ==>
      lookup_var pvar v2 = NONE
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`fn`,`inst`,`ao`,`pvar`,`sz`]
    m2v_non32_pvar_not_in_rewrite_outputs) >>
  simp[] >> strip_tac >>
  `lookup_var pvar s2 = NONE` by (res_tac >> simp[]) >>
  `~is_terminator (HD (m2v_rewrite_inst fn inst)).inst_opcode` by
    metis_tac[m2v_rewrite_nonterm] >>
  drule_all step_preserves_non_output_vars >> simp[]
QED

(* ================================================================
   PER-INSTRUCTION SIMULATION (non-promoted case)
   Non-promoted instructions pass through m2v_rewrite_inst unchanged.
   FIND=NONE means no promoted alloca variable appears in operands,
   so operands evaluate identically under m2v_inv. Memory-reading ops
   require a side condition discharged via bp_ptr_sound (non-promoted
   addresses can't alias promoted regions).
   ================================================================ *)

(* Helper: m2v_inv_noix implies operand agreement for non-fresh operands *)
Theorem m2v_inv_noix_eval_operand:
  !fn s1 s2 op.
    m2v_inv_noix fn s1 s2 /\
    (!v. op = Var v ==> v NOTIN m2v_fresh_vars fn) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >> rw[eval_operand_def, m2v_inv_noix_def]
QED

(* General: FIND P l = NONE iff no element satisfies P *)
Theorem FIND_NONE_EVERY:
  !P l. FIND P l = NONE <=> EVERY ($~ o P) l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> CASE_TAC >> simp[]
QED

(* Write-effects exclusion: non-ext-call, non-terminator, non-invoke ops
   without MEMORY writes don't write RETURNDATA.
   STATICCALL (ext_call) writes RETURNDATA, but is excluded. *)
Theorem no_returndata_write_without_memory_or_extcall:
  !op. ~is_terminator op /\ op <> INVOKE /\ ~is_ext_call_op op /\
    Eff_MEMORY NOTIN write_effects op ==>
    Eff_RETURNDATA NOTIN write_effects op
Proof
  Cases >> simp[is_terminator_def, is_ext_call_op_def,
    write_effects_def, empty_effects_def]
QED

(* Write-effects exclusion: ops that don't read MEMORY don't write LOG.
   LOG is the only opcode that writes Eff_LOG, and LOG reads Eff_MEMORY.
   After MSIZE sunset: LOG no longer has Eff_MSIZE, so this requires its own lemma. *)
Theorem LOG_reads_memory:
  Eff_MEMORY IN read_effects LOG
Proof
  EVAL_TAC
QED

Theorem no_log_write_without_memory_read:
  !op. Eff_MEMORY NOTIN read_effects op ==>
    Eff_LOG NOTIN write_effects op
Proof
  Cases >> EVAL_TAC
QED

(* Write-effects exclusion: ops without MEMORY/LOG/RETURNDATA writes
   also don't write IMMUTABLES (given our other filters).
   After MSIZE sunset: LOG and RETURNDATA write_effects no longer
   carry Eff_MSIZE, so must be excluded explicitly. *)
Theorem no_mem_write_excludes_others:
  !op. ~is_terminator op /\ op <> INVOKE /\ ~is_alloca_op op /\
    ~is_ext_call_op op /\ Eff_MEMORY NOTIN write_effects op /\
    Eff_LOG NOTIN write_effects op /\ Eff_RETURNDATA NOTIN write_effects op ==>
    Eff_IMMUTABLES NOTIN write_effects op
Proof
  Cases >> simp[is_terminator_def, is_alloca_op_def,
    is_ext_call_op_def, write_effects_def, all_effects_def,
    empty_effects_def]
QED

(* Generic list lemma: ALL_DISTINCT (FLAT ls) → disjoint sublists *)
Theorem ALL_DISTINCT_FLAT_DISJOINT:
  !ls l1 l2 x. ALL_DISTINCT (FLAT ls) /\ MEM l1 ls /\ MEM l2 ls /\
    l1 <> l2 /\ MEM x l1 ==> ~MEM x l2
Proof
  Induct_on `ls` >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_FLAT]
QED

(* SSA + promo_list → ao not in other non-alloca instruction's outputs.
   The alloca that defines ao has outputs=[ao], so inst must not be that alloca.
   ~is_alloca_op ensures inst ≠ alloca_inst. *)
Theorem ALL_DISTINCT_FLAT_MAP_unique:
  !f xs a b x. ALL_DISTINCT (FLAT (MAP f xs)) /\
    MEM a xs /\ MEM b xs /\ MEM x (f a) /\ MEM x (f b) ==> a = b
Proof
  Induct_on `xs` >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem ssa_promo_ao_not_in_outputs:
  !fn ao pvar sz inst.
    ssa_form fn /\ MEM (ao,pvar,sz) (m2v_promo_list fn) /\
    MEM inst (fn_insts fn) /\ ~is_alloca_op inst.inst_opcode ==>
    ~MEM ao inst.inst_outputs
Proof
  rpt strip_tac >>
  drule m2v_promo_list_is_alloca >> strip_tac >>
  rename1 `alloca_inst.inst_opcode = ALLOCA` >>
  gvs[ssa_form_def] >>
  qspecl_then [`\i. i.inst_outputs`, `fn_insts fn`,
    `alloca_inst`, `inst`, `ao`] mp_tac ALL_DISTINCT_FLAT_MAP_unique >>
  simp[] >> strip_tac >> gvs[is_alloca_op_def]
QED

(* Outputs of non-alloca instructions are disjoint from fresh vars
   and from promo AO names. Used in ALL dispatch cases. *)
Theorem m2v_output_safe:
  !fn inst out.
    ssa_form fn /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\ ~is_alloca_op inst.inst_opcode /\
    MEM out inst.inst_outputs ==>
    out NOTIN m2v_fresh_vars fn /\
    !pvar2 sz2. ~MEM (out,pvar2,sz2) (m2v_promo_list fn)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (CCONTR_TAC >> gvs[] >>
      gvs[m2v_fresh_names_disjoint_def] >> res_tac)
  >> rpt gen_tac >> CCONTR_TAC >> gvs[] >>
  drule_all m2v_promo_list_is_alloca >> strip_tac >>
  mp_tac (Q.SPECL [`fn`,`out`,`pvar2`,`sz2`,`inst`]
    ssa_promo_ao_not_in_outputs) >> simp[]
QED

(* For non-promoted, non-memory-writing, non-terminator instructions:
   m2v_inv_noix is preserved.

   Restricted to Eff_MEMORY ∉ write_effects so memory is unchanged
   on both sides. Memory-writing non-promoted ops handled separately. *)
Theorem m2v_step_nonpromoted:
  !fn inst s1 s2 fuel ctx v1.
    m2v_inv_noix fn s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode /\
    Eff_RETURNDATA NOTIN write_effects inst.inst_opcode /\
    (Eff_MEMORY IN read_effects inst.inst_opcode ==>
     s1.vs_memory = s2.vs_memory) /\
    (Eff_TRANSIENT IN read_effects inst.inst_opcode ==>
     s1.vs_transient = s2.vs_transient) /\
    (Eff_STORAGE IN read_effects inst.inst_opcode ==>
     s1.vs_accounts = s2.vs_accounts) /\
    (Eff_BALANCE IN read_effects inst.inst_opcode ==>
     s1.vs_accounts = s2.vs_accounts) /\
    (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
     s1.vs_accounts = s2.vs_accounts) /\
    (Eff_IMMUTABLES IN read_effects inst.inst_opcode ==>
     s1.vs_immutables = s2.vs_immutables) /\
    (Eff_LOG IN read_effects inst.inst_opcode ==>
     s1.vs_logs = s2.vs_logs) /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (~is_effect_free_op inst.inst_opcode ==> inst.inst_outputs = []) /\
    (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
    (!ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
      ~MEM ao inst.inst_outputs) /\
    step_inst fuel ctx inst s1 = OK v1 ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\
         m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  suspend "main"
QED

(* Core lemma: m2v_inv_noix preserved by a nonpromoted step.
   Extracted as standalone theorem for independent checking. *)
Theorem m2v_inv_noix_step_nonpromoted:
  !inst s1 s2 v1 v2 fn fuel ctx.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    m2v_inv_noix fn s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode /\
    Eff_RETURNDATA NOTIN write_effects inst.inst_opcode /\
    (Eff_MEMORY IN read_effects inst.inst_opcode ==>
     s1.vs_memory = s2.vs_memory) /\
    (Eff_TRANSIENT IN read_effects inst.inst_opcode ==>
     s1.vs_transient = s2.vs_transient) /\
    (Eff_STORAGE IN read_effects inst.inst_opcode ==>
     s1.vs_accounts = s2.vs_accounts) /\
    (Eff_BALANCE IN read_effects inst.inst_opcode ==>
     s1.vs_accounts = s2.vs_accounts) /\
    (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
     s1.vs_accounts = s2.vs_accounts) /\
    (Eff_IMMUTABLES IN read_effects inst.inst_opcode ==>
     s1.vs_immutables = s2.vs_immutables) /\
    (Eff_LOG IN read_effects inst.inst_opcode ==>
     s1.vs_logs = s2.vs_logs) /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (~is_effect_free_op inst.inst_opcode ==> inst.inst_outputs = []) /\
    (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
    (!ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
      ~MEM ao inst.inst_outputs) /\
    step_inst fuel ctx inst s1 = OK v1 /\
    step_inst fuel ctx inst s2 = OK v2 ==>
    m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >>
  `s1.vs_fmp = s2.vs_fmp /\
   s1.vs_initial_fmp = s2.vs_initial_fmp /\
   s1.vs_return_pc_token = s2.vs_return_pc_token` by
    gvs[m2v_inv_noix_def] >>
  `v1.vs_fmp = v2.vs_fmp` by (
    mp_tac (Q.SPECL [`inst`, `s1`, `s2`, `v1`, `v2`]
      step_inst_base_ordinary_fmp_agreement) >> simp[]) >>
  `v1.vs_call_entry_fmp = s1.vs_call_entry_fmp /\
   v1.vs_initial_fmp = s1.vs_initial_fmp /\
   v1.vs_return_pc_token = s1.vs_return_pc_token` by (
    mp_tac (Q.SPECL [`inst`, `s1`, `v1`]
      step_inst_base_preserves_stable_frame_metadata) >> simp[]) >>
  `v2.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
   v2.vs_initial_fmp = s2.vs_initial_fmp /\
   v2.vs_return_pc_token = s2.vs_return_pc_token` by (
    mp_tac (Q.SPECL [`inst`, `s2`, `v2`]
      step_inst_base_preserves_stable_frame_metadata) >> simp[]) >>
  `v1.vs_initial_fmp = v2.vs_initial_fmp /\
   v1.vs_return_pc_token = v2.vs_return_pc_token` by metis_tac[] >>
  imp_res_tac step_inst_preserves_alloca_state >>
  imp_res_tac step_inst_preserves_all >>
  imp_res_tac no_mem_write_excludes_others >>
  qpat_x_assum `step_inst _ _ inst s1 = _` assume_tac >>
  drule step_preserves_non_output_vars >> strip_tac >>
  qpat_x_assum `step_inst _ _ inst s2 = _` assume_tac >>
  drule step_preserves_non_output_vars >> strip_tac >>
  mp_tac (Q.SPECL [`inst`, `s1`, `s2`, `v1`, `v2`]
    step_inst_base_output_determined_fields) >>
  mp_tac (Q.SPECL [`inst`, `s1`, `s2`, `v1`, `v2`]
    step_inst_base_effect_free_output_determined_vars) >>
  simp[m2v_inv_noix_def] >>
  gvs[m2v_inv_noix_def] >>
  rpt strip_tac >> gvs[]
  (* Dispatch easy subgoals: allocas, memory, bridge, then vars+sync *)
  >> TRY (gvs[allocas_non_overlapping_def] >> NO_TAC)
  >> TRY (gvs[in_promoted_region_def, mem_byte_def] >> NO_TAC)
  >> TRY (gvs[in_promoted_region_def] >> metis_tac[] >> NO_TAC)
  (* Bridge: vs_allocas preserved, ao not in outputs *)
  >> TRY (rpt strip_tac >> res_tac >> metis_tac[] >> NO_TAC)
  >- suspend "g1"
  >- suspend "g2"
  >> suspend "g3"
QED

Resume m2v_inv_noix_step_nonpromoted[g1]:
  Cases_on `MEM v inst.inst_outputs`
  >- (Cases_on `is_effect_free_op inst.inst_opcode`
      >- (Cases_on `inst.inst_opcode = NOP`
          >- gvs[step_inst_base_def, AllCaseEqs()] >>
          Cases_on `inst.inst_opcode = PHI`
          >- gvs[step_inst_base_def, AllCaseEqs()] >>
          metis_tac[])
      >> gvs[])
  >> metis_tac[]
QED

Resume m2v_inv_noix_step_nonpromoted[g2]:
  gvs[allocas_non_overlapping_def] >>
  metis_tac[]
QED

Resume m2v_inv_noix_step_nonpromoted[g3]:
  `pvar IN m2v_fresh_vars fn`
     by metis_tac[m2v_promo_list_in_fresh_vars] >>
  `~MEM pvar inst.inst_outputs` by metis_tac[] >>
  `~MEM ao inst.inst_outputs` by metis_tac[] >>
  `lookup_var pvar v2 = lookup_var pvar s2` by metis_tac[] >>
  `lookup_var ao v1 = lookup_var ao s1` by metis_tac[] >>
  `lookup_var pvar s2 = SOME (mload (w2n addr) s1)`
     by metis_tac[optionTheory.IS_SOME_DEF] >>
  gvs[mload_def]
QED

Finalise m2v_inv_noix_step_nonpromoted

Resume m2v_step_nonpromoted[main]:
  `?v2. step_inst_base inst s2 = OK v2` by (
    drule_then (qspec_then `s2` mp_tac) step_inst_base_ok_transfer >>
    gvs[m2v_inv_noix_def]) >>
  qexists `v2` >> simp[] >>
  `step_inst fuel ctx inst s1 = OK v1 /\
   step_inst fuel ctx inst s2 = OK v2` by gvs[step_inst_non_invoke] >>
  mp_tac (Q.SPECL [`inst`, `s1`, `s2`, `v1`, `v2`, `fn`,
                    `fuel`, `ctx`] m2v_inv_noix_step_nonpromoted) >>
  impl_tac >- (rpt conj_tac >> gvs[]) >>
  simp[]
QED

Finalise m2v_step_nonpromoted

(* ================================================================
   PER-INSTRUCTION SIMULATION (promoted MSTORE case)
   MSTORE [Var ao; val_op] -> ASSIGN [val_op] output [pvar]
   ================================================================ *)

Theorem len_word_to_bytes_256:
  LENGTH (word_to_bytes (w:bytes32) be) = 32
Proof
  rw[byteTheory.LENGTH_word_to_bytes,
     fcpTheory.index_bit0, fcpTheory.index_bit1, fcpTheory.index_one,
     fcpTheory.finite_bit0, fcpTheory.finite_bit1, fcpTheory.finite_one]
QED

(* General: EL outside a splice is unchanged *)
Theorem EL_splice_outside:
  !n mid l i. n + LENGTH mid <= LENGTH l /\
    (i < n \/ n + LENGTH mid <= i) /\ i < LENGTH l ==>
    EL i (TAKE n l ++ mid ++ DROP (n + LENGTH mid) l) = EL i l
Proof
  rpt strip_tac
  >- (* i < n: element is in TAKE n l *)
     (simp[EL_APPEND1, LENGTH_TAKE] >> simp[EL_TAKE])
  >> (* n + LENGTH mid <= i: element is in DROP (n + LENGTH mid) l *)
     simp[EL_APPEND_EQN, LENGTH_TAKE] >>
     `~(i < n)` by simp[] >> simp[] >>
     `~(i - n < LENGTH mid)` by simp[] >> simp[] >>
     simp[EL_DROP]
QED

(* General: EL inside a splice returns the mid element *)
Theorem EL_splice_inside:
  !n mid l i. n + LENGTH mid <= LENGTH l /\
    n <= i /\ i < n + LENGTH mid ==>
    EL i (TAKE n l ++ mid ++ DROP (n + LENGTH mid) l) = EL (i - n) mid
Proof
  rpt strip_tac >> simp[EL_APPEND_EQN, LENGTH_TAKE]
QED

(* mstore on an expanded memory gives the same result as on the original
   memory, for the TAKE/DROP/++ structure *)
(* EL-with-default of splice = EL-with-default of original *)
Theorem EL_default_splice_padded:
  !n k (mem:word8 list) mid i.
    n + LENGTH mid <= LENGTH mem + k /\
    (i < n \/ n + LENGTH mid <= i) ==>
    let exp = mem ++ REPLICATE k 0w in
    let spl = TAKE n exp ++ mid ++ DROP (n + LENGTH mid) exp in
      (if i < LENGTH spl then EL i spl else 0w) =
      (if i < LENGTH mem then EL i mem else 0w)
Proof
  rpt gen_tac >> simp[LET_THM] >> strip_tac >>
  qabbrev_tac `exp = mem ++ REPLICATE k 0w` >>
  `n + LENGTH mid <= LENGTH exp` by (unabbrev_all_tac >> simp[]) >>
  `LENGTH (TAKE n exp ++ mid ++ DROP (n + LENGTH mid) exp) = LENGTH exp`
    by simp[LENGTH_TAKE, LENGTH_DROP]
  >- ((* i < n: i < LENGTH exp since n <= LENGTH exp *)
      `i < LENGTH exp` by simp[] >>
      `i < k + LENGTH mem` by (unabbrev_all_tac >> simp[]) >> simp[] >>
      `EL i (TAKE n exp ++ mid ++ DROP (n + LENGTH mid) exp) = EL i exp`
        by (irule EL_splice_outside >> simp[]) >>
      simp[] >> unabbrev_all_tac >> simp[EL_APPEND_EQN, EL_REPLICATE])
  >> (* n + LENGTH mid <= i *)
     Cases_on `i < k + LENGTH mem`
     >- (simp[] >>
         `i < LENGTH exp` by (unabbrev_all_tac >> simp[]) >>
         `EL i (TAKE n exp ++ mid ++ DROP (n + LENGTH mid) exp) = EL i exp`
           by (irule EL_splice_outside >> simp[]) >>
         simp[] >> unabbrev_all_tac >> simp[EL_APPEND_EQN, EL_REPLICATE])
     >> simp[]
QED

Theorem mem_byte_mstore_outside:
  !off (val_w:bytes32) s i. (i < off \/ off + 32 <= i) ==>
    mem_byte i (mstore off val_w s) = mem_byte i s
Proof
  rpt gen_tac >> disch_tac >>
  simp[mem_byte_def, mstore_def, LET_THM, len_word_to_bytes_256] >>
  qabbrev_tac `k = if off + 32 > LENGTH s.vs_memory
    then off + 32 - LENGTH s.vs_memory else 0` >>
  `(if off + 32 > LENGTH s.vs_memory
    then s.vs_memory ++ REPLICATE (off + 32 - LENGTH s.vs_memory) 0w
    else s.vs_memory) =
   s.vs_memory ++ REPLICATE k 0w`
    by (unabbrev_all_tac >> rw[]) >>
  ASM_REWRITE_TAC[] >>
  mp_tac (Q.SPECL [`off`, `k`, `s.vs_memory`,
    `word_to_bytes (val_w:bytes32) T`, `i`] EL_default_splice_padded) >>
  simp[len_word_to_bytes_256, LET_THM] >>
  (impl_tac >- (unabbrev_all_tac >> gvs[])) >>
  `off + 32 <= k + LENGTH s.vs_memory`
    by (unabbrev_all_tac >> rw[] >> simp[]) >>
  simp[LENGTH_TAKE]
QED

(* ----------------------------------------------------------------
   SHARED HELPERS for promoted step lemmas (mstore, mload, return).
   Each operation preserves certain fields; these lemmas auto-dispatch
   the 18 field conjuncts in m2v_inv_noix.
   ---------------------------------------------------------------- *)

(* mstore preserves all non-memory fields and lookup_var *)
Theorem mstore_preserves:
  !off v s.
    (mstore off v s).vs_current_bb = s.vs_current_bb /\
    (mstore off v s).vs_prev_bb = s.vs_prev_bb /\
    (mstore off v s).vs_transient = s.vs_transient /\
    ((mstore off v s).vs_halted <=> s.vs_halted) /\
    (mstore off v s).vs_returndata = s.vs_returndata /\
    (mstore off v s).vs_accounts = s.vs_accounts /\
    (mstore off v s).vs_call_ctx = s.vs_call_ctx /\
    (mstore off v s).vs_tx_ctx = s.vs_tx_ctx /\
    (mstore off v s).vs_block_ctx = s.vs_block_ctx /\
    (mstore off v s).vs_logs = s.vs_logs /\
    (mstore off v s).vs_immutables = s.vs_immutables /\
    (mstore off v s).vs_data_section = s.vs_data_section /\
    (mstore off v s).vs_labels = s.vs_labels /\
    (mstore off v s).vs_code = s.vs_code /\
    (mstore off v s).vs_params = s.vs_params /\
    (mstore off v s).vs_fmp = s.vs_fmp /\
    (mstore off v s).vs_initial_fmp = s.vs_initial_fmp /\
    (mstore off v s).vs_return_pc_token = s.vs_return_pc_token /\
    (mstore off v s).vs_prev_hashes = s.vs_prev_hashes /\
    (mstore off v s).vs_allocas = s.vs_allocas /\
    (mstore off v s).vs_alloca_next = s.vs_alloca_next /\
    (!x. lookup_var x (mstore off v s) = lookup_var x s) /\
    (!i. in_promoted_region fn (mstore off v s) i <=>
         in_promoted_region fn s i) /\
    (allocas_non_overlapping (mstore off v s) <=>
     allocas_non_overlapping s)
Proof
  simp[mstore_def, LET_THM, lookup_var_def,
       in_promoted_region_def, allocas_non_overlapping_def]
QED

(* write_memory_with_expansion preserves non-memory fields *)
Theorem wmwe_preserves:
  !off bytes s.
    (write_memory_with_expansion off bytes s).vs_current_bb = s.vs_current_bb /\
    (write_memory_with_expansion off bytes s).vs_prev_bb = s.vs_prev_bb /\
    (write_memory_with_expansion off bytes s).vs_transient = s.vs_transient /\
    ((write_memory_with_expansion off bytes s).vs_halted <=> s.vs_halted) /\
    (write_memory_with_expansion off bytes s).vs_returndata = s.vs_returndata /\
    (write_memory_with_expansion off bytes s).vs_accounts = s.vs_accounts /\
    (write_memory_with_expansion off bytes s).vs_call_ctx = s.vs_call_ctx /\
    (write_memory_with_expansion off bytes s).vs_tx_ctx = s.vs_tx_ctx /\
    (write_memory_with_expansion off bytes s).vs_block_ctx = s.vs_block_ctx /\
    (write_memory_with_expansion off bytes s).vs_logs = s.vs_logs /\
    (write_memory_with_expansion off bytes s).vs_immutables = s.vs_immutables /\
    (write_memory_with_expansion off bytes s).vs_data_section = s.vs_data_section /\
    (write_memory_with_expansion off bytes s).vs_labels = s.vs_labels /\
    (write_memory_with_expansion off bytes s).vs_code = s.vs_code /\
    (write_memory_with_expansion off bytes s).vs_params = s.vs_params /\
    (write_memory_with_expansion off bytes s).vs_fmp = s.vs_fmp /\
    (write_memory_with_expansion off bytes s).vs_initial_fmp = s.vs_initial_fmp /\
    (write_memory_with_expansion off bytes s).vs_return_pc_token = s.vs_return_pc_token /\
    (write_memory_with_expansion off bytes s).vs_prev_hashes = s.vs_prev_hashes /\
    (write_memory_with_expansion off bytes s).vs_allocas = s.vs_allocas /\
    (write_memory_with_expansion off bytes s).vs_alloca_next = s.vs_alloca_next /\
    (!x. lookup_var x (write_memory_with_expansion off bytes s) = lookup_var x s) /\
    (!i. in_promoted_region fn (write_memory_with_expansion off bytes s) i <=>
         in_promoted_region fn s i) /\
    (allocas_non_overlapping (write_memory_with_expansion off bytes s) <=>
     allocas_non_overlapping s)
Proof
  simp[write_memory_with_expansion_def, LET_THM, lookup_var_def,
       in_promoted_region_def, allocas_non_overlapping_def]
QED

(* mstore8 preserves non-memory fields *)
Theorem mstore8_preserves:
  !off v s.
    (mstore8 off v s).vs_current_bb = s.vs_current_bb /\
    (mstore8 off v s).vs_prev_bb = s.vs_prev_bb /\
    (mstore8 off v s).vs_transient = s.vs_transient /\
    ((mstore8 off v s).vs_halted <=> s.vs_halted) /\
    (mstore8 off v s).vs_returndata = s.vs_returndata /\
    (mstore8 off v s).vs_accounts = s.vs_accounts /\
    (mstore8 off v s).vs_call_ctx = s.vs_call_ctx /\
    (mstore8 off v s).vs_tx_ctx = s.vs_tx_ctx /\
    (mstore8 off v s).vs_block_ctx = s.vs_block_ctx /\
    (mstore8 off v s).vs_logs = s.vs_logs /\
    (mstore8 off v s).vs_immutables = s.vs_immutables /\
    (mstore8 off v s).vs_data_section = s.vs_data_section /\
    (mstore8 off v s).vs_labels = s.vs_labels /\
    (mstore8 off v s).vs_code = s.vs_code /\
    (mstore8 off v s).vs_params = s.vs_params /\
    (mstore8 off v s).vs_fmp = s.vs_fmp /\
    (mstore8 off v s).vs_initial_fmp = s.vs_initial_fmp /\
    (mstore8 off v s).vs_return_pc_token = s.vs_return_pc_token /\
    (mstore8 off v s).vs_prev_hashes = s.vs_prev_hashes /\
    (mstore8 off v s).vs_allocas = s.vs_allocas /\
    (mstore8 off v s).vs_alloca_next = s.vs_alloca_next /\
    (!x. lookup_var x (mstore8 off v s) = lookup_var x s) /\
    (!i. in_promoted_region fn (mstore8 off v s) i <=>
         in_promoted_region fn s i) /\
    (allocas_non_overlapping (mstore8 off v s) <=>
     allocas_non_overlapping s)
Proof
  simp[mstore8_def, LET_THM, lookup_var_def,
       in_promoted_region_def, allocas_non_overlapping_def]
QED

(* mcopy preserves non-memory fields *)
Theorem mcopy_preserves:
  !dst src sz s.
    (mcopy dst src sz s).vs_current_bb = s.vs_current_bb /\
    (mcopy dst src sz s).vs_prev_bb = s.vs_prev_bb /\
    (mcopy dst src sz s).vs_transient = s.vs_transient /\
    ((mcopy dst src sz s).vs_halted <=> s.vs_halted) /\
    (mcopy dst src sz s).vs_returndata = s.vs_returndata /\
    (mcopy dst src sz s).vs_accounts = s.vs_accounts /\
    (mcopy dst src sz s).vs_call_ctx = s.vs_call_ctx /\
    (mcopy dst src sz s).vs_tx_ctx = s.vs_tx_ctx /\
    (mcopy dst src sz s).vs_block_ctx = s.vs_block_ctx /\
    (mcopy dst src sz s).vs_logs = s.vs_logs /\
    (mcopy dst src sz s).vs_immutables = s.vs_immutables /\
    (mcopy dst src sz s).vs_data_section = s.vs_data_section /\
    (mcopy dst src sz s).vs_labels = s.vs_labels /\
    (mcopy dst src sz s).vs_code = s.vs_code /\
    (mcopy dst src sz s).vs_params = s.vs_params /\
    (mcopy dst src sz s).vs_fmp = s.vs_fmp /\
    (mcopy dst src sz s).vs_initial_fmp = s.vs_initial_fmp /\
    (mcopy dst src sz s).vs_return_pc_token = s.vs_return_pc_token /\
    (mcopy dst src sz s).vs_prev_hashes = s.vs_prev_hashes /\
    (mcopy dst src sz s).vs_allocas = s.vs_allocas /\
    (mcopy dst src sz s).vs_alloca_next = s.vs_alloca_next /\
    (!x. lookup_var x (mcopy dst src sz s) = lookup_var x s) /\
    (!i. in_promoted_region fn (mcopy dst src sz s) i <=>
         in_promoted_region fn s i) /\
    (allocas_non_overlapping (mcopy dst src sz s) <=>
     allocas_non_overlapping s)
Proof
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def,
       in_promoted_region_def, allocas_non_overlapping_def]
QED

(* mem_byte outside write range is unchanged by write_memory_with_expansion *)
Triviality mem_byte_wmwe_outside:
  !off bytes s i.
    (i < off \/ off + LENGTH bytes <= i) ==>
    mem_byte i (write_memory_with_expansion off bytes s) = mem_byte i s
Proof
  rpt strip_tac >>
  simp[mem_byte_def, write_memory_with_expansion_def, LET_THM] >>
  qabbrev_tac `mem = s.vs_memory` >>
  qabbrev_tac `k = if off + LENGTH bytes > LENGTH mem
                    then off + LENGTH bytes - LENGTH mem else 0` >>
  `(if off + LENGTH bytes > LENGTH mem
    then mem ++ REPLICATE (off + LENGTH bytes - LENGTH mem) 0w
    else mem) = mem ++ REPLICATE k 0w` by
    (unabbrev_all_tac >> IF_CASES_TAC >> simp[]) >>
  `off + LENGTH bytes <= k + LENGTH mem` by
    (unabbrev_all_tac >> IF_CASES_TAC >> simp[]) >>
  simp[] >>
  mp_tac (Q.SPECL [`off`, `k`, `mem`, `bytes`, `i`]
    EL_default_splice_padded) >>
  simp[LET_THM, LENGTH_TAKE]
QED

(* Inside write range, mem_byte returns the written byte *)
Triviality mem_byte_wmwe_inside:
  !off bytes s i.
    off <= i /\ i < off + LENGTH bytes ==>
    mem_byte i (write_memory_with_expansion off bytes s) = EL (i - off) bytes
Proof
  rpt strip_tac >>
  simp[mem_byte_def, write_memory_with_expansion_def, LET_THM] >>
  qabbrev_tac `n = off + LENGTH bytes` >>
  qabbrev_tac `exp = if n > LENGTH s.vs_memory
                      then s.vs_memory ++ REPLICATE (n - LENGTH s.vs_memory) 0w
                      else s.vs_memory` >>
  `n <= LENGTH exp` by (unabbrev_all_tac >> IF_CASES_TAC >> simp[]) >>
  `off <= LENGTH exp` by simp[] >>
  `LENGTH (TAKE off exp) = off` by simp[LENGTH_TAKE] >>
  simp[EL_APPEND_EQN]
QED

Triviality mem_byte_wmwe_agree:
  !off bytes s1 s2 i.
    (!j. (j < off \/ off + LENGTH bytes <= j) ==>
         mem_byte j s1 = mem_byte j s2) ==>
    mem_byte i (write_memory_with_expansion off bytes s1) =
    mem_byte i (write_memory_with_expansion off bytes s2)
Proof
  rpt strip_tac >>
  Cases_on `i < off \/ off + LENGTH bytes <= i`
  >- (mp_tac (Q.SPECL [`off`,`bytes`,`s1`,`i`] mem_byte_wmwe_outside) >>
      mp_tac (Q.SPECL [`off`,`bytes`,`s2`,`i`] mem_byte_wmwe_outside) >>
      simp[] >> metis_tac[])
  >> gvs[] >> simp[mem_byte_wmwe_inside]
QED

(* If two states agree on 32 bytes at offset, mload returns same value *)
Theorem mload_mem_byte_eq:
  !off s1 s2.
    (!j. j < 32 ==> mem_byte (off + j) s1 = mem_byte (off + j) s2) ==>
    mload off s1 = mload off s2
Proof
  rpt strip_tac >> simp[mload_def, LET_THM] >>
  AP_TERM_TAC >> irule LIST_EQ >>
  simp[LENGTH_TAKE_EQ] >> rpt strip_tac >>
  simp[EL_TAKE, EL_APPEND_EQN, EL_DROP, EL_REPLICATE, mem_byte_def] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[mem_byte_def] >>
  Cases_on `off + x < LENGTH s1.vs_memory` >>
  Cases_on `off + x < LENGTH s2.vs_memory` >> simp[]
QED

(* A promoted 32-byte region [base,base+32) is disjoint from any range
   that doesn't overlap promoted regions *)
Theorem promoted_region_disjoint_from_nonpromoted:
  !fn s b aid off len.
    0 < len /\
    aid IN m2v_promoted_ids fn /\
    FLOOKUP s.vs_allocas aid = SOME (b, 32) /\
    (!addr. off <= addr /\ addr < off + len ==> ~in_promoted_region fn s addr) ==>
    b + 32 <= off \/ off + len <= b
Proof
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  fs[arithmeticTheory.NOT_LESS_EQUAL] >>
  Cases_on `off <= b`
  >- (first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
      rewrite_tac[in_promoted_region_def] >>
      qexistsl [`aid`, `b`] >> simp[])
  >> (first_x_assum (qspec_then `off` mp_tac) >>
      simp[] >>
      rewrite_tac[in_promoted_region_def] >>
      qexistsl [`aid`, `b`] >> simp[])
QED

(* mload unchanged by wmwe to disjoint range — parallel to mload_mstore_disjoint *)
Theorem mload_wmwe_disjoint:
  !off_r off_w bytes s.
    off_r + 32 <= off_w \/ off_w + LENGTH bytes <= off_r ==>
    mload off_r (write_memory_with_expansion off_w bytes s) = mload off_r s
Proof
  rpt strip_tac >> irule mload_mem_byte_eq >> rpt strip_tac >>
  irule mem_byte_wmwe_outside >> simp[]
QED

(* mload unchanged by empty wmwe *)
Triviality mload_wmwe_nil:
  !off_r off_w s.
    mload off_r (write_memory_with_expansion off_w [] s) = mload off_r s
Proof
  rpt strip_tac >> irule mload_mem_byte_eq >> rpt strip_tac >>
  irule mem_byte_wmwe_outside >> simp[]
QED

(* m2v_inv_noix preserved when both sides do write_memory_with_expansion
   with the same offset and bytes, to a nonpromoted region *)
Theorem m2v_inv_noix_both_sides_wmwe:
  !fn s1 s2 off bytes.
    m2v_inv_noix fn s1 s2 /\
    m2v_non32_ok fn s1 s2 /\
    (!addr. off <= addr /\ addr < off + LENGTH bytes ==>
            ~in_promoted_region fn s1 addr) ==>
    m2v_inv_noix fn
      (write_memory_with_expansion off bytes s1)
      (write_memory_with_expansion off bytes s2)
Proof
  rpt strip_tac >>
  fs[m2v_inv_noix_def] >>
  simp[m2v_inv_noix_def, wmwe_preserves] >> rpt conj_tac
  >- (rpt strip_tac >>
      Cases_on `off <= i /\ i < off + LENGTH bytes`
      >- simp[mem_byte_wmwe_inside]
      >> `i < off \/ off + LENGTH bytes <= i` by simp[] >>
         simp[mem_byte_wmwe_outside])
  >- metis_tac[]
  >> rpt strip_tac >> simp[wmwe_preserves] >>
  Cases_on `sz = 32`
  >- suspend "wmwe_sync32"
  >> fs[m2v_non32_ok_def] >> res_tac >> simp[wmwe_preserves] >> gvs[]
QED

Resume m2v_inv_noix_both_sides_wmwe[wmwe_sync32]:
  gvs[] >>
  `lookup_var pvar s2 = SOME (mload (w2n addr) s1)` by metis_tac[] >>
  `mload (w2n addr) (write_memory_with_expansion off bytes s1) =
   mload (w2n addr) s1` suffices_by simp[] >>
  `?ai. MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\
        ai.inst_outputs = [ao] /\ ai.inst_id IN m2v_promoted_ids fn`
    by metis_tac[m2v_promo_list_inst_in_promoted_ids] >>
  `FLOOKUP s1.vs_allocas ai.inst_id = SOME (w2n addr, 32)` by
    (qpat_x_assum `!ao' pvar' sz' inst. _`
       (qspecl_then [`ao`,`pvar`,`32`,`ai`] mp_tac) >>
     simp[]) >>
  Cases_on `bytes` >- simp[mload_wmwe_nil] >>
  `w2n addr + 32 <= off \/ off + LENGTH (h::t) <= w2n addr` by
    (mp_tac promoted_region_disjoint_from_nonpromoted >>
     disch_then (qspecl_then [`fn`,`s1`,`w2n addr`,`ai.inst_id`,
                              `off`,`LENGTH (h::t)`] mp_tac) >>
     simp[]) >>
  metis_tac[mload_wmwe_disjoint]
QED

Finalise m2v_inv_noix_both_sides_wmwe

(* update_var preserves all non-var fields, allocas, in_promoted_region *)
Theorem update_var_preserves:
  !x v s.
    (update_var x v s).vs_current_bb = s.vs_current_bb /\
    (update_var x v s).vs_prev_bb = s.vs_prev_bb /\
    (update_var x v s).vs_transient = s.vs_transient /\
    ((update_var x v s).vs_halted <=> s.vs_halted) /\
    (update_var x v s).vs_returndata = s.vs_returndata /\
    (update_var x v s).vs_accounts = s.vs_accounts /\
    (update_var x v s).vs_call_ctx = s.vs_call_ctx /\
    (update_var x v s).vs_tx_ctx = s.vs_tx_ctx /\
    (update_var x v s).vs_block_ctx = s.vs_block_ctx /\
    (update_var x v s).vs_logs = s.vs_logs /\
    (update_var x v s).vs_immutables = s.vs_immutables /\
    (update_var x v s).vs_data_section = s.vs_data_section /\
    (update_var x v s).vs_labels = s.vs_labels /\
    (update_var x v s).vs_code = s.vs_code /\
    (update_var x v s).vs_params = s.vs_params /\
    (update_var x v s).vs_fmp = s.vs_fmp /\
    (update_var x v s).vs_initial_fmp = s.vs_initial_fmp /\
    (update_var x v s).vs_return_pc_token = s.vs_return_pc_token /\
    (update_var x v s).vs_prev_hashes = s.vs_prev_hashes /\
    (update_var x v s).vs_allocas = s.vs_allocas /\
    (update_var x v s).vs_alloca_next = s.vs_alloca_next /\
    (!y. mem_byte y (update_var x v s) = mem_byte y s) /\
    (!i. in_promoted_region fn (update_var x v s) i <=>
         in_promoted_region fn s i) /\
    (allocas_non_overlapping (update_var x v s) <=>
     allocas_non_overlapping s)
Proof
  simp[update_var_def, mem_byte_def, in_promoted_region_def,
       allocas_non_overlapping_def]
QED

Theorem lookup_var_update:
  !x v s y. lookup_var y (update_var x v s) =
    if x = y then SOME v else lookup_var y s
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Extract sync clause from m2v_inv_noix without destroying the invariant *)
Theorem m2v_inv_noix_sync:
  !fn s1 s2 ao pvar sz addr.
    m2v_inv_noix fn s1 s2 /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\
    lookup_var ao s1 = SOME addr /\
    IS_SOME (lookup_var pvar s2) ==>
    lookup_var pvar s2 = SOME (mload (w2n addr) s1)
Proof
  rpt strip_tac >> gvs[m2v_inv_noix_def] >> metis_tac[]
QED

(* lookup_var agreement for non-fresh vars *)
Theorem m2v_inv_noix_lookup_agrees:
  !fn s1 s2 v. m2v_inv_noix fn s1 s2 /\ v NOTIN m2v_fresh_vars fn ==>
    lookup_var v s1 = lookup_var v s2
Proof
  rw[m2v_inv_noix_def]
QED

(* eval_operand agreement for instructions in fn *)
Theorem m2v_inv_noix_eval_agrees:
  !fn inst s1 s2 op.
    m2v_inv_noix fn s1 s2 /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\ MEM op inst.inst_operands ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`, `inst`, `s1`, `s2`, `op`]
    m2v_step_operand_agrees) >>
  simp[] >>
  disch_then irule >>
  qpat_x_assum `m2v_inv_noix _ _ _`
    (strip_assume_tac o REWRITE_RULE [m2v_inv_noix_def]) >> simp[]
QED

(* Extract functional bridge: given the ALLOCA instruction for ao, get FLOOKUP *)
Theorem m2v_inv_noix_bridge_inst:
  !fn s1 s2 ao pvar sz inst addr.
    m2v_inv_noix fn s1 s2 /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ao] /\
    lookup_var ao s1 = SOME addr ==>
    FLOOKUP s1.vs_allocas inst.inst_id = SOME (w2n addr, sz)
Proof
  rpt strip_tac >> fs[m2v_inv_noix_def] >> metis_tac[]
QED

(* Derive existential bridge for backward compatibility *)
Theorem m2v_inv_noix_alloca_bridge:
  !fn s1 s2 ao pvar sz addr.
    m2v_inv_noix fn s1 s2 /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\
    lookup_var ao s1 = SOME addr ==>
    ?inst_id. inst_id IN m2v_promoted_ids fn /\
              FLOOKUP s1.vs_allocas inst_id = SOME (w2n addr, sz)
Proof
  rpt strip_tac >>
  drule m2v_promo_list_inst_in_promoted_ids >> strip_tac >>
  drule_all m2v_inv_noix_bridge_inst >>
  metis_tac[]
QED

(* Extract addr-in-region clause from m2v_inv_noix (derived from bridge).
   Only works for sz=32 entries since in_promoted_region is narrowed to sz=32. *)
Theorem m2v_inv_noix_addr_in_region:
  !fn s1 s2 ao pvar addr.
    m2v_inv_noix fn s1 s2 /\
    MEM (ao, pvar, 32) (m2v_promo_list fn) /\
    lookup_var ao s1 = SOME addr ==>
    !i. w2n addr <= i /\ i < w2n addr + 32 ==>
        in_promoted_region fn s1 i
Proof
  rpt strip_tac >>
  drule_all m2v_inv_noix_alloca_bridge >> strip_tac >>
  simp[in_promoted_region_def] >>
  metis_tac[]
QED

(* Bytes at a sz<>32 alloca base are NOT in any promoted region.
   Key: allocas_non_overlapping + sz>=32 means the 32-byte read/write
   window at the base is within the alloca's region, which is disjoint
   from all sz=32 allocas. *)
Theorem m2v_inv_noix_addr_not_in_region:
  !fn s1 s2 ao pvar sz addr.
    m2v_inv_noix fn s1 s2 /\
    wf_function fn /\ ssa_form fn /\
    m2v_promo_sizes_bounded fn /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\
    sz <> 32 /\
    lookup_var ao s1 = SOME addr ==>
    !i. w2n addr <= i /\ i < w2n addr + 32 ==>
      ~in_promoted_region fn s1 i
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  CCONTR_TAC >> gvs[in_promoted_region_def] >>
  drule_all m2v_inv_noix_alloca_bridge >> strip_tac >>
  Cases_on `inst_id = aid`
  >- gvs[]
  >> `allocas_non_overlapping s1` by fs[m2v_inv_noix_def] >>
  fs[allocas_non_overlapping_def] >>
  first_x_assum (qspecl_then [`inst_id`, `aid`] mp_tac) >> simp[] >>
  `sz = 32` by (fs[m2v_promo_sizes_bounded_def] >> res_tac) >>
  simp[]
QED


(* Corollary: mload at a sz<>32 alloca base agrees between s1 and s2 *)
Theorem m2v_inv_noix_mload_agrees_non32:
  !fn s1 s2 ao pvar sz addr.
    m2v_inv_noix fn s1 s2 /\
    wf_function fn /\ ssa_form fn /\
    m2v_promo_sizes_bounded fn /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\
    sz <> 32 /\
    lookup_var ao s1 = SOME addr ==>
    mload (w2n addr) s1 = mload (w2n addr) s2
Proof
  rpt strip_tac >>
  irule mload_mem_byte_eq >> rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`,`s1`,`s2`,`ao`,`pvar`,`sz`,`addr`]
    m2v_inv_noix_addr_not_in_region) >>
  simp[] >> disch_then (qspec_then `w2n addr + j` mp_tac) >> simp[] >>
  strip_tac >> fs[m2v_inv_noix_def]
QED

(* Two distinct promo entries with distinct ao's have disjoint regions
   and distinct pvars. Key for mstore/mload dispatch. *)
Theorem m2v_inv_noix_regions_disjoint:
  !fn s1 s2 ao pvar sz ao2 pvar2 sz2 a1 a2.
    m2v_inv_noix fn s1 s2 /\
    wf_function fn /\ ssa_form fn /\
    allocas_non_overlapping s1 /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\
    MEM (ao2, pvar2, sz2) (m2v_promo_list fn) /\
    ao <> ao2 /\
    lookup_var ao s1 = SOME a1 /\
    lookup_var ao2 s1 = SOME a2 ==>
    regions_disjoint (w2n a1, sz) (w2n a2, sz2) /\ pvar <> pvar2
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- suspend "reg"
  >> suspend "pvar"
QED

Resume m2v_inv_noix_regions_disjoint[reg]:
  qpat_assum `MEM (ao,_,_) _`
    (qx_choose_then `i1` strip_assume_tac o
     MATCH_MP m2v_promo_list_is_alloca) >>
  qpat_assum `MEM (ao2,_,_) _`
    (qx_choose_then `i2` strip_assume_tac o
     MATCH_MP m2v_promo_list_is_alloca) >>
  mp_tac (Q.SPECL [`fn`,`s1`,`s2`,`ao`,`pvar`,`sz`,`i1`,`a1`]
    m2v_inv_noix_bridge_inst) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`fn`,`s1`,`s2`,`ao2`,`pvar2`,`sz2`,`i2`,`a2`]
    m2v_inv_noix_bridge_inst) >> simp[] >> strip_tac >>
  suspend "id_neq"
QED

Resume m2v_inv_noix_regions_disjoint[id_neq]:
  `i1.inst_id <> i2.inst_id` by
    (CCONTR_TAC >> fs[] >>
     mp_tac (Q.SPECL [`fn`,`i1`,`i2`] wf_fn_inst_id_inj) >>
     (impl_tac >- simp[]) >>
     strip_tac >> gvs[]) >>
  gvs[allocas_non_overlapping_def, regions_disjoint_def] >>
  first_x_assum (qspecl_then [`i1.inst_id`,`i2.inst_id`] mp_tac) >>
  simp[]
QED

Resume m2v_inv_noix_regions_disjoint[pvar]:
  CCONTR_TAC >> gvs[] >>
  mp_tac (Q.SPECL [`fn`,`ao`,`pvar`,`sz`,`ao2`,`sz2`]
    m2v_promo_list_pvar_unique) >> simp[]
QED

Finalise m2v_inv_noix_regions_disjoint

Theorem mload_update_var[simp]:
  !off x v s. mload off (update_var x v s) = mload off s
Proof
  simp[mload_def, update_var_def]
QED

(* update_var with same value on both sides preserves m2v_inv_noix.
   When x is not an ao in promo_list, bridge/sync preconditions are vacuous. *)
Theorem m2v_inv_noix_update_var:
  !fn s1 s2 x val.
    m2v_inv_noix fn s1 s2 /\
    x NOTIN m2v_fresh_vars fn /\
    (* Bridge for entries where x = ao *)
    (!ao pvar sz inst. MEM (ao,pvar,sz) (m2v_promo_list fn) /\ x = ao /\
       MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_outputs = [ao] ==>
       FLOOKUP s1.vs_allocas inst.inst_id = SOME (w2n val, sz)) /\
    (* Sync for entries where x = ao *)
    (!ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) /\ x = ao ==>
       IS_SOME (lookup_var pvar s2) ==>
       lookup_var pvar s2 = SOME (mload (w2n val) s1))
    ==>
    m2v_inv_noix fn (update_var x val s1) (update_var x val s2)
Proof
  rpt strip_tac >>
  qpat_x_assum `m2v_inv_noix fn s1 s2` mp_tac >>
  simp[m2v_inv_noix_def] >> strip_tac >>
  simp[m2v_inv_noix_def, update_var_preserves, lookup_var_update] >>
  rpt conj_tac
  (* bridge *)
  >- (rpt gen_tac >> strip_tac >> gen_tac >>
      rename1 `MEM (ao2,pvar2,sz2) _` >>
      Cases_on `x = ao2` >> gvs[] >>
      metis_tac[])
  (* sync *)
  >> rpt gen_tac >> strip_tac >> gen_tac >>
  rename1 `MEM (ao2,pvar2,sz2) _` >>
  `pvar2 <> x` by
    (strip_tac >> gvs[] >>
     imp_res_tac m2v_promo_list_in_fresh_vars >> gvs[]) >>
  simp[] >>
  Cases_on `x = ao2` >> gvs[] >>
  metis_tac[]
QED

Theorem m2v_step_nonpromoted_dalloca:
  !fn inst s1 s2 fuel ctx v1.
    m2v_inv_noix fn s1 s2 /\
    inst.inst_opcode = DALLOCA /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
    (!ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
       ~MEM ao inst.inst_outputs) /\
    step_inst fuel ctx inst s1 = OK v1 ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\
         m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >>
  `s1.vs_fmp = s2.vs_fmp` by gvs[m2v_inv_noix_def] >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  qabbrev_tac `t1 = s1 with vs_fmp :=
    s2.vs_fmp + n2w (ceil32 (w2n sz))` >>
  qabbrev_tac `t2 = s2 with vs_fmp :=
    s2.vs_fmp + n2w (ceil32 (w2n sz))` >>
  `m2v_inv_noix fn t1 t2` by (
    gvs[Abbr `t1`, Abbr `t2`, m2v_inv_noix_def,
        lookup_var_def, mem_byte_def, mload_def, in_promoted_region_def,
        allocas_non_overlapping_def] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists `update_var out s2.vs_fmp t2` >>
  conj_tac
  >- (qexists `sz` >> simp[Abbr `t2`]) >>
  simp[Abbr `t1`, Abbr `t2`] >>
  qpat_assum `m2v_inv_noix fn (s1 with vs_fmp := _) _`
    (assume_tac o ONCE_REWRITE_RULE [wordsTheory.WORD_ADD_COMM]) >>
  irule m2v_inv_noix_update_var >>
  simp[] >> metis_tac[]
QED

(* alloca insert preserves allocas_non_overlapping when:
   (1) old map is non-overlapping AND all entries end before new_base
   (2) new key is fresh (FLOOKUP NONE)
   Follows from alloca_inv = allocas_non_overlapping + alloca_next_valid *)
Theorem allocas_non_overlapping_insert:
  !s new_id new_base new_sz.
    alloca_inv s /\
    FLOOKUP s.vs_allocas new_id = NONE /\
    s.vs_alloca_next <= new_base ==>
    allocas_non_overlapping
      (s with vs_allocas := s.vs_allocas |+ (new_id, (new_base, new_sz)))
Proof
  rpt strip_tac >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  rpt strip_tac >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
  res_tac >> simp[]
QED

(* Identical allocas + alloca_next update preserves m2v_inv_noix.
   Both sides get exactly the same record update, so all clauses transfer.
   Requires: new allocas_non_overlapping, and old bridge entries still valid
   (which holds because lookup_var is unchanged by allocas update). *)
Theorem m2v_inv_noix_identical_alloca_update:
  !fn s1 s2 new_allocas new_next.
    m2v_inv_noix fn s1 s2 /\
    allocas_non_overlapping
      (s1 with <|vs_allocas := new_allocas;
                  vs_alloca_next := new_next|>) /\
    (* Old alloca entries preserved *)
    (!k v. FLOOKUP s1.vs_allocas k = SOME v ==>
           FLOOKUP new_allocas k = SOME v) ==>
    m2v_inv_noix fn
      (s1 with <|vs_allocas := new_allocas;
                  vs_alloca_next := new_next|>)
      (s2 with <|vs_allocas := new_allocas;
                  vs_alloca_next := new_next|>)
Proof
  rpt strip_tac >>
  qpat_x_assum `m2v_inv_noix fn s1 s2` mp_tac >>
  simp[m2v_inv_noix_def, lookup_var_def] >> strip_tac >>
  simp[m2v_inv_noix_def, lookup_var_def] >> rpt conj_tac
  (* mem_byte: monotonicity of in_promoted_region *)
  >- (rpt strip_tac >>
      `mem_byte i (s1 with <|vs_allocas := new_allocas;
         vs_alloca_next := new_next|>) = mem_byte i s1` by
        simp[mem_byte_def] >>
      `mem_byte i (s2 with <|vs_allocas := new_allocas;
         vs_alloca_next := new_next|>) = mem_byte i s2` by
        simp[mem_byte_def] >>
      gvs[] >>
      qpat_x_assum `!i. ~in_promoted_region _ s1 _ ==> _` irule >>
      qpat_x_assum `~in_promoted_region _ _ _` mp_tac >>
      simp[in_promoted_region_def] >> metis_tac[])
  (* bridge: old FLOOKUP entry preserved *)
  >- metis_tac[]
  (* sync: mload unchanged since memory unchanged *)
  >> rpt strip_tac >>
  `mload (w2n addr) (s1 with <|vs_allocas := new_allocas;
     vs_alloca_next := new_next|>) = mload (w2n addr) s1` by
    simp[mload_def] >>
  metis_tac[]
QED

(* mem_byte inside mstore's written region depends only on val, not state *)
Theorem mem_byte_mstore_inside:
  !off (val_w:bytes32) s i.
    off <= i /\ i < off + 32 ==>
    mem_byte i (mstore off val_w s) =
    EL (i - off) (word_to_bytes val_w T)
Proof
  rpt strip_tac >>
  simp[mem_byte_def, mstore_def, LET_THM, len_word_to_bytes_256] >>
  qmatch_goalsub_abbrev_tac `TAKE off expanded` >>
  `off + 32 <= LENGTH expanded`
    by (unabbrev_all_tac >> rw[] >> simp[]) >>
  `i < LENGTH expanded` by simp[] >>
  simp[LENGTH_TAKE, len_word_to_bytes_256] >>
  `32 = LENGTH (word_to_bytes val_w T)` by simp[len_word_to_bytes_256] >>
  pop_assum SUBST1_TAC >>
  irule EL_splice_inside >> simp[len_word_to_bytes_256]
QED
(* mload is unaffected by mstore at a disjoint region *)
Theorem mload_mstore_disjoint:
  !off_r off_w (val_w:bytes32) s.
    off_r + 32 <= off_w \/ off_w + 32 <= off_r ==>
    mload off_r (mstore off_w val_w s) = mload off_r s
Proof
  rpt strip_tac >> irule mload_mem_byte_eq >> rpt strip_tac >>
  irule mem_byte_mstore_outside >> simp[]
QED

(* Both sides do mstore with same args: memory agreement preserved *)
Theorem mstore_both_sides_mem:
  !fn s1 s2 off val_w.
    (!i. ~in_promoted_region fn s1 i ==> mem_byte i s1 = mem_byte i s2) ==>
    !i. ~in_promoted_region fn s1 i ==>
        mem_byte i (mstore off val_w s1) =
        mem_byte i (mstore off val_w s2)
Proof
  rpt strip_tac >>
  Cases_on `i < off \/ off + 32 <= i`
  >- metis_tac[mem_byte_mstore_outside]
  >> `off <= i /\ i < off + 32` by simp[] >>
  metis_tac[mem_byte_mstore_inside]
QED

(* mstore at offset disjoint from all sz=32 allocas preserves
   m2v_inv_noix when applied to both sides.
   m2v_non32_ok needed so sync clause is vacuous for sz<>32 entries. *)
Theorem m2v_inv_noix_both_sides_mstore:
  !fn s1 s2 off val_w.
    m2v_inv_noix fn s1 s2 /\
    m2v_non32_ok fn s1 s2 /\
    (!ao pvar addr. MEM (ao,pvar,32) (m2v_promo_list fn) /\
      lookup_var ao s1 = SOME addr ==>
      off + 32 <= w2n addr \/ w2n addr + 32 <= off) ==>
    m2v_inv_noix fn (mstore off val_w s1) (mstore off val_w s2)
Proof
  rpt strip_tac >> fs[m2v_inv_noix_def] >>
  simp[m2v_inv_noix_def, mstore_preserves] >> rpt conj_tac
  >- (rpt strip_tac >> irule mstore_both_sides_mem >> simp[] >>
      metis_tac[])
  >- metis_tac[]  (* bridge: mstore preserves lookup_var and vs_allocas *)
  >> (* sync *)
  rpt strip_tac >> simp[mstore_preserves] >>
  Cases_on `sz = 32`
  >- (`mload (w2n addr) (mstore off val_w s1) = mload (w2n addr) s1` by
        (irule mload_mstore_disjoint >> metis_tac[]) >>
      simp[] >> metis_tac[])
  >> (* sz<>32: IS_SOME is false by m2v_non32_ok *)
  fs[m2v_non32_ok_def] >> res_tac >> simp[mstore_preserves] >>
  gvs[]
QED

Theorem m2v_inv_noix_with_immutables:
  !fn s1 s2 imm.
    m2v_inv_noix fn s1 s2 ==>
    m2v_inv_noix fn (s1 with vs_immutables := imm)
                    (s2 with vs_immutables := imm)
Proof
  rw[m2v_inv_noix_def, lookup_var_def, in_promoted_region_def,
     mem_byte_def, mload_def, allocas_non_overlapping_def] >>
  metis_tac[]
QED

Theorem m2v_inv_noix_both_sides_istore:
  !fn s1 s2 off val_w.
    m2v_inv_noix fn s1 s2 /\
    m2v_non32_ok fn s1 s2 /\
    (!ao pvar addr. MEM (ao,pvar,32) (m2v_promo_list fn) /\
      lookup_var ao s1 = SOME addr ==>
      off + 32 <= w2n addr \/ w2n addr + 32 <= off) ==>
    m2v_inv_noix fn (istore off val_w s1) (istore off val_w s2)
Proof
  rpt strip_tac >>
  `s1.vs_immutables = s2.vs_immutables` by gvs[m2v_inv_noix_def] >>
  simp[istore_def] >>
  irule m2v_inv_noix_with_immutables >>
  irule m2v_inv_noix_both_sides_mstore >> simp[] >>
  qpat_x_assum `!ao pvar addr. _` ACCEPT_TAC
QED

(* --- Memory clause helper for mstore_core --- *)
Theorem mstore_core_mem_clause:
  !fn s1 s2 addr val_w.
    (!i. ~in_promoted_region fn s1 i ==> mem_byte i s1 = mem_byte i s2) /\
    (!i. w2n addr <= i /\ i < w2n addr + 32 ==>
         in_promoted_region fn s1 i) ==>
    !i. ~in_promoted_region fn s1 i ==>
        mem_byte i (mstore (w2n addr) val_w s1) = mem_byte i s2
Proof
  rpt strip_tac >>
  Cases_on `i < w2n addr` >- metis_tac[mem_byte_mstore_outside] >>
  Cases_on `w2n addr + 32 <= i` >- metis_tac[mem_byte_mstore_outside] >>
  `w2n addr <= i /\ i < w2n addr + 32` by simp[] >>
  metis_tac[]
QED

(* --- Sync clause helper for mstore_core --- *)
Theorem mstore_core_sync_clause:
  !fn s1 s2 ao pvar addr val_w.
    (!ao2 pvar2 sz2.
       MEM (ao2,pvar2,sz2) (m2v_promo_list fn) ==>
       !addr2. lookup_var ao2 s1 = SOME addr2 ==>
         IS_SOME (lookup_var pvar2 s2) ==>
         lookup_var pvar2 s2 = SOME (mload (w2n addr2) s1)) /\
    lookup_var ao s1 = SOME addr /\
    MEM (ao,pvar,32) (m2v_promo_list fn) /\
    (!ao2 pvar2 sz2 a2.
       MEM (ao2,pvar2,sz2) (m2v_promo_list fn) /\
       (ao,pvar,32) <> (ao2,pvar2,sz2) /\
       lookup_var ao2 s1 = SOME a2 ==>
       regions_disjoint (w2n addr,32) (w2n a2,32) /\
       pvar <> pvar2) ==>
    !ao2 pvar2 sz2.
      MEM (ao2,pvar2,sz2) (m2v_promo_list fn) ==>
      !addr2. lookup_var ao2 s1 = SOME addr2 ==>
        IS_SOME (if pvar = pvar2 then SOME val_w
                 else lookup_var pvar2 s2) ==>
        (if pvar = pvar2 then SOME val_w else lookup_var pvar2 s2) =
        SOME (mload (w2n addr2) (mstore (w2n addr) val_w s1))
Proof
  rpt strip_tac >> Cases_on `pvar = pvar2`
  >- (* Same pvar => same entry *)
     (`(ao,pvar,32) = (ao2,pvar2,sz2)` by
        (CCONTR_TAC >>
         qpat_x_assum `!a b c d. _ ==> regions_disjoint _ _ /\ _`
           (qspecl_then [`ao2`,`pvar2`,`sz2`,`addr2`] mp_tac) >>
         gvs[]) >>
      gvs[] >> simp[mload_mstore_same_proof])
  >> (* Different pvar => disjoint *)
     simp[] >>
     `regions_disjoint (w2n addr,32) (w2n addr2,32)` by
       (qpat_x_assum `!a b c d. _ ==> regions_disjoint _ _ /\ _`
          (qspecl_then [`ao2`,`pvar2`,`sz2`,`addr2`] mp_tac) >>
        gvs[]) >>
     `mload (w2n addr2) (mstore (w2n addr) val_w s1) = mload (w2n addr2) s1`
       by metis_tac[mload_mstore_disjoint_proof] >>
     simp[] >>
     `IS_SOME (lookup_var pvar2 s2)` by gvs[] >>
     metis_tac[]
QED

(* Core step lemma for promoted MSTORE. *)
Theorem m2v_step_promoted_mstore_core:
  !fn s1 s2 ao pvar val_op addr val_w.
    m2v_inv_noix fn s1 s2 /\
    pvar IN m2v_fresh_vars fn /\
    lookup_var ao s1 = SOME addr /\
    eval_operand val_op s1 = SOME val_w /\
    eval_operand val_op s2 = SOME val_w /\
    ao NOTIN m2v_fresh_vars fn /\
    (* Written region is in promoted region *)
    (!i. w2n addr <= i /\ i < w2n addr + 32 ==>
         in_promoted_region fn s1 i) /\
    (* Different promo entries have disjoint regions AND distinct pvars *)
    (!ao2 pvar2 sz2 a2.
       MEM (ao2, pvar2, sz2) (m2v_promo_list fn) /\
       (ao, pvar, 32) <> (ao2, pvar2, sz2) /\
       lookup_var ao2 s1 = SOME a2 ==>
       regions_disjoint (w2n addr, 32) (w2n a2, sz2) /\
       pvar <> pvar2 /\
       (IS_SOME (lookup_var pvar2 s2) ==> sz2 >= 32)) /\
    MEM (ao, pvar, 32) (m2v_promo_list fn) ==>
    m2v_inv_noix fn
      (mstore (w2n addr) val_w s1)
      (update_var pvar val_w s2)
Proof
  rpt strip_tac >> fs[m2v_inv_noix_def] >>
  simp[m2v_inv_noix_def, mstore_preserves, update_var_preserves,
       lookup_var_update] >>
  rpt conj_tac
  >- suspend "var"
  >- suspend "mem"
  >- metis_tac[]
  >> suspend "sync"
QED

Resume m2v_step_promoted_mstore_core[var]:
  rpt strip_tac >>
  Cases_on `pvar = v` >> gvs[]
QED

Resume m2v_step_promoted_mstore_core[mem]:
  rpt strip_tac >>
  Cases_on `i < w2n addr` >- metis_tac[mem_byte_mstore_outside] >>
  Cases_on `w2n addr + 32 <= i` >- metis_tac[mem_byte_mstore_outside] >>
  `w2n addr <= i /\ i < w2n addr + 32` by simp[] >>
  metis_tac[]
QED

Resume m2v_step_promoted_mstore_core[sync]:
  rpt strip_tac >>
  rename1 `MEM (ao2,pvar2,sz2) (m2v_promo_list fn)` >>
  rename1 `lookup_var ao2 s1 = SOME addr2` >>
  Cases_on `pvar = pvar2`
  >- (`(ao,pvar,32) = (ao2,pvar2,sz2)` by
        (CCONTR_TAC >>
         qpat_x_assum `!a b c d. _ ==> _ /\ _ /\ _`
           (qspecl_then [`ao2`,`pvar2`,`sz2`,`addr2`] mp_tac) >>
         gvs[]) >>
      gvs[] >> simp[mload_mstore_same_proof])
  >> simp[] >>
     (* IS_SOME holds because sync obligation is guarded by it *)
     (`IS_SOME (lookup_var pvar2 s2)` by gvs[]) >>
     (* Get disjointness + sz2 >= 32 *)
     (qpat_x_assum `!a b c d. _ ==> _ /\ _ /\ _`
        (qspecl_then [`ao2`,`pvar2`,`sz2`,`addr2`] mp_tac) >>
      gvs[] >> strip_tac) >>
     (* Derive 32-byte disjointness from sz2 >= 32 *)
     (`regions_disjoint (w2n addr,32) (w2n addr2,32)` by
       (gvs[regions_disjoint_def] >> decide_tac)) >>
     (`mload (w2n addr2) (mstore (w2n addr) val_w s1) = mload (w2n addr2) s1`
       by metis_tac[mload_mstore_disjoint_proof]) >>
     simp[] >> metis_tac[]
QED

Finalise m2v_step_promoted_mstore_core

Theorem m2v_step_promoted_mstore:
  !fn inst s1 s2 fuel ctx ao pvar sz v1 val_op.
    m2v_inv_noix fn s1 s2 /\
    inst.inst_opcode = MSTORE /\ sz = 32 /\
    inst.inst_operands = [Var ao; val_op] /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\
    ao NOTIN m2v_fresh_vars fn /\
    (* val_op evaluates identically (non-fresh operand) *)
    (!v. val_op = Var v ==> v NOTIN m2v_fresh_vars fn) /\
    (* Written region is in promoted region *)
    (!addr i. lookup_var ao s1 = SOME addr /\
              w2n addr <= i /\ i < w2n addr + 32 ==>
              in_promoted_region fn s1 i) /\
    (* Different promo entries have disjoint regions and distinct pvars *)
    (!ao2 pvar2 sz2 a1 a2.
       MEM (ao2, pvar2, sz2) (m2v_promo_list fn) /\
       (ao, pvar, sz) <> (ao2, pvar2, sz2) /\
       lookup_var ao s1 = SOME a1 /\ lookup_var ao2 s1 = SOME a2 ==>
       regions_disjoint (w2n a1, 32) (w2n a2, sz2) /\
       pvar <> pvar2 /\
       (IS_SOME (lookup_var pvar2 s2) ==> sz2 >= 32)) /\
    step_inst fuel ctx inst s1 = OK v1 ==>
    ?v2. step_inst fuel ctx
           (inst with <| inst_opcode := ASSIGN;
                         inst_operands := [val_op];
                         inst_outputs := [pvar] |>) s2 = OK v2 /\
         m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
      eval_operand_def, AllCaseEqs()] >>
  rename1 `eval_operand val_op s1 = SOME val_w` >>
  `eval_operand val_op s2 = SOME val_w` by
    metis_tac[m2v_inv_noix_eval_operand] >>
  qexists `update_var pvar val_w s2` >> simp[] >>
  irule m2v_step_promoted_mstore_core >>
  metis_tac[m2v_promo_list_in_fresh_vars]
QED

(* ================================================================
   PER-INSTRUCTION SIMULATION (promoted MLOAD case)
   MLOAD [Var ao] output [out] -> ASSIGN [Var pvar] output [out]
   ================================================================ *)

Theorem m2v_step_promoted_mload:
  !fn inst s1 s2 fuel ctx ao pvar sz v1.
    m2v_inv_noix fn s1 s2 /\
    inst.inst_opcode = MLOAD /\ sz = 32 /\
    inst.inst_operands = [Var ao] /\
    MEM (ao, pvar, sz) (m2v_promo_list fn) /\
    IS_SOME (lookup_var pvar s2) /\
    (* Output variable is not fresh and not any promo ao *)
    (!out. MEM out inst.inst_outputs ==>
           out NOTIN m2v_fresh_vars fn /\
           !ao2 pvar2 sz2. MEM (ao2,pvar2,sz2) (m2v_promo_list fn) ==>
             out <> ao2) /\
    step_inst fuel ctx inst s1 = OK v1 ==>
    ?v2. step_inst fuel ctx
           (inst with <| inst_opcode := ASSIGN;
                         inst_operands := [Var pvar] |>) s2 = OK v2 /\
         m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >> suspend "base"
QED

Resume m2v_step_promoted_mload[base]:
  gvs[step_inst_base_def] >> suspend "exec"
QED

Resume m2v_step_promoted_mload[exec]:
  gvs[exec_read1_def, eval_operand_def, AllCaseEqs()] >> suspend "main"
QED

Resume m2v_step_promoted_mload[main]:
  (* sync: pvar in s2 = mload addr s1, so both sides update same value *)
  mp_tac (Q.SPECL [`fn`,`s1`,`s2`,`ao`,`pvar`,`32`,`addr`]
    m2v_inv_noix_sync) >>
  simp[] >> strip_tac >> gvs[] >>
  irule m2v_inv_noix_update_var >> simp[]
QED

Finalise m2v_step_promoted_mload

(* ================================================================
   MAIN THEOREM: m2v_per_block_sim
   (proved here instead of mem2varProofsScript to use helpers)
   ================================================================ *)

(* Helper: for non-terminal instruction at index i in a well-formed block,
   stepping preserves m2v_inv_noix. Dispatches to nonpromoted/mstore/mload. *)
(* Helper: MEM (Var v) ops ==> MEM v (operand_vars ops) *)
Theorem MEM_Var_operand_vars:
  !v ops. MEM (Var v) ops ==> MEM v (operand_vars ops)
Proof
  Induct_on `ops` >> rw[operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_vars_def] >>
  Cases_on `h` >> gvs[operand_var_def]
QED

(* Helper: if FIND returns SOME (ao,pvar,sz) from promo_list, the inst
   uses ao and therefore m2v_can_promote_alloca constrains its opcode *)
Theorem promo_find_inst_opcode:
  !fn inst ao pvar sz.
    FIND (\(ao,_,_). MEM (Var ao) inst.inst_operands) (m2v_promo_list fn) =
      SOME (ao,pvar,sz) /\
    MEM inst (fn_insts fn) ==>
    inst.inst_opcode = MSTORE \/ inst.inst_opcode = MLOAD \/
    inst.inst_opcode = RETURN
Proof
  rpt strip_tac >>
  imp_res_tac FIND_MEM >>
  imp_res_tac FIND_P >> gvs[] >>
  drule MEM_Var_operand_vars >> strip_tac >>
  drule_all dfg_build_function_uses_complete_proof >> strip_tac >>
  drule m2v_promo_list_can_promote >>
  simp[m2v_can_promote_alloca_def, EVERY_MEM]
QED

(* When promote_inst actually changes the instruction, derive format *)
Theorem m2v_promote_mload_format:
  !inst ao pvar sz. inst.inst_opcode = MLOAD /\
    MEM (Var ao) inst.inst_operands /\
    m2v_promote_inst pvar ao sz inst <> [inst] ==>
    sz = 32 /\ inst.inst_operands = [Var ao]
Proof
  rpt strip_tac >> fs[m2v_promote_inst_def] >>
  every_case_tac >> gvs[]
QED

Theorem m2v_promote_mstore_format:
  !inst ao pvar sz. inst.inst_opcode = MSTORE /\
    MEM (Var ao) inst.inst_operands /\
    m2v_promote_inst pvar ao sz inst <> [inst] ==>
    sz = 32 /\ ?val_op. inst.inst_operands = [Var ao; val_op]
Proof
  rpt strip_tac >> fs[m2v_promote_inst_def] >>
  every_case_tac >> gvs[]
QED

(* RETURN promotion: derive operand format, sz bound, and expansion *)
Theorem m2v_promote_return_format:
  !inst ao pvar sz. inst.inst_opcode = RETURN /\
    MEM (Var ao) inst.inst_operands /\
    m2v_promote_inst pvar ao sz inst <> [inst] ==>
    sz <= 32 /\ ?sz_op.
      inst.inst_operands = [Var ao; sz_op] /\
      m2v_promote_inst pvar ao sz inst =
        [<|inst_id := inst.inst_id; inst_opcode := MSTORE;
           inst_operands := [Var ao; Var pvar]; inst_outputs := []|>;
         inst]
Proof
  rpt strip_tac >>
  gvs[m2v_promote_inst_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

(* ================================================================
   POINTER CONFINEMENT HELPERS
   ao from promo_list is in alloca_roots, hence in pointer_derived_vars.
   pointer_confined then forces ao into offset position for MSTORE.
   ================================================================ *)

(* Variables in the initial list remain in pointer_use_vars output *)
Theorem mem_pointer_use_vars:
  !fn vars v. MEM v vars ==> MEM v (pointer_use_vars fn vars)
Proof
  rpt strip_tac >> simp[pointer_use_vars_def] >>
  qabbrev_tac `g = \w:string list + string list.
    case pointer_use_step_step fn (OUTL w) of
      NONE => INR (OUTL w) | SOME vs => INL vs` >>
  qspecl_then [`ISL`, `g`, `INL vars`]
    mp_tac (DB.fetch "While" "OWHILE_INV_IND"
      |> INST_TYPE [alpha |-> ``:string list + string list``]
      |> Q.INST [`P` |->
           `\s. case s of INL l => MEM v l | INR l => MEM v l`]
      |> SIMP_RULE (srw_ss()) []) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      rename [`ISL xx`] >> Cases_on `xx` >> gvs[Abbr`g`] >>
      Cases_on `pointer_use_step_step fn x` >> simp[] >>
      gvs[pointer_use_step_step_def, LET_DEF] >> rw[] >> simp[MEM_APPEND]) >>
  disch_tac >>
  Cases_on `OWHILE ISL g (INL vars)` >> simp[] >>
  Cases_on `x` >> simp[] >> res_tac >> gvs[]
QED

(* Roots are always in pointer_derived_vars *)
Theorem roots_in_pointer_derived_vars:
  !fn roots v. FINITE roots /\ v IN roots ==>
    v IN pointer_derived_vars fn roots
Proof
  rw[pointer_derived_vars_def] >>
  irule mem_pointer_use_vars >>
  metis_tac[MEM_SET_TO_LIST]
QED

(* alloca_roots is always finite (defined via fn_insts, a finite list) *)
Theorem FINITE_alloca_roots:
  !fn. FINITE (alloca_roots fn)
Proof
  rw[alloca_roots_def] >>
  irule SUBSET_FINITE >>
  qexists `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  simp[SUBSET_DEF, MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
  rename1 `MEM ainst (fn_insts fn)` >>
  qexists `ainst.inst_outputs` >> simp[] >>
  (conj_tac >- (qexists `ainst` >> simp[])) >>
  gvs[inst_output_def] >>
  Cases_on `ainst.inst_outputs` >> gvs[inst_output_def] >>
  Cases_on `t` >> gvs[]
QED

(* ao from promo_list is in alloca_roots *)
Theorem m2v_promo_ao_in_alloca_roots:
  !fn ao pvar sz.
    MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    ao IN alloca_roots fn
Proof
  rpt strip_tac >>
  drule m2v_promo_list_is_alloca >> strip_tac >>
  simp[alloca_roots_def] >> qexists `inst` >>
  simp[inst_output_def]
QED

(* ao from promo_list is in pointer_derived_vars fn (alloca_roots fn) *)
Theorem m2v_promo_ao_in_pointer_derived:
  !fn ao pvar sz.
    MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    ao IN pointer_derived_vars fn (alloca_roots fn)
Proof
  rpt strip_tac >>
  irule roots_in_pointer_derived_vars >>
  simp[FINITE_alloca_roots] >>
  irule m2v_promo_ao_in_alloca_roots >>
  metis_tac[]
QED

(* Key enabler: promoted alloca outputs have no pointer descendants.
   All uses of ao are MSTORE/MLOAD/RETURN (from promotability), none of which
   are pointer-preserving, so the transitive pointer-use closure is trivial. *)
Theorem pointer_use_step_promo_nil:
  !fn ao pvar sz.
    MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    pointer_use_step fn [ao] = []
Proof
  rpt strip_tac >>
  drule m2v_promo_list_can_promote >> strip_tac >>
  simp[pointer_use_step_def, FLAT_EQ_NIL', MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> rename1 `MEM bb fn.fn_blocks` >>
  simp[FLAT_EQ_NIL', MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> rename1 `MEM inst bb.bb_instructions` >>
  rw[] >>
  (* inst uses Var ao AND is_pointer_preserving_op → contradiction *)
  CCONTR_TAC >> gvs[] >>
  `MEM ao (operand_vars inst.inst_operands)` by
    (irule MEM_Var_operand_vars >>
     gvs[EXISTS_MEM] >> rename1 `MEM op inst.inst_operands` >>
     Cases_on `op` >> gvs[]) >>
  `MEM inst (fn_insts fn)` by metis_tac[MEM_fn_insts] >>
  `MEM inst (dfg_get_uses (dfg_build_function fn) ao)` by
    (irule dfgCorrectnessProofTheory.dfg_build_function_uses_complete_proof >>
     simp[]) >>
  gvs[m2v_can_promote_alloca_def, EVERY_MEM] >>
  res_tac >> gvs[is_pointer_preserving_op_def]
QED

Theorem pointer_use_vars_promo_id:
  !fn ao pvar sz.
    MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    pointer_use_vars fn [ao] = [ao]
Proof
  rpt strip_tac >>
  drule pointer_use_step_promo_nil >> strip_tac >>
  simp[pointer_use_vars_def] >>
  `pointer_use_step_step fn [ao] = NONE` by
    simp[pointer_use_step_step_def, LET_DEF] >>
  SUBGOAL_THEN ``OWHILE ISL
    (\v. case pointer_use_step_step fn (OUTL v) of
           NONE => INR (OUTL v)
         | SOME vs => INL vs) (INL [ao]) = SOME (INR [ao])``
    (fn th => simp[th])
  >- (ONCE_REWRITE_TAC [DB.fetch "While" "OWHILE_THM"] >> simp[] >>
      ONCE_REWRITE_TAC [DB.fetch "While" "OWHILE_THM"] >> simp[])
QED

Theorem m2v_promoted_no_pointer_descendants:
  !fn ao pvar sz.
    MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    pointer_derived_vars fn {ao} = {ao}
Proof
  rpt strip_tac >>
  simp[pointer_derived_vars_def, SET_TO_LIST_SING] >>
  drule pointer_use_vars_promo_id >> simp[]
QED

(* For MSTORE with alloca_pointer_confined: if ao is a promo alloca output
   and MEM (Var ao) inst.inst_operands, then Var ao is the offset (first operand) *)
Theorem m2v_pointer_confined_mstore_ao_is_offset:
  !fn bb inst ao pvar sz.
    alloca_pointer_confined fn /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst.inst_opcode = MSTORE /\
    MEM (ao,pvar,sz) (m2v_promo_list fn) /\
    MEM (Var ao) inst.inst_operands ==>
    ?val_op. inst.inst_operands = [Var ao; val_op]
Proof
  rpt strip_tac >>
  `ao IN pointer_derived_vars fn (alloca_roots fn)` by
    metis_tac[m2v_promo_ao_in_pointer_derived] >>
  gvs[alloca_pointer_confined_def, pointer_confined_def, LET_DEF] >>
  first_x_assum (qspecl_then [`bb`,`inst`,`ao`] mp_tac) >> simp[] >>
  strip_tac >> gvs[]
  >- ((* mem_write_ops case: Var ao = iao_ofst = HD inst.inst_operands *)
      gvs[mem_write_ops_def] >>
      every_case_tac >> gvs[] >>
      Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      Cases_on `t'` >> gvs[])
  >- ((* mem_read_ops case: impossible for MSTORE *)
      gvs[mem_read_ops_def] >> every_case_tac >> gvs[])
  >> (* pointer_preserving: impossible for MSTORE *)
  gvs[is_pointer_preserving_op_def]
QED

(* Unchanged MSTORE with confined pointer → sz ≠ 32 *)
Theorem m2v_promote_mstore_unchanged_neq32:
  !fn bb inst ao pvar sz.
    alloca_pointer_confined fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = MSTORE /\
    MEM (ao,pvar,sz) (m2v_promo_list fn) /\
    MEM (Var ao) inst.inst_operands /\
    m2v_promote_inst pvar ao sz inst = [inst] ==>
    sz <> 32
Proof
  rpt strip_tac >>
  drule_all m2v_pointer_confined_mstore_ao_is_offset >> strip_tac >>
  qpat_x_assum `_ = [inst]` mp_tac >>
  simp[m2v_promote_inst_def, instruction_component_equality]
QED

(* For RETURN with alloca_pointer_confined: ao is in offset position *)
Theorem m2v_pointer_confined_return_ao_is_offset:
  !fn bb inst ao pvar sz.
    alloca_pointer_confined fn /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst.inst_opcode = RETURN /\
    MEM (ao,pvar,sz) (m2v_promo_list fn) /\
    MEM (Var ao) inst.inst_operands ==>
    ?sz_op. inst.inst_operands = [Var ao; sz_op]
Proof
  rpt strip_tac >>
  `ao IN pointer_derived_vars fn (alloca_roots fn)` by
    metis_tac[m2v_promo_ao_in_pointer_derived] >>
  gvs[alloca_pointer_confined_def, pointer_confined_def, LET_DEF] >>
  first_x_assum (qspecl_then [`bb`,`inst`,`ao`] mp_tac) >> simp[] >>
  strip_tac >> gvs[]
  >- ((* mem_write_ops: impossible for RETURN *)
      gvs[mem_write_ops_def] >> every_case_tac >> gvs[])
  >- ((* mem_read_ops: Var ao = offset, first operand *)
      gvs[mem_read_ops_def] >>
      every_case_tac >> gvs[] >>
      Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[] >>
      Cases_on `t'` >> gvs[])
  >> gvs[is_pointer_preserving_op_def]
QED

(* Non-promoted alloca access: bytes within a non-promoted alloca's region
   are not in any promoted region, given allocas don't overlap. *)
Theorem nonpromoted_alloca_not_in_promoted_region:
  !fn s aid b1 sz1 base n.
    allocas_non_overlapping s /\
    FLOOKUP s.vs_allocas aid = SOME (b1, sz1) /\
    aid NOTIN m2v_promoted_ids fn /\
    b1 <= base /\ base + n <= b1 + sz1 ==>
    !addr. base <= addr /\ addr < base + n ==>
      ~in_promoted_region fn s addr
Proof
  rpt strip_tac >> gvs[in_promoted_region_def] >>
  rename1 `aid2 IN m2v_promoted_ids fn` >>
  rename1 `FLOOKUP s.vs_allocas aid2 = SOME (b2, 32)` >>
  Cases_on `aid = aid2` >- gvs[] >>
  qpat_x_assum `allocas_non_overlapping _`
    (strip_assume_tac o REWRITE_RULE [allocas_non_overlapping_def]) >>
  first_x_assum (qspecl_then [`aid`, `aid2`, `b1`, `sz1`, `b2`, `32`]
    mp_tac) >>
  simp[]
QED

(* Property: FIND=NONE memory accesses avoid promoted regions.
   Depends on pointer analysis soundness + alloca bounds.
   Used by RETURN/REVERT FIND=NONE and nonpromoted memory ops. *)
Definition m2v_nonpromoted_access_safe_def:
  m2v_nonpromoted_access_safe fn s <=>
    (!bb inst ops off_val sz_val sz_op.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
      FIND (\(ao,_,_). MEM (Var ao) inst.inst_operands)
           (m2v_promo_list fn) = NONE /\
      eval_operand ops.iao_ofst s = SOME off_val /\
      ops.iao_max_size = SOME sz_op /\
      eval_operand sz_op s = SOME sz_val ==>
      !addr. w2n off_val <= addr /\ addr < w2n off_val + w2n sz_val ==>
        ~in_promoted_region fn s addr) /\
    (!bb inst vals q r pairs src sz.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = DRET /\
      parse_dret_shape inst = SOME (q,r) /\
      eval_operands inst.inst_operands s = SOME vals /\
      pair_dret_words (TAKE (2 * r) (DROP (q + 1) vals)) = SOME pairs /\
      MEM (src,sz) pairs ==>
      !addr. w2n src <= addr /\ addr < w2n src + w2n sz ==>
        ~in_promoted_region fn s addr)
End

Triviality eval_operand_idx[simp]:
  eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof simp[instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem m2v_nonpromoted_access_safe_idx[simp]:
  m2v_nonpromoted_access_safe fn (s with vs_inst_idx := n) =
  m2v_nonpromoted_access_safe fn s
Proof
  simp[m2v_nonpromoted_access_safe_def, in_promoted_region_def,
       instIdxIndepTheory.eval_ops_inst_idx]
QED

(* Element of TAKE sz (DROP off mem ++ REPLICATE sz 0w) = mem_byte *)
Triviality el_take_drop_replicate:
  !x off sz (mem : word8 list).
    x < sz ==>
    EL x (TAKE sz (DROP off mem ++ REPLICATE sz 0w)) =
    if off + x < LENGTH mem then EL (off + x) mem else 0w
Proof
  rpt strip_tac >> simp[EL_TAKE] >>
  Cases_on `off + x < LENGTH mem`
  >- (simp[EL_APPEND1, LENGTH_DROP] >> simp[EL_DROP])
  >> simp[EL_APPEND2, LENGTH_DROP, EL_REPLICATE]
QED

(* mem_byte agreement implies bulk memory read agreement *)
Theorem mem_byte_agrees_take_drop:
  !off sz (s1:venom_state) (s2:venom_state).
    (!i. off <= i /\ i < off + sz ==>
         mem_byte i s1 = mem_byte i s2) ==>
    TAKE sz (DROP off s1.vs_memory ++ REPLICATE sz 0w) =
    TAKE sz (DROP off s2.vs_memory ++ REPLICATE sz 0w)
Proof
  rpt strip_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ] >>
  rpt strip_tac >>
  simp[el_take_drop_replicate] >>
  first_x_assum (qspec_then `off + x` mp_tac) >>
  simp[mem_byte_def]
QED

(* ===== ext_call helpers ===== *)

(* venom_to_tx_params agrees under m2v_inv_noix *)
Triviality venom_to_tx_params_m2v_inv:
  m2v_inv_noix fn s1 s2 ==>
  venom_to_tx_params s1 = venom_to_tx_params s2
Proof
  simp[m2v_inv_noix_def, venom_to_tx_params_def]
QED

(* make_venom_call_state agrees under m2v_inv_noix *)
Triviality make_venom_call_state_m2v_inv:
  m2v_inv_noix fn s1 s2 ==>
  make_venom_call_state s1 tgt gas val cd code st =
  make_venom_call_state s2 tgt gas val cd code st
Proof
  strip_tac >>
  simp[make_venom_call_state_def] >>
  `venom_to_tx_params s1 = venom_to_tx_params s2`
    by metis_tac[venom_to_tx_params_m2v_inv] >>
  gvs[m2v_inv_noix_def]
QED

(* make_venom_delegatecall_state agrees under m2v_inv_noix *)
Triviality make_venom_delegatecall_state_m2v_inv:
  m2v_inv_noix fn s1 s2 ==>
  make_venom_delegatecall_state s1 tgt gas cd code st =
  make_venom_delegatecall_state s2 tgt gas cd code st
Proof
  strip_tac >>
  simp[make_venom_delegatecall_state_def] >>
  `venom_to_tx_params s1 = venom_to_tx_params s2`
    by metis_tac[venom_to_tx_params_m2v_inv] >>
  gvs[m2v_inv_noix_def]
QED

(* make_venom_create_state agrees under m2v_inv_noix *)
Triviality make_venom_create_state_m2v_inv:
  m2v_inv_noix fn s1 s2 ==>
  make_venom_create_state s1 addr gas val ic =
  make_venom_create_state s2 addr gas val ic
Proof
  strip_tac >>
  simp[make_venom_create_state_def] >>
  `venom_to_tx_params s1 = venom_to_tx_params s2`
    by metis_tac[venom_to_tx_params_m2v_inv] >>
  gvs[m2v_inv_noix_def]
QED

(* read_memory agrees under m2v_inv_noix when range is nonpromoted *)
Triviality read_memory_m2v_inv:
  m2v_inv_noix fn s1 s2 /\
  (!addr. off <= addr /\ addr < off + sz ==>
          ~in_promoted_region fn s1 addr) ==>
  read_memory off sz s1 = read_memory off sz s2
Proof
  rpt strip_tac >> simp[read_memory_def] >>
  irule mem_byte_agrees_take_drop >>
  rpt strip_tac >> gvs[m2v_inv_noix_def]
QED

(* extract_venom_result: same run_result on both sides gives
   same output, and result states preserve m2v_inv_noix
   when the write range is nonpromoted *)
(* Setting non-semantic fields (transient, returndata, accounts, logs)
   to equal values preserves m2v_inv_noix. All semantic functions
   (lookup_var, mem_byte, mload, in_promoted_region, allocas_non_overlapping)
   are transparent to these fields. *)
Triviality m2v_inv_noix_set_fields:
  m2v_inv_noix fn s1 s2 ==>
  m2v_inv_noix fn
    (s1 with <| vs_transient := ts; vs_returndata := rd;
                vs_accounts := accts; vs_logs := lgs |>)
    (s2 with <| vs_transient := ts; vs_returndata := rd;
                vs_accounts := accts; vs_logs := lgs |>)
Proof
  simp[m2v_inv_noix_def, lookup_var_def, mem_byte_def, mload_def,
       in_promoted_region_def, allocas_non_overlapping_def] >>
  metis_tac[]
QED

(* m2v_inv_noix is preserved by wmwe at a nonpromoted range combined
   with setting non-semantic fields to equal values on both sides. *)
Triviality m2v_inv_noix_ext_update:
  m2v_inv_noix fn s1 s2 /\
  m2v_non32_ok fn s1 s2 /\
  (!addr. off <= addr /\ addr < off + LENGTH bytes ==>
          ~in_promoted_region fn s1 addr) ==>
  m2v_inv_noix fn
    (s1 with <| vs_memory :=
       (write_memory_with_expansion off bytes s1).vs_memory;
       vs_transient := ts; vs_returndata := rd;
       vs_accounts := accts; vs_logs := lgs |>)
    (s2 with <| vs_memory :=
       (write_memory_with_expansion off bytes s2).vs_memory;
       vs_transient := ts; vs_returndata := rd;
       vs_accounts := accts; vs_logs := lgs |>)
Proof
  strip_tac >>
  `m2v_inv_noix fn
     (write_memory_with_expansion off bytes s1)
     (write_memory_with_expansion off bytes s2)`
    by (irule m2v_inv_noix_both_sides_wmwe >> simp[]) >>
  `m2v_inv_noix fn
     ((write_memory_with_expansion off bytes s1) with
        <| vs_transient := ts; vs_returndata := rd;
           vs_accounts := accts; vs_logs := lgs |>)
     ((write_memory_with_expansion off bytes s2) with
        <| vs_transient := ts; vs_returndata := rd;
           vs_accounts := accts; vs_logs := lgs |>)`
    by (irule m2v_inv_noix_set_fields >> simp[]) >>
  gvs[wmwe_preserves, write_memory_with_expansion_def, LET_THM]
QED

(* Strengthened: only requires s1 extraction succeeds.
   Since extract_venom_result's SOME/NONE depends only on rr
   (not s), s2 extraction must also succeed. *)
Triviality extract_venom_result_m2v_inv:
  !fn s1 s2 ov retOff retSz rr out1 s1'.
  m2v_inv_noix fn s1 s2 /\
  m2v_non32_ok fn s1 s2 /\
  extract_venom_result s1 ov retOff retSz rr = SOME (out1, s1') /\
  (!addr. retOff <= addr /\ addr < retOff + retSz ==>
          ~in_promoted_region fn s1 addr) ==>
  ?s2'. extract_venom_result s2 ov retOff retSz rr = SOME (out1, s2') /\
        m2v_inv_noix fn s1' s2'
Proof
  rpt strip_tac >>
  `s1.vs_transient = s2.vs_transient /\
   s1.vs_accounts = s2.vs_accounts /\
   s1.vs_logs = s2.vs_logs /\
   s1.vs_returndata = s2.vs_returndata`
    by gvs[m2v_inv_noix_def] >>
  gvs[extract_venom_result_def, CaseEq "option", CaseEq "prod",
      CaseEq "list"] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[CaseEq "sum", CaseEq "option"] >>
  simp[m2v_inv_noix_ext_update, LENGTH_TAKE_EQ]
QED

(* ================================================================
   EXT_CALL PRESERVATION: each exec function preserves m2v_inv_noix
   when called with identical arguments on s1/s2.
   ================================================================ *)

(* Shared proof pattern for ext_call exec functions:
   1. Show read_memory agrees (metis_tac[read_memory_m2v_inv])
   2. Show field equalities (gvs[m2v_inv_noix_def])
   3. Unfold exec, show make_venom_*_state agrees
   4. Decompose s1 case, drule extract_venom_result_m2v_inv
   5. Show update_var preserves invariant *)

(* exec_ext_call (CALL/STATICCALL) preserves m2v_inv_noix *)
Triviality exec_ext_call_m2v_inv:
  m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
  exec_ext_call inst s1 (gas:bytes32) (addr:bytes32) (val:bytes32)
    (ao:bytes32) (as_:bytes32) (ro:bytes32) (rs:bytes32) st = OK v1 /\
  (!i. w2n ao <= i /\ i < w2n ao + w2n as_ ==>
          ~in_promoted_region fn s1 i) /\
  (!i. w2n ro <= i /\ i < w2n ro + w2n rs ==>
          ~in_promoted_region fn s1 i) /\
  (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
  (!ao' pvar sz. MEM (ao',pvar,sz) (m2v_promo_list fn) ==>
     ~MEM ao' inst.inst_outputs) ==>
  ?v2. exec_ext_call inst s2 gas addr val ao as_ ro rs st = OK v2 /\
       m2v_inv_noix fn v1 v2
Proof
  strip_tac >>
  `read_memory (w2n ao) (w2n as_) s1 =
   read_memory (w2n ao) (w2n as_) s2` by
    metis_tac[read_memory_m2v_inv] >>
  `s1.vs_accounts = s2.vs_accounts` by gvs[m2v_inv_noix_def] >>
  gvs[exec_ext_call_def, LET_THM] >>
  `make_venom_call_state s1 = make_venom_call_state s2` by
    metis_tac[make_venom_call_state_m2v_inv] >>
  gvs[] >>
  qpat_x_assum `_ = OK v1` mp_tac >> simp[AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule_all extract_venom_result_m2v_inv >> strip_tac >> gvs[] >>
  simp[AllCaseEqs()] >>
  irule m2v_inv_noix_update_var >> simp[]
QED

(* exec_delegatecall preserves m2v_inv_noix *)
Triviality exec_delegatecall_m2v_inv:
  m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
  exec_delegatecall inst s1 (gas:bytes32) (addr:bytes32)
    (ao:bytes32) (as_:bytes32) (ro:bytes32) (rs:bytes32) = OK v1 /\
  (!i. w2n ao <= i /\ i < w2n ao + w2n as_ ==>
          ~in_promoted_region fn s1 i) /\
  (!i. w2n ro <= i /\ i < w2n ro + w2n rs ==>
          ~in_promoted_region fn s1 i) /\
  (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
  (!ao' pvar sz. MEM (ao',pvar,sz) (m2v_promo_list fn) ==>
     ~MEM ao' inst.inst_outputs) ==>
  ?v2. exec_delegatecall inst s2 gas addr ao as_ ro rs = OK v2 /\
       m2v_inv_noix fn v1 v2
Proof
  strip_tac >>
  `read_memory (w2n ao) (w2n as_) s1 =
   read_memory (w2n ao) (w2n as_) s2` by
    metis_tac[read_memory_m2v_inv] >>
  `s1.vs_accounts = s2.vs_accounts /\ s1.vs_call_ctx = s2.vs_call_ctx`
    by gvs[m2v_inv_noix_def] >>
  gvs[exec_delegatecall_def, LET_THM] >>
  `make_venom_delegatecall_state s1 = make_venom_delegatecall_state s2` by
    metis_tac[make_venom_delegatecall_state_m2v_inv] >>
  gvs[] >>
  qpat_x_assum `_ = OK v1` mp_tac >> simp[AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule_all extract_venom_result_m2v_inv >> strip_tac >> gvs[] >>
  simp[AllCaseEqs()] >>
  irule m2v_inv_noix_update_var >> simp[]
QED

(* exec_create (CREATE/CREATE2) preserves m2v_inv_noix.
   retOff=0, retSize=0, so wmwe write range condition is vacuous. *)
Triviality exec_create_m2v_inv:
  m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
  exec_create inst s1 (value:bytes32) (offset:bytes32)
    (sz:bytes32) salt_opt = OK v1 /\
  (!i. w2n offset <= i /\ i < w2n offset + w2n sz ==>
          ~in_promoted_region fn s1 i) /\
  (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
  (!ao' pvar sz'. MEM (ao',pvar,sz') (m2v_promo_list fn) ==>
     ~MEM ao' inst.inst_outputs) ==>
  ?v2. exec_create inst s2 value offset sz salt_opt = OK v2 /\
       m2v_inv_noix fn v1 v2
Proof
  strip_tac >>
  `s1.vs_call_ctx = s2.vs_call_ctx /\ s1.vs_accounts = s2.vs_accounts`
    by gvs[m2v_inv_noix_def] >>
  `read_memory (w2n offset) (w2n sz) s1 =
   read_memory (w2n offset) (w2n sz) s2` by
    metis_tac[read_memory_m2v_inv] >>
  gvs[exec_create_def, LET_THM] >>
  `make_venom_create_state s1 = make_venom_create_state s2` by
    metis_tac[make_venom_create_state_m2v_inv] >>
  gvs[] >>
  qpat_x_assum `_ = OK v1` mp_tac >> simp[AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  (* retOff=0, retSz=0 so range condition is vacuous *)
  `!addr. 0 <= addr /\ addr < 0 + 0 ==> ~in_promoted_region fn s1 addr`
    by simp[] >>
  drule_all extract_venom_result_m2v_inv >> strip_tac >> gvs[] >>
  simp[AllCaseEqs()] >>
  irule m2v_inv_noix_update_var >> simp[]
QED

(* NAS extraction: write range disjointness from promoted regions *)
Theorem nas_write_range_disjoint:
  !fn s bb inst ops off_val sz_val sz_op.
    m2v_nonpromoted_access_safe fn s /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    mem_write_ops inst = SOME ops /\
    FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
         (m2v_promo_list fn) = NONE /\
    eval_operand ops.iao_ofst s = SOME off_val /\
    ops.iao_max_size = SOME sz_op /\
    eval_operand sz_op s = SOME sz_val ==>
    !addr. w2n off_val <= addr /\ addr < w2n off_val + w2n sz_val ==>
           ~in_promoted_region fn s addr
Proof
  simp[m2v_nonpromoted_access_safe_def] >> metis_tac[]
QED

(* NAS extraction: read range disjointness from promoted regions *)
Theorem nas_read_range_disjoint:
  !fn s bb inst ops off_val sz_val sz_op.
    m2v_nonpromoted_access_safe fn s /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    mem_read_ops inst = SOME ops /\
    FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
         (m2v_promo_list fn) = NONE /\
    eval_operand ops.iao_ofst s = SOME off_val /\
    ops.iao_max_size = SOME sz_op /\
    eval_operand sz_op s = SOME sz_val ==>
    !addr. w2n off_val <= addr /\ addr < w2n off_val + w2n sz_val ==>
           ~in_promoted_region fn s addr
Proof
  simp[m2v_nonpromoted_access_safe_def] >> metis_tac[]
QED

(* NAS extraction: each successfully parsed DRET dynamic source range is
   disjoint from promoted regions. *)
Theorem nas_dret_source_range_disjoint:
  !fn s bb inst vals q r pairs src sz.
    m2v_nonpromoted_access_safe fn s /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = DRET /\
    parse_dret_shape inst = SOME (q,r) /\
    eval_operands inst.inst_operands s = SOME vals /\
    pair_dret_words (TAKE (2 * r) (DROP (q + 1) vals)) = SOME pairs /\
    MEM (src,sz) pairs ==>
    !addr. w2n src <= addr /\ addr < w2n src + w2n sz ==>
           ~in_promoted_region fn s addr
Proof
  simp[m2v_nonpromoted_access_safe_def] >> metis_tac[]
QED

(* Combined: read_memory agrees for nonpromoted mem_read_ops instructions.
   Chains read_memory_m2v_inv + nas_read_range_disjoint.
   Takes eval_operand on EITHER state (bridges via agreement). *)
Triviality read_memory_nas_agrees:
  !fn s1 s2 bb inst ops off_val sz_val sz_op.
    m2v_inv_noix fn s1 s2 /\
    m2v_nonpromoted_access_safe fn s1 /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    mem_read_ops inst = SOME ops /\
    FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
         (m2v_promo_list fn) = NONE /\
    eval_operand ops.iao_ofst s1 = SOME off_val /\
    ops.iao_max_size = SOME sz_op /\
    eval_operand sz_op s1 = SOME sz_val ==>
    read_memory (w2n off_val) (w2n sz_val) s1 =
    read_memory (w2n off_val) (w2n sz_val) s2
Proof
  rpt strip_tac >>
  irule read_memory_m2v_inv >> simp[] >>
  metis_tac[nas_read_range_disjoint]
QED

(* step_inst_base wrapper: dispatch all 5 ext_call opcodes *)
val ext_call_source_unfold_tac =
  qpat_x_assum `step_inst_base _ s1 = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def];

val ext_call_source_cases_tac = gvs[AllCaseEqs()];

val ext_call_target_tac =
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[AllCaseEqs()];

Triviality m2v_step_ext_call:
  m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
  is_ext_call_op inst.inst_opcode /\
  step_inst_base inst s1 = OK v1 /\
  (!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2) /\
  (!ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
     ~MEM ao inst.inst_outputs) /\
  (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
  m2v_nonpromoted_access_safe fn s1 /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
       (m2v_promo_list fn) = NONE /\
  ~is_immutable_op inst.inst_opcode ==>
  ?v2. step_inst_base inst s2 = OK v2 /\ m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >>
  (Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def])
  >- (ext_call_source_unfold_tac >> suspend "call_unfold")
  >- (ext_call_source_unfold_tac >> suspend "static_unfold")
  >- (ext_call_source_unfold_tac >> suspend "deleg_unfold")
  >- (ext_call_source_unfold_tac >> suspend "create_unfold") >>
  ext_call_source_unfold_tac >> suspend "create2_unfold"
QED

Resume m2v_step_ext_call[call_unfold]:
  ext_call_source_cases_tac >> suspend "call_source"
QED

Resume m2v_step_ext_call[static_unfold]:
  ext_call_source_cases_tac >> suspend "static_source"
QED

Resume m2v_step_ext_call[deleg_unfold]:
  ext_call_source_cases_tac >> suspend "deleg_source"
QED

Resume m2v_step_ext_call[create_unfold]:
  ext_call_source_cases_tac >> suspend "create_source"
QED

Resume m2v_step_ext_call[create2_unfold]:
  ext_call_source_cases_tac >> suspend "create2_source"
QED

Resume m2v_step_ext_call[call_source]:
  ext_call_target_tac >> suspend "call"
QED

Resume m2v_step_ext_call[static_source]:
  ext_call_target_tac >> suspend "static"
QED

Resume m2v_step_ext_call[deleg_source]:
  ext_call_target_tac >> suspend "deleg"
QED

Resume m2v_step_ext_call[create_source]:
  ext_call_target_tac >> suspend "create"
QED

Resume m2v_step_ext_call[create2_source]:
  ext_call_target_tac >> suspend "create2"
QED

(* Shared tactic for all 5 ext_call Resume blocks:
   TRY each exec helper, then discharge NAS range conditions *)
(* Extract call_ctx equality from m2v_inv_noix *)
fun m2v_inv_call_ctx th =
  List.nth (CONJUNCTS (REWRITE_RULE [m2v_inv_noix_def] th), 7);

val m2v_ext_call_tac =
  strip_tac >> gvs[] >>
  FIRST [match_mp_tac exec_ext_call_m2v_inv,
         match_mp_tac exec_delegatecall_m2v_inv,
         match_mp_tac exec_create_m2v_inv] >>
  (* match_mp_tac unifies st with s2 fields;
     rewrite exec asm using call_ctx equality from m2v_inv_noix *)
  qpat_assum `m2v_inv_noix _ _ _`
    (fn th => assume_tac th >>
              RULE_ASSUM_TAC (REWRITE_RULE [m2v_inv_call_ctx th])) >>
  simp[] >>
  rpt conj_tac >>
  TRY (CHANGED_TAC (simp[]) >> NO_TAC) >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (ho_match_mp_tac nas_read_range_disjoint >>
       qexistsl [`bb`, `inst`] >>
       simp[mem_read_ops_def, is_immutable_op_def] >> NO_TAC) >>
  TRY (ho_match_mp_tac nas_write_range_disjoint >>
       qexistsl [`bb`, `inst`] >>
       simp[mem_write_ops_def, is_immutable_op_def] >> NO_TAC);

Resume m2v_step_ext_call[call]:
  m2v_ext_call_tac
QED

Resume m2v_step_ext_call[static]:
  m2v_ext_call_tac
QED

Resume m2v_step_ext_call[deleg]:
  m2v_ext_call_tac
QED

Resume m2v_step_ext_call[create]:
  m2v_ext_call_tac
QED

Resume m2v_step_ext_call[create2]:
  m2v_ext_call_tac
QED
Finalise m2v_step_ext_call

Theorem m2v_promo_sizes_bounded_MEM:
  !fn ao pvar sz.
    m2v_promo_sizes_bounded fn /\
    MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    sz = 32
Proof
  rpt strip_tac >>
  fs[m2v_promo_sizes_bounded_def] >>
  first_x_assum drule >> simp[]
QED

Theorem m2v_nonterminal_step_dispatch:
  !fn bb i fuel ctx s1 s2 v1.
    wf_function fn /\
    fn_inst_wf fn /\
    ssa_form fn /\
    m2v_promotable_wf fn /\
    m2v_fresh_names_disjoint fn /\
    m2v_promo_sizes_bounded fn /\
    alloca_pointer_confined fn /\
    all_mem_via_pointer fn (alloca_roots fn) /\
    alloca_inv s1 /\
    alloca_bridge fn s1 /\
    m2v_nonpromoted_access_safe fn s1 /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
    MEM bb fn.fn_blocks /\
    bb_well_formed bb /\
    i < LENGTH bb.bb_instructions - 1 /\
    m2v_inv_noix fn s1 s2 /\
    m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\
    m2v_pvars_set fn bb i s2 /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1.vs_alloca_next < dimword (:256) /\
    step_inst fuel ctx (EL i bb.bb_instructions) s1 = OK v1 ==>
    ?v2. step_inst fuel ctx
           (HD (m2v_rewrite_inst fn (EL i bb.bb_instructions))) s2 = OK v2 /\
         m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >>
  `allocas_non_overlapping s1` by gvs[alloca_inv_def] >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  `i < LENGTH bb.bb_instructions` by
    (fs[bb_well_formed_def] >> Cases_on `bb.bb_instructions` >> fs[]) >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`, MEM_EL] >> qexists `i` >> simp[]) >>
  `MEM inst (fn_insts fn)` by metis_tac[MEM_fn_insts] >>
  `~is_terminator inst.inst_opcode` by
    (fs[bb_well_formed_def, Abbr `inst`] >>
     CCONTR_TAC >> fs[] >> res_tac >> fs[]) >>
  simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_,_). MEM (Var ao) inst.inst_operands)
                  (m2v_promo_list fn)`
  >- (simp[] >> suspend "nonpromoted")
  >> rename1 `SOME entry` >> PairCases_on `entry` >>
  rename1 `SOME (ao, pvar, sz)` >> simp[] >>
  `inst.inst_opcode = MSTORE \/ inst.inst_opcode = MLOAD \/
   inst.inst_opcode = RETURN` by metis_tac[promo_find_inst_opcode] >>
  `inst.inst_opcode <> RETURN` by fs[is_terminator_def] >>
  gvs[]
  >- suspend "mstore"
  >> suspend "mload"
QED

Resume m2v_nonterminal_step_dispatch[nonpromoted]:
  (* Nonpromoted: FIND NONE → same instruction on both sides.
     Need to show step succeeds on s2 and m2v_inv_noix preserved. *)
  (* Operand agreement from strengthened m2v_fresh_names_disjoint *)
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2` by (
    rpt strip_tac >>
    irule m2v_step_operand_agrees >>
    gvs[m2v_inv_noix_def] >> metis_tac[]) >>
  (* Output not fresh *)
  `!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn` by
    (rpt strip_tac >> CCONTR_TAC >> gvs[] >>
     gvs[m2v_fresh_names_disjoint_def] >> res_tac) >>
  (* INVOKE: contradicts precondition *)
  `inst.inst_opcode <> INVOKE` by (gvs[EVERY_MEM] >> res_tac) >>
  (* Case split: memory/alloca/ext_call effects? *)
  Cases_on `Eff_MEMORY IN write_effects inst.inst_opcode \/
            Eff_MEMORY IN read_effects inst.inst_opcode \/
            is_alloca_op inst.inst_opcode \/
            is_ext_call_op inst.inst_opcode`
  >- ((* Complex: mem/alloca/ext_call effects *)
      Cases_on `is_alloca_op inst.inst_opcode`
      >- (suspend "alloca")
      >> Cases_on `is_ext_call_op inst.inst_opcode`
      >- (suspend "ext_call")
      >> (* Memory effects on nonpromoted inst *)
      suspend "nonpromoted_mem")
  >> (* No mem/alloca/ext_call effects.
        Side-effectful ops (SSTORE etc.) have inst_outputs=[] from fn_inst_wf,
        so they satisfy m2v_step_nonpromoted's preconditions. *)
  gvs[] >>
  `!ao pvar sz. MEM (ao,pvar,sz) (m2v_promo_list fn) ==>
    ~MEM ao inst.inst_outputs` by
    metis_tac[ssa_promo_ao_not_in_outputs] >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (mp_tac (Q.SPECL [`fn`, `inst`, `s1`, `s2`, `fuel`, `ctx`, `v1`]
        m2v_step_nonpromoted_dalloca) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  mp_tac (Q.SPECL [`fn`, `inst`, `s1`, `s2`, `fuel`, `ctx`, `v1`]
    m2v_step_nonpromoted) >>
  simp[] >>
  disch_then irule >>
  rpt conj_tac >> TRY (gvs[m2v_inv_noix_def] >> NO_TAC)
  >- metis_tac[no_log_write_without_memory_read]
  >- metis_tac[no_returndata_write_without_memory_or_extcall]
  (* Remaining: ~is_effect_free_op ==> inst.inst_outputs = [] *)
  >> (strip_tac >>
      `inst_wf inst` by (drule_all fn_inst_wf_MEM >> simp[]) >>
      (* Enumerate opcodes — only SSTORE/TSTORE/ASSERT/ASSERT_UNREACHABLE remain *)
      Cases_on `inst.inst_opcode` >>
      gvs[is_effect_free_op_def] >>
      gvs[inst_wf_def, write_effects_def, read_effects_def,
          is_alloca_op_def, is_ext_call_op_def, is_terminator_def])
QED

Resume m2v_nonterminal_step_dispatch[mstore]:
  drule venomExecProofsTheory.FIND_MEM >> strip_tac >>
  drule venomExecProofsTheory.FIND_P >> simp[] >> strip_tac >>
  Cases_on `m2v_promote_inst pvar ao sz inst = [inst]`
  >- ((* Unchanged (sz<>32): same inst both sides *)
      gvs[] >> suspend "mstore_unchanged")
  >> (* Actually promoted: derive sz=32, operands=[Var ao; val_op] *)
  drule_all m2v_promote_mstore_format >> strip_tac >>
  gvs[m2v_promote_inst_def] >>
  mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`,`fuel`,`ctx`,`ao`,`pvar`,`32`,
    `v1`,`val_op`] m2v_step_promoted_mstore) >>
  simp[] >> disch_then irule >> rpt conj_tac
  (* 1. addr-in-region *)
  >- (rpt strip_tac >> drule_all m2v_inv_noix_addr_in_region >> simp[])
  (* 2. regions-disjoint and distinct pvars *)
  >- (rpt gen_tac >> strip_tac >> suspend "disjoint")
  (* 3. val_op not fresh *)
  >- (rpt strip_tac >> CCONTR_TAC >> gvs[] >>
      drule_all m2v_fresh_not_in_operands >> simp[])
  (* 4. ao not fresh *)
  >> mp_tac (Q.SPECL [`fn`,`ao`,`pvar`,`32`]
       m2v_promo_list_ao_not_fresh) >> simp[]
QED

Resume m2v_nonterminal_step_dispatch[disjoint]:
  `ao <> ao2` by
    (CCONTR_TAC >> gvs[] >>
     mp_tac (Q.SPECL [`fn`,`ao`,`pvar`,`32`,`pvar2`,`sz2`]
       m2v_promo_list_ao_unique) >> simp[]) >>
  mp_tac (Q.SPECL [`fn`,`s1`,`s2`,`ao`,`pvar`,`32`,`ao2`,`pvar2`,`sz2`,
    `a1`,`a2`] m2v_inv_noix_regions_disjoint) >>
  (impl_tac >- simp[]) >>
  strip_tac >> simp[] >>
  (* IS_SOME ==> sz2 >= 32: fresh pvar2 only assigned by promoted MSTORE (sz=32) *)
  strip_tac >>
  `sz2 = 32` by
    (drule_all m2v_promo_sizes_bounded_MEM >> gvs[]) >>
  simp[]
QED

Resume m2v_nonterminal_step_dispatch[mload]:
  drule venomExecProofsTheory.FIND_MEM >> strip_tac >>
  drule venomExecProofsTheory.FIND_P >> simp[] >> strip_tac >>
  Cases_on `m2v_promote_inst pvar ao sz inst = [inst]`
  >- (gvs[] >> suspend "mload_unchanged") (* Unchanged (sz<>32) *)
  >> drule_all m2v_promote_mload_format >> strip_tac >>
  gvs[m2v_promote_inst_def] >>
  irule m2v_step_promoted_mload >> simp[] >>
  suspend "mload_promoted"
QED

Resume m2v_nonterminal_step_dispatch[mload_promoted]:
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      mp_tac (Q.SPECL [`fn`,`inst`,`out`] m2v_output_safe) >>
      simp[is_alloca_op_def])
  >- (mp_tac (Q.SPECL [`fn`,`bb`,`i`,`s2`,`ao`,`pvar`]
        m2v_pvars_set_mload_is_some) >>
      gvs[markerTheory.Abbrev_def])
  >> (qexists `s1` >> simp[])
QED

Theorem m2v_promote_mload_unchanged_neq32:
  !inst ao pvar sz.
    inst.inst_opcode = MLOAD /\
    inst.inst_operands = [Var ao] /\
    m2v_promote_inst pvar ao sz inst = [inst] ==>
    sz <> 32
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = [inst]` mp_tac >>
  simp[m2v_promote_inst_def, instruction_component_equality]
QED

Resume m2v_nonterminal_step_dispatch[mload_unchanged]:
  (* Unfold step_inst for MLOAD — derive operand structure *)
  gvs[step_inst_non_invoke, step_inst_base_def, exec_read1_def,
      AllCaseEqs()] >>
  rename1 `inst.inst_outputs = [out]` >>
  (* operands = [Var ao] from MEM + singleton *)
  `inst.inst_operands = [Var ao]` by (
    Cases_on `inst.inst_operands` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  gvs[eval_operand_def] >>
  rename1 `lookup_var ao s1 = SOME addr` >>
  (* Derive sz <> 32 *)
  drule_all m2v_promote_mload_unchanged_neq32 >> strip_tac >>
  (* Operand agreement: ao not fresh *)
  `ao NOTIN m2v_fresh_vars fn`
    by metis_tac[m2v_promo_list_ao_not_fresh] >>
  `lookup_var ao s2 = SOME addr` by (
    `lookup_var ao s1 = lookup_var ao s2` suffices_by gvs[] >>
    qpat_x_assum `m2v_inv_noix _ _ _`
      (strip_assume_tac o REWRITE_RULE [m2v_inv_noix_def]) >>
    first_x_assum irule >> simp[]) >>
  (* mload agreement *)
  `mload (w2n addr) s1 = mload (w2n addr) s2` by (
    mp_tac (Q.SPECL [`fn`,`s1`,`s2`,`ao`,`pvar`,`sz`,`addr`]
      m2v_inv_noix_mload_agrees_non32) >> simp[]) >>
  simp[] >>
  (* output safe: out not fresh and not a promo ao *)
  mp_tac (Q.SPECL [`fn`,`inst`,`out`] m2v_output_safe) >>
  simp[is_alloca_op_def] >> strip_tac >>
  irule m2v_inv_noix_update_var >> simp[]
QED

Resume m2v_nonterminal_step_dispatch[mstore_unchanged]:
  (* 1. Derive operand structure and sz <> 32 *)
  drule_all m2v_pointer_confined_mstore_ao_is_offset >> strip_tac >>
  drule_all m2v_promote_mstore_unchanged_neq32 >> strip_tac >>
  (* 2. Unfold step_inst for MSTORE *)
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
      AllCaseEqs(), eval_operand_def] >>
  rename1 `lookup_var ao s1 = SOME addr` >>
  rename1 `eval_operand val_op s1 = SOME val` >>
  (* 3. Operand agreement: ao not fresh *)
  `ao NOTIN m2v_fresh_vars fn`
    by metis_tac[m2v_promo_list_ao_not_fresh] >>
  `lookup_var ao s2 = SOME addr` by (
    `lookup_var ao s1 = lookup_var ao s2` suffices_by gvs[] >>
    qpat_x_assum `m2v_inv_noix _ _ _`
      (strip_assume_tac o REWRITE_RULE [m2v_inv_noix_def]) >>
    first_x_assum irule >> simp[]) >>
  (* 4. val_op agreement *)
  `eval_operand val_op s2 = SOME val` by (
    `eval_operand val_op s1 = eval_operand val_op s2` suffices_by gvs[] >>
    mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`,`val_op`]
      m2v_step_operand_agrees) >>
    simp[] >>
    qpat_x_assum `m2v_inv_noix _ _ _`
      (strip_assume_tac o REWRITE_RULE [m2v_inv_noix_def]) >>
    simp[]) >>
  simp[] >>
  (* 5. Apply m2v_inv_noix_both_sides_mstore *)
  irule m2v_inv_noix_both_sides_mstore >> simp[] >>
  rpt strip_tac >>
  (* 6. Disjointness: ao alloca (sz>=32, sz<>32) vs ao2 alloca (32) *)
  `ao <> ao'` by (
    CCONTR_TAC >> gvs[] >>
    mp_tac (Q.SPECL [`fn`,`ao`,`pvar`,`sz`,`pvar'`,`32`]
      m2v_promo_list_ao_unique) >> simp[]) >>
  mp_tac (Q.SPECL [`fn`,`s1`,`s2`,`ao`,`pvar`,`sz`,`ao'`,`pvar'`,`32`,
    `addr`,`addr'`] m2v_inv_noix_regions_disjoint) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* regions_disjoint (w2n addr, sz) (w2n addr', 32) with sz = 32 *)
  `sz = 32` by
    (mp_tac (Q.SPECL [`fn`,`ao`,`pvar`,`sz`]
       m2v_promo_sizes_bounded_MEM) >> simp[]) >>
  gvs[regions_disjoint_def]
QED

Resume m2v_nonterminal_step_dispatch[alloca]:
  (* ALLOCA: same instruction on both sides (not transformed).
     Both execute exec_alloca identically when vs_alloca_next agrees. *)
  `inst.inst_opcode = ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  gvs[step_inst_non_invoke] >>
  `inst_wf inst` by (drule_all fn_inst_wf_MEM >> simp[]) >>
  gvs[inst_wf_def] >> rename1 `inst.inst_operands = [Lit alloc_sz]` >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  rename1 `inst.inst_outputs = [out]` >>
  gvs[step_inst_base_def, exec_alloca_def] >>
  `s1.vs_allocas = s2.vs_allocas` by gvs[m2v_inv_noix_def] >>
  `s1.vs_alloca_next = s2.vs_alloca_next` by gvs[m2v_inv_noix_def] >>
  (* vs_alloca_next agreement from dispatch precondition *)
  Cases_on `FLOOKUP s1.vs_allocas inst.inst_id`
  >- ((* NONE: new allocation — both sides compute identical result.
        Both sides: allocas |+ (id, (nao, w2n alloc_sz)),
        alloca_next := nao + w2n alloc_sz, update_var out (n2w nao). *)
      gvs[AllCaseEqs()] >>
      qmatch_goalsub_abbrev_tac `m2v_inv_noix fn (update_var _ _ s1') _` >>
      qmatch_goalsub_abbrev_tac `m2v_inv_noix fn _ (update_var _ _ s2')` >>
      (* s1' and s2' differ from s1/s2 only in allocas + alloca_next *)
      irule m2v_inv_noix_update_var >>
      `s1'.vs_allocas = s2'.vs_allocas` by simp[Abbr `s1'`, Abbr `s2'`] >>
      `s1'.vs_alloca_next = s2'.vs_alloca_next`
        by simp[Abbr `s1'`, Abbr `s2'`] >>
      simp[] >> rpt conj_tac
      (* bridge: SSA uniqueness + new FLOOKUP *)
      >- suspend "alloca_none_bridge"
      (* sync: pvar not yet set — ao undefined implies pvar undefined *)
      >- suspend "alloca_none_sync"
      (* m2v_inv_noix fn s1' s2': identical alloca insert *)
      >> suspend "alloca_none_inv")
  >> ((* SOME: existing allocation — just returns existing offset *)
      PairCases_on `x` >> gvs[AllCaseEqs()] >>
      (* Both sides: update_var out (n2w x0) s, no allocas/memory changes *)
      Cases_on `?pvar sz. MEM (out,pvar,sz) (m2v_promo_list fn)`
      >- ((* Promoted: out = ao for some promo entry. Use helper. *)
          gvs[] >>
          (* Use alloca_bridge reverse direction *)
          `x1 = sz /\ ?addr. lookup_var out s1 = SOME addr /\
                              w2n addr = x0` by
            (mp_tac (Q.SPECL [`fn`,`inst`,`out`,`pvar`,`sz`,`s1`,`x0`,`x1`]
              alloca_bridge_entry_sz) >> simp[]) >>
          `x0 < dimword (:256)` by metis_tac[wordsTheory.w2n_lt] >>
          (* Derive FLOOKUP in bridge-compatible form *)
          `w2n (n2w x0 :256 word) = x0`
            by gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
          irule m2v_inv_noix_update_var >> simp[] >> rpt conj_tac
          (* bridge: uniqueness gives sz'=sz, inst'=inst *)
          >- (rpt strip_tac >>
              metis_tac[m2v_promo_list_ao_unique,
                        ssa_alloca_output_unique, MEM])
          (* sync: uniqueness + pre-state sync *)
          >> rpt strip_tac >>
          metis_tac[m2v_inv_noix_sync, m2v_promo_list_ao_unique])
      >> ((* Nonpromoted: update_var with vacuous bridge/sync *)
          irule m2v_inv_noix_update_var >> simp[] >>
          gvs[m2v_inv_noix_def]))
QED

Resume m2v_nonterminal_step_dispatch[alloca_none_bridge]:
  (* Bridge: inst' = inst by SSA uniqueness, then FLOOKUP new entry *)
  rpt strip_tac >>
  `inst' = inst` by metis_tac[ssa_alloca_output_unique, MEM] >>
  gvs[Abbr `s2'`, FLOOKUP_UPDATE] >>
  drule m2v_promo_list_is_alloca >> strip_tac >>
  `inst' = inst` by metis_tac[ssa_alloca_output_unique, MEM] >>
  gvs[AllCaseEqs()]
QED

Resume m2v_nonterminal_step_dispatch[alloca_none_inv]:
  (* m2v_inv_noix fn s1' s2': identical alloca insert preserves inv. *)
  qunabbrev_tac `s1'` >> qunabbrev_tac `s2'` >>
  MATCH_MP_TAC m2v_inv_noix_identical_alloca_update >>
  simp[] >> conj_tac
  >- suspend "alloca_none_inv_overlap"
  >> simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `k = inst.inst_id` >> gvs[]
QED

Resume m2v_nonterminal_step_dispatch[alloca_none_inv_overlap]:
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      FLOOKUP_UPDATE, AllCaseEqs()] >>
  rpt strip_tac >> res_tac >> simp[] >>
  gvs[arithmeticTheory.MAX_LE]
QED

Resume m2v_nonterminal_step_dispatch[alloca_none_sync]:
  (* Vacuously true: out not yet defined → ao_undef_sync → pvar NONE → ¬IS_SOME *)
  rpt strip_tac >>
  `lookup_var pvar s2' = lookup_var pvar s2`
    by simp[Abbr `s2'`, lookup_var_def] >>
  (* out undefined in s1: bridge + FLOOKUP=NONE *)
  `lookup_var out s1 = NONE` by
    (Cases_on `lookup_var out s1` >> simp[] >>
     drule_all m2v_inv_noix_bridge_inst >> gvs[]) >>
  (* ao_undef_sync: out NONE → pvar NONE *)
  `lookup_var pvar s2 = NONE` by
    (gvs[m2v_ao_undef_sync_def] >> res_tac) >>
  gvs[]
QED

(* mstore8 is equivalent to wmwe with a single byte *)
Triviality mstore8_eq_wmwe:
  !off (val_w:bytes32) s. mstore8 off val_w s =
    write_memory_with_expansion off [w2w val_w] s
Proof
  simp[mstore8_def, write_memory_with_expansion_def, LET_THM]
QED

(* Enumerate the ~14 opcodes with memory effects that are
   not alloca, not ext_call, not terminator, not INVOKE, not MEMTOP.
   Proved by Cases_on once; avoids repeating 70-way split inline. *)
Triviality mem_effect_opcodes:
  !op. ~is_alloca_op op /\ ~is_ext_call_op op /\ ~is_terminator op /\
       op <> INVOKE /\ op <> MEMTOP /\
       (Eff_MEMORY IN write_effects op \/
        Eff_MEMORY IN read_effects op) ==>
       op = MLOAD \/ op = MSTORE \/ op = MSTORE8 \/ op = MCOPY \/
       op = SHA3 \/ op = LOG \/ op = CALLDATACOPY \/ op = CODECOPY \/
       op = EXTCODECOPY \/ op = RETURNDATACOPY \/ op = DLOADBYTES \/
       op = DLOAD \/ op = ILOAD \/ op = ISTORE
Proof
  Cases >> simp[write_effects_def, read_effects_def, empty_effects_def,
    is_alloca_op_def, is_ext_call_op_def, is_terminator_def]
QED

(* Helper: for exec_read1-type nonpromoted ops, if the read function
   agrees between s1 and s2, then step succeeds on s2 and inv preserved.
   Works for MLOAD, ILOAD, DLOAD (after showing read agrees).
   Precondition: step_inst_base = exec_read1 f for this opcode on both sides.
   Key: the function `f` applied to the same operand value produces the same
   result on both states. *)
Theorem m2v_step_nonpromoted_read1:
  !fn inst f s1 s2 fuel ctx v1.
    m2v_inv_noix fn s1 s2 /\
    ssa_form fn /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\ ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
    step_inst_base inst s1 = exec_read1 f inst s1 /\
    step_inst_base inst s2 = exec_read1 f inst s2 /\
    step_inst fuel ctx inst s1 = OK v1 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!a. eval_operand (HD inst.inst_operands) s1 = SOME a ==>
         f a s1 = f a s2) ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\ m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  (* Unfold exec_read1 on s1 side (known OK) to extract operand/output *)
  qpat_x_assum `exec_read1 _ _ s1 = OK _` mp_tac >>
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `inst.inst_outputs = [out]` >>
  (* gvs unified s1/s2 operand values via agreement; v is the value *)
  (* Read function agrees *)
  `f v s1 = f v s2`
    by (first_x_assum irule >> gvs[]) >>
  (* s2 side succeeds: witness is update_var out (f v s2) s2 *)
  qexists `update_var out (f v s2) s2` >> conj_tac
  >- (qexists `v` >> gvs[]) >>
  irule m2v_inv_noix_update_var >> simp[] >>
  (* Bridge and sync: vacuous because out is not a promo ao *)
  mp_tac (Q.SPECL [`fn`,`inst`,`out`] m2v_output_safe) >> simp[]
QED

(* Helper: for wmwe-type nonpromoted ops, if both sides produce
   write_memory_with_expansion with the same offset and bytes,
   and the write range doesn't overlap promoted regions,
   then inv is preserved. *)
Theorem m2v_step_nonpromoted_wmwe:
  !fn inst s1 s2 fuel ctx v1 off bytes.
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s1 = OK v1 /\
    v1 = write_memory_with_expansion off bytes s1 /\
    step_inst_base inst s2 =
      OK (write_memory_with_expansion off bytes s2) /\
    (!addr. off <= addr /\ addr < off + LENGTH bytes ==>
            ~in_promoted_region fn s1 addr) ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\ m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  irule m2v_inv_noix_both_sides_wmwe >> simp[]
QED

(* Helper: for mstore-type nonpromoted ops (always 32 bytes),
   if both sides mstore same offset and value, and the write range
   doesn't overlap promoted allocas, then inv is preserved. *)
Theorem m2v_step_nonpromoted_mstore:
  !fn inst s1 s2 fuel ctx v1 off val_w.
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s1 = OK v1 /\
    v1 = mstore off val_w s1 /\
    step_inst_base inst s2 = OK (mstore off val_w s2) /\
    (!ao pvar addr. MEM (ao,pvar,32) (m2v_promo_list fn) /\
      lookup_var ao s1 = SOME addr ==>
      off + 32 <= w2n addr \/ w2n addr + 32 <= off) ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\ m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  irule m2v_inv_noix_both_sides_mstore >> metis_tac[]
QED

(* Helper: ISTORE performs the same 32-byte memory write and immutable-map
   update on both sides, away from promoted allocation regions. *)
Theorem m2v_step_nonpromoted_istore:
  !fn inst s1 s2 fuel ctx v1.
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    inst.inst_opcode = ISTORE /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s1 = OK v1 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!ao pvar off addr.
      MEM (ao,pvar,32) (m2v_promo_list fn) /\
      lookup_var ao s1 = SOME addr /\
      eval_operand (HD inst.inst_operands) s1 = SOME off ==>
      w2n off + 32 <= w2n addr \/ w2n addr + 32 <= w2n off) ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\ m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  gvs[step_inst_base_def, AllCaseEqs()] >>
  irule m2v_inv_noix_both_sides_istore >> simp[] >>
  metis_tac[]
QED

(* Helper: SHA3 — reads memory range, hashes, update_var.
   Memory data agrees via nonpromoted_access_safe. *)
Theorem m2v_step_nonpromoted_sha3:
  !fn inst s1 s2 fuel ctx v1 bb.
    m2v_inv_noix fn s1 s2 /\
    ssa_form fn /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\ ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode = SHA3 /\ inst.inst_opcode <> INVOKE /\
    (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
    step_inst fuel ctx inst s1 = OK v1 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!i. ~in_promoted_region fn s1 i ==>
         mem_byte i s1 = mem_byte i s2) /\
    m2v_nonpromoted_access_safe fn s1 /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
         (m2v_promo_list fn) = NONE ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\ m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  gvs[step_inst_base_def, AllCaseEqs()] >>
  rename1 `inst.inst_outputs = [out]` >>
  (* Memory data agrees: extract from nonpromoted_access_safe *)
  `!addr. w2n offset <= addr /\ addr < w2n offset + w2n size_val ==>
          ~in_promoted_region fn s1 addr`
    by (ho_match_mp_tac nas_read_range_disjoint >>
        qexistsl [`bb`, `inst`] >>
        simp[mem_read_ops_def, is_immutable_op_def]) >>
  `TAKE (w2n size_val) (DROP (w2n offset) s1.vs_memory ++
     REPLICATE (w2n size_val) 0w) =
   TAKE (w2n size_val) (DROP (w2n offset) s2.vs_memory ++
     REPLICATE (w2n size_val) 0w)`
    by (irule mem_byte_agrees_take_drop >> metis_tac[]) >>
  simp[] >>
  irule m2v_inv_noix_update_var >> simp[] >>
  mp_tac (Q.SPECL [`fn`,`inst`,`out`] m2v_output_safe) >> simp[]
QED

(* If each operand evaluates the same on s1 and s2, then eval_operands agrees. *)
Triviality eval_operands_agree:
  !ops s1 s2.
    (!op. MEM op ops ==> eval_operand op s1 = eval_operand op s2) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s1 = eval_operand h s2` by simp[] >>
  Cases_on `eval_operand h s1` >> simp[] >>
  `eval_operands ops s1 = eval_operands ops s2`
    by (first_x_assum irule >> simp[]) >>
  simp[]
QED

(* Helper: LOG — reads memory for event data, updates vs_logs.
   Event data and topics agree, so same event on both sides. *)
Theorem m2v_step_nonpromoted_log:
  !fn inst s1 s2 fuel ctx v1 bb.
    m2v_inv_noix fn s1 s2 /\
    inst.inst_opcode = LOG /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s1 = OK v1 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!i. ~in_promoted_region fn s1 i ==>
         mem_byte i s1 = mem_byte i s2) /\
    m2v_nonpromoted_access_safe fn s1 /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
         (m2v_promo_list fn) = NONE ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\ m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  gvs[step_inst_base_def, AllCaseEqs()] >>
  (* Operand agreement for rest elements *)
  `!op. MEM op rest ==> eval_operand op s1 = eval_operand op s2`
    by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  (* eval_operands for topics agrees *)
  `eval_operands (DROP 2 rest) s1 = eval_operands (DROP 2 rest) s2`
    by (irule eval_operands_agree >> rpt strip_tac >>
        first_x_assum irule >> metis_tac[MEM_DROP_IMP]) >>
  (* Memory read range is outside promoted regions *)
  `!addr. w2n off <= addr /\ addr < w2n off + w2n sz ==>
          ~in_promoted_region fn s1 addr`
    by (ho_match_mp_tac nas_read_range_disjoint >>
        qexistsl [`bb`, `inst`] >>
        `LENGTH rest >= 2` by simp[] >>
        simp[mem_read_ops_def, is_immutable_op_def] >>
        Cases_on `rest` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  (* Memory data for event agrees *)
  `TAKE (w2n sz) (DROP (w2n off) s1.vs_memory ++ REPLICATE (w2n sz) 0w) =
   TAKE (w2n sz) (DROP (w2n off) s2.vs_memory ++ REPLICATE (w2n sz) 0w)`
    by (irule mem_byte_agrees_take_drop >> rpt strip_tac >>
        qpat_x_assum `!i. ~in_promoted_region _ _ _ ==> _` irule >>
        first_x_assum irule >> simp[]) >>
  (* Operands agree on s2 side *)
  `eval_operand (HD rest) s2 = SOME off`
    by (first_x_assum (qspec_then `HD rest` mp_tac) >>
        impl_tac >- (Cases_on `rest` >> gvs[]) >> simp[]) >>
  `eval_operand (EL 1 rest) s2 = SOME sz`
    by (first_x_assum (qspec_then `EL 1 rest` mp_tac) >>
        impl_tac >- (Cases_on `rest` >> gvs[] >>
          Cases_on `t` >> gvs[]) >> simp[]) >>
  gvs[] >>
  simp[m2v_inv_noix_def] >>
  gvs[m2v_inv_noix_def, in_promoted_region_def, mem_byte_def,
      lookup_var_def, allocas_non_overlapping_def, mload_def] >>
  metis_tac[]
QED


(* Master dispatch for all 14 nonpromoted memory-effect opcodes.
   Takes the 14-way disjunction + standard preconditions, calls the
   appropriate per-group helper. *)
Theorem m2v_nonpromoted_mem_dispatch:
  !fn inst s1 s2 fuel ctx v1 bb.
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    ssa_form fn /\ m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\ ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!v. MEM v inst.inst_outputs ==> v NOTIN m2v_fresh_vars fn) /\
    step_inst fuel ctx inst s1 = OK v1 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    m2v_nonpromoted_access_safe fn s1 /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
         (m2v_promo_list fn) = NONE /\
    (inst.inst_opcode = MLOAD \/ inst.inst_opcode = MSTORE \/
     inst.inst_opcode = MSTORE8 \/ inst.inst_opcode = MCOPY \/
     inst.inst_opcode = SHA3 \/ inst.inst_opcode = LOG \/
     inst.inst_opcode = CALLDATACOPY \/ inst.inst_opcode = CODECOPY \/
     inst.inst_opcode = EXTCODECOPY \/ inst.inst_opcode = RETURNDATACOPY \/
     inst.inst_opcode = DLOADBYTES \/ inst.inst_opcode = DLOAD \/
     inst.inst_opcode = ILOAD \/ inst.inst_opcode = ISTORE) ==>
    ?v2. step_inst fuel ctx inst s2 = OK v2 /\ m2v_inv_noix fn v1 v2
Proof
  rpt strip_tac >> gvs[]
  >- suspend "mload"
  >- suspend "mstore"
  >- suspend "mstore8"
  >- suspend "mcopy"
  >- suspend "sha3"
  >- suspend "log"
  >- suspend "calldatacopy"
  >- suspend "codecopy"
  >- suspend "extcodecopy"
  >- suspend "returndatacopy"
  >- suspend "dloadbytes"
  >- suspend "dload"
  >- suspend "iload"
  >> suspend "istore"
QED

(* --- Resume blocks for m2v_nonpromoted_mem_dispatch --- *)

Triviality lt_32_dimword_256:
  32 < dimword (:256)
Proof
  simp[wordsTheory.dimword_def]
QED

(* Helper tactic: NAS write disjointness after step_inst_base unfold.
   After gvs[step_inst_base_def, AllCaseEqs()], auto-generated names for
   operand eval results. Extract NAS for write range disjointness. *)

Resume m2v_nonpromoted_mem_dispatch[istore]:
  ho_match_mp_tac m2v_step_nonpromoted_istore >>
  qexists `s1` >> simp[] >>
  rpt strip_tac >>
  `?offset_op value_op. inst.inst_operands = [offset_op; value_op]` by
    (qpat_x_assum `step_inst fuel ctx inst s1 = OK v1` mp_tac >>
     simp[step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[]) >>
  drule_all m2v_inv_noix_alloca_bridge >> strip_tac >>
  irule (iffRL DISJ_COMM) >>
  ho_match_mp_tac promoted_region_disjoint_from_nonpromoted >>
  qexistsl [`fn`, `s1`, `inst_id`] >> simp[] >>
  `eval_operand offset_op s1 = SOME off` by gvs[] >>
  `eval_operand offset_op s2 = SOME off` by
    (qpat_x_assum `!op. MEM op inst.inst_operands ==> _`
       (qspec_then `offset_op` mp_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`fn`, `s1`, `bb`, `inst`,
    `<| iao_ofst := HD inst.inst_operands;
        iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w) |>`,
    `off`, `32w`, `Lit 32w`] nas_write_range_disjoint) >>
  simp[mem_write_ops_def, eval_operand_def, lt_32_dimword_256,
       arithmeticTheory.LESS_MOD]
QED

Resume m2v_nonpromoted_mem_dispatch[iload]:
  ho_match_mp_tac m2v_step_nonpromoted_read1 >>
  qexistsl [`\addr s. mload (w2n addr) s`, `s1`] >>
  ASM_REWRITE_TAC[step_inst_non_invoke, step_inst_base_def,
                  is_alloca_op_def] >> gvs[] >>
  rpt strip_tac >>
  irule mload_mem_byte_eq >> rpt strip_tac >>
  qpat_x_assum `m2v_inv_noix _ _ _` mp_tac >>
  simp[m2v_inv_noix_def] >> strip_tac >>
  first_x_assum irule >>
  mp_tac (Q.SPECL [`fn`, `s1`, `bb`, `inst`] nas_read_range_disjoint) >>
  simp[mem_read_ops_def, is_immutable_op_def, eval_operand_def] >>
  disch_then irule >>
  `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
    (irule step_inst_non_invoke >> simp[]) >>
  qpat_x_assum `step_inst fuel ctx inst s1 = OK v1` mp_tac >>
  ASM_REWRITE_TAC[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >>
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[eval_operand_def, lt_32_dimword_256, arithmeticTheory.LESS_MOD]
QED

Resume m2v_nonpromoted_mem_dispatch[dload]:
  ho_match_mp_tac m2v_step_nonpromoted_read1 >>
  qexistsl [`\off s. word_of_bytes T 0w
    (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))`, `s1`] >>
  gvs[step_inst_non_invoke, step_inst_base_def] >>
  gvs[m2v_inv_noix_def]
QED

Resume m2v_nonpromoted_mem_dispatch[sha3]:
  ho_match_mp_tac m2v_step_nonpromoted_sha3 >>
  qexists `s1` >> qexists `bb` >> simp[] >> gvs[m2v_inv_noix_def]
QED

Resume m2v_nonpromoted_mem_dispatch[log]:
  ho_match_mp_tac m2v_step_nonpromoted_log >>
  qexists `s1` >> qexists `bb` >> simp[] >> gvs[m2v_inv_noix_def]
QED

(* wmwe ops: unfold step_inst_base → wmwe form, show bytes agree from
   inv field equality, use both_sides_wmwe, discharge NAS disjointness *)

(* Shared wmwe pattern: unfold step_inst_base, show source bytes equal
   from inv field equality, apply both_sides_wmwe, discharge NAS. *)
fun wmwe_nas_tac field_eq =
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  field_eq by gvs[m2v_inv_noix_def] >>
  gvs[] >> irule m2v_inv_noix_both_sides_wmwe >> simp[] >>
  ho_match_mp_tac nas_write_range_disjoint >>
  qexistsl [`bb`, `inst`] >> simp[mem_write_ops_def, is_immutable_op_def];

Resume m2v_nonpromoted_mem_dispatch[dloadbytes]:
  wmwe_nas_tac `s1.vs_data_section = s2.vs_data_section`
QED

Resume m2v_nonpromoted_mem_dispatch[calldatacopy]:
  wmwe_nas_tac `s1.vs_call_ctx = s2.vs_call_ctx`
QED

Resume m2v_nonpromoted_mem_dispatch[codecopy]:
  wmwe_nas_tac `s1.vs_code = s2.vs_code`
QED

Resume m2v_nonpromoted_mem_dispatch[returndatacopy]:
  wmwe_nas_tac `s1.vs_returndata = s2.vs_returndata`
QED

Resume m2v_nonpromoted_mem_dispatch[extcodecopy]:
  wmwe_nas_tac `s1.vs_accounts = s2.vs_accounts`
QED

Resume m2v_nonpromoted_mem_dispatch[mstore8]:
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(),
      mstore8_eq_wmwe, exec_write2_def] >>
  `eval_operand op1 s1 = SOME addr` by gvs[] >>
  irule m2v_inv_noix_both_sides_wmwe >> simp[] >>
  rpt strip_tac >> `addr' = w2n addr` by simp[] >> gvs[] >>
  mp_tac (Q.SPECL [`fn`, `s1`, `bb`, `inst`] nas_write_range_disjoint) >>
  simp[mem_write_ops_def, is_immutable_op_def, eval_operand_def] >>
  qexists `w2n addr` >> simp[]
QED

Resume m2v_nonpromoted_mem_dispatch[mcopy]:
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(),
      mcopy_def, LET_THM] >>
  (* Source bytes agree: inv memory clause + NAS read range disjointness *)
  `TAKE (w2n sz) (DROP (w2n src) s1.vs_memory ++ REPLICATE (w2n sz) 0w) =
   TAKE (w2n sz) (DROP (w2n src) s2.vs_memory ++ REPLICATE (w2n sz) 0w)`
    by (irule mem_byte_agrees_take_drop >> rpt strip_tac >>
        qpat_x_assum `m2v_inv_noix _ _ _` mp_tac >>
        simp[m2v_inv_noix_def] >> strip_tac >>
        first_x_assum irule >>
        `eval_operand op_src s1 = SOME src` by gvs[] >>
        mp_tac (Q.SPECL [`fn`, `s1`, `bb`, `inst`]
                nas_read_range_disjoint) >>
        simp[mem_read_ops_def, is_immutable_op_def, eval_operand_def] >>
        disch_then irule >> simp[]) >>
  gvs[] >> irule m2v_inv_noix_both_sides_wmwe >> simp[] >>
  ho_match_mp_tac nas_write_range_disjoint >>
  qexistsl [`bb`, `inst`] >> simp[mem_write_ops_def, is_immutable_op_def]
QED

Resume m2v_nonpromoted_mem_dispatch[mstore]:
  ho_match_mp_tac m2v_step_nonpromoted_mstore >>
  qpat_x_assum `step_inst _ _ _ s1 = _` mp_tac >>
  simp[step_inst_non_invoke] >> suspend "mstore_base"
QED

Resume m2v_nonpromoted_mem_dispatch[mstore_base]:
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >>
  suspend "mstore_exec"
QED

Resume m2v_nonpromoted_mem_dispatch[mstore_exec]:
  simp[exec_write2_def, AllCaseEqs()] >> suspend "mstore_done"
QED

Resume m2v_nonpromoted_mem_dispatch[mstore_done]:
  strip_tac >> gvs[] >>
  rename1 `eval_operand _ s2 = SOME data_v` >>
  `eval_operand op1 s1 = SOME addr` by gvs[] >>
  qexistsl [`s1`, `w2n addr`, `data_v`] >> simp[] >>
  rpt strip_tac >>
  drule_all m2v_inv_noix_alloca_bridge >> strip_tac >>
  irule (iffRL DISJ_COMM) >>
  ho_match_mp_tac promoted_region_disjoint_from_nonpromoted >>
  qexistsl [`fn`, `s1`, `inst_id`] >> simp[] >>
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`, `s1`, `bb`, `inst`,
    `<| iao_ofst := op1; iao_size := SOME (Lit 32w);
        iao_max_size := SOME (Lit 32w) |>`,
    `addr`, `32w`, `Lit 32w`] nas_write_range_disjoint) >>
  (impl_tac >-
    simp[mem_write_ops_def, is_immutable_op_def, eval_operand_def,
         lt_32_dimword_256, arithmeticTheory.LESS_MOD]) >>
  simp[lt_32_dimword_256, arithmeticTheory.LESS_MOD] >>
  metis_tac[]
QED

Resume m2v_nonpromoted_mem_dispatch[mload]:
  ho_match_mp_tac m2v_step_nonpromoted_read1 >>
  qexistsl [`\addr s. mload (w2n addr) s`, `s1`] >>
  ASM_REWRITE_TAC[step_inst_non_invoke, step_inst_base_def,
                  is_alloca_op_def] >> gvs[] >>
  rpt strip_tac >>
  irule mload_mem_byte_eq >> rpt strip_tac >>
  qpat_x_assum `m2v_inv_noix _ _ _` mp_tac >>
  simp[m2v_inv_noix_def] >> strip_tac >>
  first_x_assum irule >>
  mp_tac (Q.SPECL [`fn`, `s1`, `bb`, `inst`] nas_read_range_disjoint) >>
  simp[mem_read_ops_def, is_immutable_op_def, eval_operand_def] >>
  disch_then irule >>
  `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
    (irule step_inst_non_invoke >> simp[]) >>
  qpat_x_assum `step_inst fuel ctx inst s1 = OK v1` mp_tac >>
  ASM_REWRITE_TAC[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >>
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[eval_operand_def, lt_32_dimword_256, arithmeticTheory.LESS_MOD]
QED

Finalise m2v_nonpromoted_mem_dispatch

Resume m2v_nonterminal_step_dispatch[nonpromoted_mem]:
  (* Opcodes with memory effects, not alloca, not ext_call.
     Narrow to 14 opcodes, then handle per-category. *)
  `inst.inst_opcode <> MEMTOP`
    by (qpat_x_assum `EVERY _ bb.bb_instructions` mp_tac >>
        simp[EVERY_MEM] >> disch_then irule >>
        simp[Abbr `inst`] >> simp[EL_MEM]) >>
  irule m2v_nonpromoted_mem_dispatch >>
  simp[] >>
  conj_tac >- (qexists `bb` >> simp[]) >>
  conj_tac >- metis_tac[mem_effect_opcodes] >>
  qexists `s1` >> simp[]
QED

Triviality ext_call_not_immutable:
  is_ext_call_op op ==> ~is_immutable_op op
Proof
  Cases_on `op` >> simp[is_ext_call_op_def, is_immutable_op_def]
QED

Resume m2v_nonterminal_step_dispatch[ext_call]:
  gvs[step_inst_non_invoke] >>
  match_mp_tac m2v_step_ext_call >>
  simp[] >>
  metis_tac[ssa_promo_ao_not_in_outputs, ext_call_not_immutable]
QED

Finalise m2v_nonterminal_step_dispatch

(* ================================================================
   EXEC_BLOCK STEP CHAIN (m2v-adapted)
   Adapted from memmerging: uses get_instruction instead of EL+LENGTH.
   ================================================================ *)

(* Non-terminal step chain: unfold exec_block one step on both sides.
   Requires step-level simulation (Error ∨ lift_result) and IH. *)
Theorem m2v_exec_block_step_chain:
  !R R' inst1 inst2 bb1 bb2 fuel ctx s1 s2.
    s1.vs_inst_idx < LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    EL s1.vs_inst_idx bb1.bb_instructions = inst1 /\
    get_instruction bb2 s1.vs_inst_idx = SOME inst2 /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ((?e. step_inst fuel ctx inst1 s1 = Error e) \/
     lift_result R R' R' (step_inst fuel ctx inst1 s1)
                          (step_inst fuel ctx inst2 s2)) /\
    (!s1' s2'. step_inst fuel ctx inst1 s1 = OK s1' /\
               step_inst fuel ctx inst2 s2 = OK s2' /\
               R s1' s2' ==>
      (?e. exec_block fuel ctx bb1
             (s1' with vs_inst_idx := SUC s1.vs_inst_idx) = Error e) \/
      lift_result R R' R'
        (exec_block fuel ctx bb1 (s1' with vs_inst_idx := SUC s1.vs_inst_idx))
        (exec_block fuel ctx bb2 (s2' with vs_inst_idx := SUC s1.vs_inst_idx)))
    ==>
    (?e. exec_block fuel ctx bb1 s1 = Error e) \/
    lift_result R R' R' (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac
  >- ((* Error on step => Error on exec_block *)
      DISJ1_TAC >> qexists `e` >>
      ONCE_REWRITE_TAC[exec_block_def] >>
      simp[get_instruction_def])
  >> (* lift_result on step *)
  ONCE_REWRITE_TAC[exec_block_def] >>
  `get_instruction bb1 s1.vs_inst_idx = SOME inst1` by
    simp[get_instruction_def] >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst1 s1` >>
  Cases_on `step_inst fuel ctx inst2 s2` >>
  gvs[lift_result_def]
QED

(* Helper: per-block simulation at arbitrary index *)
(* Non-terminal instruction must not be at the last position *)
Theorem nonterm_not_last:
  !bb i. bb_well_formed bb /\ i < LENGTH bb.bb_instructions /\
    ~is_terminator (EL i bb.bb_instructions).inst_opcode ==>
    i < LENGTH bb.bb_instructions - 1
Proof
  rpt strip_tac >> CCONTR_TAC >>
  gvs[bb_well_formed_def, LAST_EL, NULL_EQ] >>
  `i = PRE (LENGTH bb.bb_instructions)` by simp[] >>
  gvs[]
QED



(* ================================================================
   INVARIANT PRESERVATION FOR STATE TRANSFORMS
   ================================================================ *)

(* m2v_inv_noix preserved by halt_state *)
Theorem m2v_inv_noix_halt_state:
  !fn s1 s2. m2v_inv_noix fn s1 s2 ==>
    m2v_inv_noix fn (halt_state s1) (halt_state s2)
Proof
  rw[m2v_inv_noix_def, halt_state_def, lookup_var_def,
     mem_byte_def, in_promoted_region_def, mload_def,
     allocas_non_overlapping_def] >> metis_tac[]
QED

(* m2v_inv_noix preserved by jump_to *)
Theorem m2v_inv_noix_jump_to:
  !fn s1 s2 lbl. m2v_inv_noix fn s1 s2 ==>
    m2v_inv_noix fn (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[m2v_inv_noix_def, jump_to_def, lookup_var_def,
     mem_byte_def, in_promoted_region_def, mload_def,
     allocas_non_overlapping_def] >> metis_tac[]
QED

(* m2v_inv_noix preserved by set_returndata *)
Theorem m2v_inv_noix_set_returndata:
  !fn s1 s2 rd. m2v_inv_noix fn s1 s2 ==>
    m2v_inv_noix fn (set_returndata rd s1) (set_returndata rd s2)
Proof
  rw[m2v_inv_noix_def, set_returndata_def, lookup_var_def,
     mem_byte_def, in_promoted_region_def, mload_def,
     allocas_non_overlapping_def] >> metis_tac[]
QED

(* m2v_non32_ok preserved by halt_state *)
Theorem m2v_non32_ok_halt_state:
  !fn s1 s2. m2v_non32_ok fn s1 s2 ==>
    m2v_non32_ok fn (halt_state s1) (halt_state s2)
Proof
  rw[m2v_non32_ok_def, halt_state_def, lookup_var_def]
QED

(* m2v_non32_ok preserved by jump_to *)
Theorem m2v_non32_ok_jump_to:
  !fn s1 s2 lbl. m2v_non32_ok fn s1 s2 ==>
    m2v_non32_ok fn (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[m2v_non32_ok_def, jump_to_def, lookup_var_def]
QED

(* m2v_non32_ok preserved by set_returndata *)
Theorem m2v_non32_ok_set_returndata:
  !fn s1 s2 rd. m2v_non32_ok fn s1 s2 ==>
    m2v_non32_ok fn (set_returndata rd s1) (set_returndata rd s2)
Proof
  rw[m2v_non32_ok_def, set_returndata_def, lookup_var_def]
QED

(* m2v_ao_undef_sync preserved by halt_state *)
Theorem m2v_ao_undef_sync_halt_state:
  !fn s1 s2. m2v_ao_undef_sync fn s1 s2 ==>
    m2v_ao_undef_sync fn (halt_state s1) (halt_state s2)
Proof
  rw[m2v_ao_undef_sync_def, halt_state_def, lookup_var_def]
QED

(* m2v_ao_undef_sync preserved by jump_to *)
Theorem m2v_ao_undef_sync_jump_to:
  !fn s1 s2 lbl. m2v_ao_undef_sync fn s1 s2 ==>
    m2v_ao_undef_sync fn (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[m2v_ao_undef_sync_def, jump_to_def, lookup_var_def]
QED

(* m2v_ao_undef_sync preserved by set_returndata *)
Theorem m2v_ao_undef_sync_set_returndata:
  !fn s1 s2 rd. m2v_ao_undef_sync fn s1 s2 ==>
    m2v_ao_undef_sync fn (set_returndata rd s1) (set_returndata rd s2)
Proof
  rw[m2v_ao_undef_sync_def, set_returndata_def, lookup_var_def]
QED

(* m2v_ao_undef_sync preserved by same-value vs_accounts update *)
Theorem m2v_ao_undef_sync_update_accounts:
  !fn s1 s2 a. m2v_ao_undef_sync fn s1 s2 ==>
    m2v_ao_undef_sync fn (s1 with vs_accounts := a) (s2 with vs_accounts := a)
Proof
  rw[m2v_ao_undef_sync_def, lookup_var_def]
QED

(* m2v_inv_noix preserved by same-value vs_accounts update *)
Theorem m2v_inv_noix_update_accounts:
  !fn s1 s2 a. m2v_inv_noix fn s1 s2 ==>
    m2v_inv_noix fn (s1 with vs_accounts := a) (s2 with vs_accounts := a)
Proof
  rw[m2v_inv_noix_def, lookup_var_def,
     mem_byte_def, in_promoted_region_def, mload_def,
     allocas_non_overlapping_def] >> metis_tac[]
QED

(* m2v_non32_ok preserved by vs_accounts update *)
Theorem m2v_non32_ok_update_accounts:
  !fn s1 s2 a. m2v_non32_ok fn s1 s2 ==>
    m2v_non32_ok fn (s1 with vs_accounts := a) (s2 with vs_accounts := a)
Proof
  rw[m2v_non32_ok_def, lookup_var_def]
QED

(* eval_operands agreement from operand agreement *)
Theorem eval_operands_agrees:
  !ops s1 s2.
    (!op. MEM op ops ==> eval_operand op s1 = eval_operand op s2) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s1 = eval_operand h s2` by simp[] >>
  Cases_on `eval_operand h s1` >> simp[] >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> simp[]) >>
  simp[]
QED

(* For FIND=NONE easy terminators (not RETURN/REVERT), step_inst on s1
   and s2 produce lift_result-related outputs. *)
Theorem m2v_step_easy_terminator:
  !fn inst s1 s2 fuel ctx.
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\
    m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> RETURN /\
    inst.inst_opcode <> REVERT /\
    inst.inst_opcode <> DRET /\
    inst.inst_opcode <> RETFMP ==>
    lift_result (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2)
                (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2)
                (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2)
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  simp[step_inst_non_invoke] >>
  SUBGOAL_THEN ``!op. MEM op inst.inst_operands ==>
    eval_operand op s1 = eval_operand op s2`` assume_tac
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`,`op`]
        m2v_inv_noix_eval_agrees) >> simp[]) >>
  SUBGOAL_THEN ``eval_operands inst.inst_operands s1 =
    eval_operands inst.inst_operands s2`` assume_tac
  >- (irule eval_operands_agrees >> simp[]) >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
  >- (ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[lift_result_def] >>
      metis_tac[m2v_inv_noix_jump_to, m2v_non32_ok_jump_to,
                m2v_ao_undef_sync_jump_to])
  >- (ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[lift_result_def] >>
      metis_tac[m2v_inv_noix_jump_to, m2v_non32_ok_jump_to,
                m2v_ao_undef_sync_jump_to])
  >- (ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[lift_result_def] >>
      metis_tac[m2v_inv_noix_jump_to, m2v_non32_ok_jump_to,
                m2v_ao_undef_sync_jump_to])
  >- (ASM_REWRITE_TAC[step_inst_base_def] >>
      (Cases_on `eval_operands inst.inst_operands s2`
       >- gvs[lift_result_def]) >>
      Cases_on `x` >> gvs[lift_result_def])
  >- (ASM_REWRITE_TAC[step_inst_base_def] >> simp[lift_result_def] >>
      metis_tac[m2v_inv_noix_halt_state, m2v_non32_ok_halt_state,
                m2v_ao_undef_sync_halt_state])
  >- (ASM_REWRITE_TAC[step_inst_base_def] >> simp[lift_result_def] >>
      metis_tac[m2v_inv_noix_halt_state, m2v_non32_ok_halt_state,
                m2v_ao_undef_sync_halt_state])
  (* SELFDESTRUCT: extract call_ctx/accounts agreement before case split. *)
  >- (SUBGOAL_THEN ``s1.vs_call_ctx = s2.vs_call_ctx /\
        s1.vs_accounts = s2.vs_accounts`` strip_assume_tac
      >- gvs[m2v_inv_noix_def] >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[lift_result_def] >>
      metis_tac[m2v_inv_noix_update_accounts, m2v_inv_noix_halt_state,
                m2v_non32_ok_update_accounts, m2v_non32_ok_halt_state,
                m2v_ao_undef_sync_update_accounts,
                m2v_ao_undef_sync_halt_state]) >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[lift_result_def] >>
  metis_tac[m2v_inv_noix_set_returndata, m2v_inv_noix_halt_state,
            m2v_non32_ok_set_returndata, m2v_non32_ok_halt_state,
            m2v_ao_undef_sync_set_returndata,
            m2v_ao_undef_sync_halt_state]
QED

(* ================================================================== *)
(* nao (vs_alloca_next) preservation helpers — moved early for     *)
(* use in Resume blocks below.                                         *)
(* ================================================================== *)

(* Strengthen lift_result with an additional property P *)
Theorem lift_result_strengthen:
  !R R' R'' P r1 r2.
    lift_result R R' R'' r1 r2 /\
    (!s1 s2. r1 = OK s1 /\ r2 = OK s2 ==> P s1 s2) /\
    (!s1 s2. r1 = Halt s1 /\ r2 = Halt s2 ==> P s1 s2) /\
    (!a s1 s2. r1 = Abort a s1 /\ r2 = Abort a s2 ==> P s1 s2) /\
    (!v s1 s2. r1 = IntRet v s1 /\ r2 = IntRet v s2 ==> P s1 s2) ==>
    lift_result (\s1 s2. R s1 s2 /\ P s1 s2) (\s1 s2. R' s1 s2 /\ P s1 s2)
                (\s1 s2. R'' s1 s2 /\ P s1 s2) r1 r2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> gvs[lift_result_def]
QED

(* vs_alloca_next preserved by halt/revert/set_returndata/jump_to *)
Theorem nao_halt_revert:
  !s rd. (halt_state s).vs_alloca_next = s.vs_alloca_next /\
         (revert_state s).vs_alloca_next = s.vs_alloca_next /\
         (set_returndata rd s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[halt_state_def, revert_state_def,
       set_returndata_def]
QED

(* Combined 4-tuple invariant preservation through terminal state wrapping.
   Covers halt_state(set_returndata rd s) and revert_state(set_returndata rd s). *)
Theorem m2v_terminal_inv_preserved:
  !fn s1 s2 rd.
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\
    s1.vs_alloca_next = s2.vs_alloca_next ==>
    (m2v_inv_noix fn (halt_state (set_returndata rd s1))
                     (halt_state (set_returndata rd s2)) /\
     m2v_non32_ok fn (halt_state (set_returndata rd s1))
                     (halt_state (set_returndata rd s2)) /\
     m2v_ao_undef_sync fn (halt_state (set_returndata rd s1))
                          (halt_state (set_returndata rd s2)) /\
     (halt_state (set_returndata rd s1)).vs_alloca_next =
     (halt_state (set_returndata rd s2)).vs_alloca_next) /\
    (m2v_inv_noix fn (revert_state (set_returndata rd s1))
                     (revert_state (set_returndata rd s2)) /\
     m2v_non32_ok fn (revert_state (set_returndata rd s1))
                     (revert_state (set_returndata rd s2)) /\
     m2v_ao_undef_sync fn (revert_state (set_returndata rd s1))
                          (revert_state (set_returndata rd s2)) /\
     (revert_state (set_returndata rd s1)).vs_alloca_next =
     (revert_state (set_returndata rd s2)).vs_alloca_next)
Proof
  rpt strip_tac >>
  `revert_state = halt_state` by simp[FUN_EQ_THM, revert_state_def, halt_state_def] >>
  gvs[] >> rpt conj_tac >>
  TRY (irule m2v_inv_noix_halt_state >> irule m2v_inv_noix_set_returndata >>
       simp[] >> NO_TAC) >>
  TRY (MATCH_MP_TAC m2v_non32_ok_halt_state >>
       MATCH_MP_TAC m2v_non32_ok_set_returndata >> simp[] >> NO_TAC) >>
  TRY (irule m2v_ao_undef_sync_halt_state >>
       irule m2v_ao_undef_sync_set_returndata >> simp[] >> NO_TAC) >>
  simp[nao_halt_revert]
QED

(* RETURN/REVERT with FIND=NONE: same inst both sides, memory reads agree *)
val return_revert_find_none_tac =
  simp[step_inst_non_invoke] >>
  `?off_op sz_op. inst.inst_operands = [off_op; sz_op]` by (
    qpat_x_assum `inst_wf _` mp_tac >> simp[Once inst_wf_def] >>
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[]) >>
  `eval_operand off_op s1 = eval_operand off_op s2` by
    (mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`,`off_op`]
       m2v_inv_noix_eval_agrees) >> simp[MEM]) >>
  `eval_operand sz_op s1 = eval_operand sz_op s2` by
    (mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`,`sz_op`]
       m2v_inv_noix_eval_agrees) >> simp[MEM]) >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  Cases_on `eval_operand off_op s2` >> gvs[] >>
  Cases_on `eval_operand sz_op s2` >> gvs[] >>
  rename1 `eval_operand off_op s2 = SOME off_val` >>
  rename1 `eval_operand sz_op s2 = SOME sz_val` >>
  `!addr. w2n off_val <= addr /\ addr < w2n off_val + w2n sz_val ==>
          ~in_promoted_region fn s1 addr` by (
    ho_match_mp_tac nas_read_range_disjoint >>
    qexistsl [`bb`, `inst`] >>
    simp[mem_read_ops_def, is_immutable_op_def]) >>
  `TAKE (w2n sz_val) (DROP (w2n off_val) s1.vs_memory ++
     REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n off_val) s2.vs_memory ++
     REPLICATE (w2n sz_val) 0w)` by (
    irule mem_byte_agrees_take_drop >> rpt strip_tac >>
    qpat_x_assum `m2v_inv_noix _ _ _`
      (strip_assume_tac o REWRITE_RULE[m2v_inv_noix_def]) >>
    first_x_assum irule >> first_x_assum irule >> simp[]) >>
  simp[lift_result_def] >>
  mp_tac m2v_terminal_inv_preserved >>
  disch_then (qspecl_then [`fn`,`s1`,`s2`,
    `TAKE (w2n sz_val) (DROP (w2n off_val) s1.vs_memory ++
       REPLICATE (w2n sz_val) 0w)`] mp_tac) >>
  simp[];

Theorem m2v_step_return_revert_find_none:
  !fn bb inst s1 s2 fuel ctx.
    (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
    FIND (\(ao,_,_). MEM (Var ao) inst.inst_operands)
         (m2v_promo_list fn) = NONE /\
    m2v_inv_noix fn s1 s2 /\
    m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\
    m2v_fresh_names_disjoint fn /\
    m2v_nonpromoted_access_safe fn s1 /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    (?e. step_inst fuel ctx inst s1 = Error e) \/
    lift_result
      (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
               m2v_ao_undef_sync fn s1 s2 /\
               s1.vs_alloca_next = s2.vs_alloca_next)
      (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
               m2v_ao_undef_sync fn s1 s2 /\
               s1.vs_alloca_next = s2.vs_alloca_next)
      (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
               m2v_ao_undef_sync fn s1 s2 /\
               s1.vs_alloca_next = s2.vs_alloca_next)
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = RETURN` >> gvs[]
  >- return_revert_find_none_tac >>
  return_revert_find_none_tac
QED

Theorem nao_jump_to:
  !s lbl. (jump_to lbl s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[jump_to_def]
QED

(* nao preserved through non-terminal easy terminator step_inst
   (JMP/JNZ/DJMP/STOP/SELFDESTRUCT). All produce halt_state/jump_to. *)
(* nao preserved through easy terminators — OK result case only.
   For other result shapes (Halt/Abort/IntRet), derive nao from
   nao_halt_revert/nao_jump_to + m2v_inv_noix alloca_next agreement. *)
Theorem nao_easy_terminator:
  !fn inst s1 s2 fuel ctx.
    m2v_inv_noix fn s1 s2 /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> RETURN /\
    inst.inst_opcode <> REVERT ==>
    !s1' s2'. step_inst fuel ctx inst s1 = OK s1' /\
              step_inst fuel ctx inst s2 = OK s2' ==>
              s1'.vs_alloca_next = s2'.vs_alloca_next
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  `inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  qspecl_then [`inst`, `s1`, `s1'`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_alloca_next >>
  simp[] >> strip_tac >>
  qspecl_then [`inst`, `s2`, `s2'`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_alloca_next >>
  simp[]
QED

(* MAX a (MAX L1 d) = MAX a (MAX L2 d) when MAX a L1 = MAX a L2.
   Covers: same mstore on both sides (d = off+32). *)
Theorem nao_max_ext_cong:
  !a L1 L2 d. MAX a L1 = MAX a L2 ==>
    MAX a (MAX L1 d) = MAX a (MAX L2 d)
Proof metis_tac[arithmeticTheory.MAX_ASSOC]
QED

(* MAX a (MAX L1 d) = MAX a L2 when d <= a and MAX a L1 = MAX a L2.
   Covers: promoted MSTORE (s1 extends mem, s2 doesn't). *)
Theorem nao_bounded_ext:
  !a L1 L2 d. MAX a L1 = MAX a L2 /\ d <= a ==>
    MAX a (MAX L1 d) = MAX a L2
Proof simp[arithmeticTheory.MAX_DEF] >> rpt (COND_CASES_TAC >> gvs[])
QED

(* exec_block at terminal: wraps step_inst result *)
Theorem exec_block_terminal_lift:
  !R inst inst2 bb bb2 s1 s2 fuel ctx.
    get_instruction bb s1.vs_inst_idx = SOME inst /\
    get_instruction bb2 s2.vs_inst_idx = SOME inst2 /\
    is_terminator inst.inst_opcode /\
    is_terminator inst2.inst_opcode /\
    (!s1 s2. R s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    ((?e. step_inst fuel ctx inst s1 = Error e) \/
     lift_result R R R
       (step_inst fuel ctx inst s1) (step_inst fuel ctx inst2 s2)) ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result R R R
      (exec_block fuel ctx bb s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac
  >- (DISJ1_TAC >> ONCE_REWRITE_TAC[exec_block_def] >> simp[]) >>
  DISJ2_TAC >>
  ONCE_REWRITE_TAC[exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst2 s2` >>
  gvs[lift_result_def] >>
  `v'.vs_halted = v.vs_halted` by metis_tac[] >>
  pop_assum SUBST_ALL_TAC >>
  Cases_on `v.vs_halted` >> gvs[lift_result_def]
QED

(* exec_block at terminal with 1:2 expansion.
   Original: 1 terminal instruction at idx.
   Transformed: 1 non-terminal at idx, 1 terminal at idx+1.
   Given step_inst simulation for the combined 2-step. *)
Theorem exec_block_1to2_terminal_lift:
  !R inst pre_inst post_inst bb bb2 s1 s2 fuel ctx s2m.
    get_instruction bb s1.vs_inst_idx = SOME inst /\
    get_instruction bb2 s2.vs_inst_idx = SOME pre_inst /\
    get_instruction bb2 (SUC s2.vs_inst_idx) = SOME post_inst /\
    is_terminator inst.inst_opcode /\
    ~is_terminator pre_inst.inst_opcode /\
    pre_inst.inst_opcode <> INVOKE /\
    is_terminator post_inst.inst_opcode /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!s1 s2. R s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    step_inst fuel ctx pre_inst s2 = OK s2m /\
    ((?e. step_inst fuel ctx inst s1 = Error e) \/
     lift_result R R R
       (step_inst fuel ctx inst s1)
       (step_inst fuel ctx post_inst
          (s2m with vs_inst_idx := SUC s2.vs_inst_idx))) ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result R R R
      (exec_block fuel ctx bb s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac
  >- (DISJ1_TAC >> ONCE_REWRITE_TAC[exec_block_def] >> simp[]) >>
  DISJ2_TAC >>
  (* Unfold original side *)
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[exec_block_def])) >> simp[] >>
  (* Unfold transformed side once: step pre_inst *)
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[exec_block_def])) >> simp[] >>
  simp[step_inst_non_invoke] >>
  (* Unfold transformed side again: step post_inst *)
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[exec_block_def])) >> simp[] >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx post_inst
    (s2m with vs_inst_idx := SUC s2.vs_inst_idx)` >>
  gvs[lift_result_def] >>
  `v'.vs_halted = v.vs_halted` by metis_tac[] >>
  pop_assum SUBST_ALL_TAC >>
  Cases_on `v.vs_halted` >> gvs[lift_result_def]
QED

(* Terminal instruction: may be RETURN (1:2) or other terminator (1:1) *)

(* FIND=NONE terminal: both sides execute same instruction *)



(* mstore on s2 side only, at a promoted alloca region, preserves m2v_inv_noix.
   Used for RETURN promotion: we mstore pval back before RETURN. *)
Theorem m2v_inv_noix_mstore_s2_only:
  !fn s1 s2 ao pvar addr.
    m2v_inv_noix fn s1 s2 /\
    MEM (ao, pvar, 32) (m2v_promo_list fn) /\
    lookup_var ao s1 = SOME addr /\
    IS_SOME (lookup_var pvar s2) ==>
    m2v_inv_noix fn s1 (mstore (w2n addr) (mload (w2n addr) s1) s2)
Proof
  rpt strip_tac >>
  `!i. w2n addr <= i /\ i < w2n addr + 32 ==>
       in_promoted_region fn s1 i` by
    metis_tac[m2v_inv_noix_addr_in_region] >>
  gvs[m2v_inv_noix_def, mstore_preserves] >>
  rpt conj_tac
  (* mem outside promoted *)
  >- (rpt strip_tac >>
      Cases_on `i < w2n addr \/ w2n addr + 32 <= i`
      >- metis_tac[mem_byte_mstore_outside]
      >> `w2n addr <= i /\ i < w2n addr + 32` by simp[] >>
         metis_tac[])
  (* bridge *)
  >- metis_tac[]
  (* sync *)
  >> metis_tac[mstore_preserves]
QED

(* Return data after mstore roundtrip agrees with original.
   Writing mload(off,s1) to off in s2, then reading k<=32 bytes from off,
   gives the same result as reading from s1. *)
(* mstore at off writes exactly word_to_bytes at positions [off..off+32) *)
Theorem DROP_mstore_prefix:
  !off (pval:bytes32) s.
    TAKE 32 (DROP off (mstore off pval s).vs_memory) =
    word_to_bytes pval T
Proof
  rpt gen_tac >> simp[mstore_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `TAKE off expanded` >>
  `off + 32 <= LENGTH expanded` by
    (unabbrev_all_tac >> rw[] >> simp[]) >>
  DEP_REWRITE_TAC[DROP_APPEND1] >>
  simp[LENGTH_TAKE, Abbr `expanded`] >>
  simp[DROP_TAKE_EQ_NIL, TAKE_APPEND1, len_word_to_bytes_256]
QED

Theorem LENGTH_mstore_mem:
  !off (v:bytes32) s. off + 32 <= LENGTH (mstore off v s).vs_memory
Proof
  rw[mstore_def, LET_THM, len_word_to_bytes_256]
QED

Theorem take_append_pad:
  !n (l:'a list) a b x. n <= LENGTH l + a /\ n <= LENGTH l + b ==>
    TAKE n (l ++ REPLICATE a x) = TAKE n (l ++ REPLICATE b x)
Proof
  rw[LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_APPEND, LENGTH_REPLICATE] >>
  rw[EL_TAKE, EL_APPEND_EQN, EL_REPLICATE, LENGTH_REPLICATE]
QED

Theorem return_data_mstore_roundtrip:
  !off (pval:bytes32) s1 s2 k.
    pval = mload off s1 /\ k <= 32 ==>
    TAKE k (DROP off (mstore off pval s2).vs_memory ++ REPLICATE k 0w) =
    TAKE k (DROP off s1.vs_memory ++ REPLICATE k 0w)
Proof
  rpt strip_tac >>
  (* Both sides = TAKE k (word_to_bytes pval T).
     word_to_bytes inverts mload *)
  qabbrev_tac `bytes = word_to_bytes pval T` >>
  `bytes = TAKE 32 (DROP off s1.vs_memory ++ REPLICATE 32 0w)` by (
    simp[Abbr `bytes`, mload_def, LET_THM] >>
    irule word_bytes_roundtrip_256 >> simp[LENGTH_TAKE_EQ]) >>
  (* mstore writes bytes at [off..off+32) *)
  `TAKE 32 (DROP off (mstore off pval s2).vs_memory) = bytes` by
    simp[DROP_mstore_prefix, Abbr `bytes`] >>
  (* DROP off after mstore has >= 32 elements *)
  qabbrev_tac `mem2 = DROP off (mstore off pval s2).vs_memory` >>
  `32 <= LENGTH mem2` by (
    simp[Abbr `mem2`, LENGTH_DROP] >>
    mp_tac (Q.SPECL [`off`,`pval`,`s2`] LENGTH_mstore_mem) >> simp[]) >>
  (* LHS = TAKE k bytes *)
  `TAKE k (mem2 ++ REPLICATE k 0w) = TAKE k mem2` by
    (irule TAKE_APPEND1 >> simp[]) >>
  `TAKE k mem2 = TAKE k bytes` by
    metis_tac[TAKE_TAKE_T] >>
  (* RHS = TAKE k bytes *)
  qabbrev_tac `mem1 = DROP off s1.vs_memory` >>
  `TAKE k (mem1 ++ REPLICATE k 0w) =
   TAKE k (mem1 ++ REPLICATE 32 0w)` by
    (irule take_append_pad >> simp[]) >>
  `TAKE k (mem1 ++ REPLICATE 32 0w) = TAKE k bytes` by
    metis_tac[TAKE_TAKE_T] >>
  simp[]
QED

(* m2v_non32_ok preserved through mstore (vars unchanged) *)
Theorem m2v_non32_ok_mstore:
  !fn s1 s2 off v.
    m2v_non32_ok fn s1 s2 ==> m2v_non32_ok fn s1 (mstore off v s2)
Proof
  rw[m2v_non32_ok_def, mstore_preserves]
QED

(* Updating vs_inst_idx on s2 preserves m2v_inv_noix and m2v_non32_ok *)
Theorem m2v_inv_noix_update_idx:
  !fn s1 s2 j k. m2v_inv_noix fn s1 s2 ==>
    m2v_inv_noix fn (s1 with vs_inst_idx := j) (s2 with vs_inst_idx := k)
Proof
  rpt strip_tac >>
  fs[m2v_inv_noix_def, lookup_var_def, mem_byte_def,
     in_promoted_region_def, mload_def, allocas_non_overlapping_def] >>
  metis_tac[]
QED

(* FIND=SOME terminal: promoted RETURN, 2-step simulation *)

Theorem lookup_var_mstore_idx:
  !x off v s k. lookup_var x (mstore off v s with vs_inst_idx := k) =
                 lookup_var x s
Proof
  simp[lookup_var_def, mstore_def, LET_THM]
QED

Theorem m2v_inv_noix_update_idx_s2:
  !fn s1 s2 k. m2v_inv_noix fn s1 s2 ==>
    m2v_inv_noix fn s1 (s2 with vs_inst_idx := k)
Proof
  rpt strip_tac >>
  fs[m2v_inv_noix_def, lookup_var_def, mem_byte_def,
     in_promoted_region_def, mload_def, allocas_non_overlapping_def] >>
  metis_tac[]
QED

Theorem m2v_non32_ok_update_idx_s2:
  !fn s1 s2 k. m2v_non32_ok fn s1 s2 ==>
    m2v_non32_ok fn s1 (s2 with vs_inst_idx := k)
Proof
  simp[m2v_non32_ok_def, lookup_var_def]
QED


(* Weakening lemma for lift_result with conjunction *)
Theorem lift_result_weaken_conj:
  !R1 R2 r1 r2.
    lift_result (\s1 s2. R1 s1 s2 /\ R2 s1 s2) (\s1 s2. R1 s1 s2 /\ R2 s1 s2)
                (\s1 s2. R1 s1 s2 /\ R2 s1 s2) r1 r2 ==>
    lift_result R1 R1 R1 r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def]
QED

(* Weaken OK relation in lift_result, keeping Halt/Abort/IntRet unchanged *)
Theorem lift_result_weaken_ok:
  !R1 R2 R' r1 r2.
    (!s1 s2. R1 s1 s2 ==> R2 s1 s2) /\
    lift_result R1 R' R' r1 r2 ==>
    lift_result R2 R' R' r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def]
QED

(* Non-terminal instruction: use chain with R = inv /\ non32 /\ ao_undef_sync.
   Chain passes step_inst result on s2 side to ih_cont,
   allowing pvars_set derivation for IH application. *)

(* step_inst_base can't Halt or IntRet for non-terminators *)
Triviality exec_result_helpers_no_halt_abort[simp]:
  (!f inst s s'. exec_pure1 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure1 f inst s <> Abort a s') /\
  (!f inst s s'. exec_pure2 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure2 f inst s <> Abort a s') /\
  (!f inst s s'. exec_pure3 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure3 f inst s <> Abort a s') /\
  (!f inst s s'. exec_read0 f inst s <> Halt s') /\
  (!f inst s a s'. exec_read0 f inst s <> Abort a s') /\
  (!f inst s s'. exec_read1 f inst s <> Halt s') /\
  (!f inst s a s'. exec_read1 f inst s <> Abort a s') /\
  (!f inst s s'. exec_write2 f inst s <> Halt s') /\
  (!f inst s a s'. exec_write2 f inst s <> Abort a s') /\
  (!inst s alloc_size s'. exec_alloca inst s alloc_size <> Halt s') /\
  (!inst s alloc_size a s'. exec_alloca inst s alloc_size <> Abort a s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_result_helpers_not_intret[simp]:
  (!f inst s vs s'. exec_pure1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure2 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure3 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read0 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_write2 f inst s <> IntRet vs s') /\
  (!inst s alloc_size vs s'. exec_alloca inst s alloc_size <> IntRet vs s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_not_intret[simp]:
  (!inst s g a v ao as_ ro rs is_s vs s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> IntRet vs s') /\
  (!inst s g a ao as_ ro rs vs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> IntRet vs s') /\
  (!inst s v off sz salt vs s'.
     exec_create inst s v off sz salt <> IntRet vs s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_no_halt_abort[simp]:
  (!inst s g a v ao as_ ro rs is_s s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Halt s') /\
  (!inst s g a v ao as_ ro rs is_s ab s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Abort ab s') /\
  (!inst s g a ao as_ ro rs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Halt s') /\
  (!inst s g a ao as_ ro rs ab s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Abort ab s') /\
  (!inst s v off sz salt s'.
     exec_create inst s v off sz salt <> Halt s') /\
  (!inst s v off sz salt ab s'.
     exec_create inst s v off sz salt <> Abort ab s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

val step_base_result_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def];

Theorem step_inst_base_no_halt:
  !inst s s'.
    step_inst_base inst s = Halt s' ==>
    is_terminator inst.inst_opcode
Proof
  step_base_result_tac
QED

Theorem step_inst_base_no_intret:
  !inst s vs s'.
    step_inst_base inst s = IntRet vs s' ==>
    is_terminator inst.inst_opcode
Proof
  step_base_result_tac
QED

(* Abort: both sides run same non-promoted instruction *)
Theorem step_inst_base_abort_input_equiv:
  !inst s1 s2 a s1'.
    step_inst_base inst s1 = Abort a s1' /\
    ~is_terminator inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_labels = s2.vs_labels ==>
    ?s2'. step_inst_base inst s2 = Abort a s2'
Proof
  ACCEPT_TAC passSharedFrameTheory.step_inst_base_abort_input_equiv
QED

(* Characterize abort state form for non-terminal step_inst_base *)
Theorem step_inst_base_abort_form:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode ==>
    (s' = halt_state (set_returndata [] s) /\ a = ExHalt_abort) \/
    (s' = revert_state (set_returndata [] s) /\ a = Revert_abort)
Proof
  step_base_result_tac
QED

(* m2v_non32_ok preserved under halt/revert state transform *)
Theorem m2v_non32_ok_abort_state:
  !fn s1 s2.
    m2v_non32_ok fn s1 s2 ==>
    m2v_non32_ok fn
      (halt_state (set_returndata [] s1))
      (halt_state (set_returndata [] s2)) /\
    m2v_non32_ok fn
      (revert_state (set_returndata [] s1))
      (revert_state (set_returndata [] s2))
Proof
  rw[m2v_non32_ok_def, halt_state_def, revert_state_def,
     set_returndata_def, lookup_var_def, mem_byte_def]
QED

(* m2v_ao_undef_sync preserved under halt/revert state transform *)
Theorem m2v_ao_undef_sync_abort_state:
  !fn s1 s2.
    m2v_ao_undef_sync fn s1 s2 ==>
    m2v_ao_undef_sync fn
      (halt_state (set_returndata [] s1))
      (halt_state (set_returndata [] s2)) /\
    m2v_ao_undef_sync fn
      (revert_state (set_returndata [] s1))
      (revert_state (set_returndata [] s2))
Proof
  rw[m2v_ao_undef_sync_def, halt_state_def, revert_state_def,
     set_returndata_def, lookup_var_def]
QED

(* m2v_inv_noix preserved under halt/revert state transform *)
Theorem m2v_inv_noix_abort_state:
  !fn s1 s2.
    m2v_inv_noix fn s1 s2 ==>
    m2v_inv_noix fn
      (halt_state (set_returndata [] s1))
      (halt_state (set_returndata [] s2)) /\
    m2v_inv_noix fn
      (revert_state (set_returndata [] s1))
      (revert_state (set_returndata [] s2))
Proof
  rw[m2v_inv_noix_def, halt_state_def, revert_state_def,
     set_returndata_def, lookup_var_def, mem_byte_def,
     in_promoted_region_def, mload_def, allocas_non_overlapping_def] >>
  metis_tac[]
QED



(* Fresh promoted pvars are never in any instruction's outputs *)
Theorem m2v_pvar32_not_in_inst_outputs:
  !fn bb inst ao pvar.
    m2v_fresh_names_disjoint fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\ MEM (ao,pvar,32) (m2v_promo_list fn) ==>
    ~MEM pvar inst.inst_outputs
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  drule m2v_promo_list_in_fresh_vars >> strip_tac >>
  drule_all m2v_fresh_not_in_block_outputs >> strip_tac >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

(* step_inst preserves IS_SOME of a fresh pvar (not in inst outputs) *)
Theorem m2v_step_preserves_pvar_is_some:
  !fn bb inst ao pvar fuel ctx s s'.
    m2v_fresh_names_disjoint fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\ MEM (ao,pvar,32) (m2v_promo_list fn) /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' /\
    IS_SOME (lookup_var pvar s) ==>
    IS_SOME (lookup_var pvar s')
Proof
  rpt strip_tac >>
  SUBGOAL_THEN ``lookup_var pvar s' = lookup_var pvar s`` (fn th => gvs[th])
  >- (drule venomInstProofsTheory.step_preserves_non_output_vars >>
      simp[] >> disch_then (qspec_then `pvar` mp_tac) >>
      (impl_tac >- metis_tac[m2v_pvar32_not_in_inst_outputs]) >> simp[])
QED

(* m2v_pvars_set advances from i to SUC i after dispatch on s2 side.
   Uses m2v_pvars_set_step: (1) existing pvars preserved across step,
   (2) if EL i is MSTORE to ao with sz=32, pvar IS_SOME after step.
   Key insight: pvars are fresh → not in any instruction's outputs,
   so lookup_var pvar preserved across any step. For MSTORE sz=32,
   ASSIGN writes pvar directly. pointer_confined rules out two distinct
   promoted ao's in a single MSTORE's operands. *)
Theorem m2v_pvars_set_after_dispatch:
  !fn bb i fuel ctx s2 v2.
    wf_function fn /\
    ssa_form fn /\
    m2v_fresh_names_disjoint fn /\
    alloca_pointer_confined fn /\
    MEM bb fn.fn_blocks /\
    bb_well_formed bb /\
    i < LENGTH bb.bb_instructions - 1 /\
    m2v_pvars_set fn bb i s2 /\
    step_inst fuel ctx (HD (m2v_rewrite_inst fn (EL i bb.bb_instructions)))
      s2 = OK v2 ==>
    m2v_pvars_set fn bb (SUC i) v2
Proof
  rpt strip_tac >>
  SUBGOAL_THEN ``i < LENGTH bb.bb_instructions`` assume_tac >- simp[] >>
  SUBGOAL_THEN ``MEM (EL i bb.bb_instructions) bb.bb_instructions`` assume_tac
  >- (simp[MEM_EL] >> qexists `i` >> simp[]) >>
  SUBGOAL_THEN ``MEM (EL i bb.bb_instructions) (fn_insts fn)`` assume_tac
  >- metis_tac[MEM_fn_insts] >>
  SUBGOAL_THEN ``~is_terminator (EL i bb.bb_instructions).inst_opcode``
    assume_tac
  >- (gvs[bb_well_formed_def] >> CCONTR_TAC >> gvs[] >> res_tac >> gvs[]) >>
  mp_tac (Q.SPECL [`fn`,`bb`,`i`,`s2`,`v2`] m2v_pvars_set_step) >>
  simp[] >> disch_then irule >>
  (* Case split on FIND to determine what instruction was actually stepped *)
  qpat_x_assum `step_inst _ _ (HD _) _ = _` mp_tac >>
  simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_,_). MEM (Var ao)
    (EL i bb.bb_instructions).inst_operands) (m2v_promo_list fn)`
  >- (simp[] >> strip_tac >> suspend "find_none")
  >> (rename1 `SOME entry` >> PairCases_on `entry` >>
      rename1 `SOME (fao, fpvar, fsz)` >>
      simp[] >> strip_tac >> suspend "find_some")
QED

Resume m2v_pvars_set_after_dispatch[find_none]:
  conj_tac
  (* MSTORE condition: vacuous — FIND=NONE contradicts MEM (Var ao) operands *)
  >- (rpt strip_tac >>
      SUBGOAL_THEN ``EVERY ($~ o (\(ao,_0:string,_1:num).
        MEM (Var ao) (EL i bb.bb_instructions).inst_operands))
        (m2v_promo_list fn)`` mp_tac
      >- gvs[GSYM FIND_NONE_EVERY]
      >> simp[EVERY_MEM] >>
      disch_then (qspec_then `(ao,pvar,32)` mp_tac) >> simp[])
  (* Preservation: original inst unchanged, use m2v_step_preserves_pvar_is_some *)
  >> (rpt strip_tac >>
      mp_tac (Q.SPECL [`fn`,`bb`,`EL i bb.bb_instructions`,`ao`,`pvar`,
        `fuel`,`ctx`,`s2`,`v2`] m2v_step_preserves_pvar_is_some) >>
      simp[])
QED

Resume m2v_pvars_set_after_dispatch[find_some]:
  (* Derive MEM of FIND result *)
  SUBGOAL_THEN ``MEM (fao,fpvar,fsz) (m2v_promo_list fn)``
    assume_tac
  >- (drule venomExecProofsTheory.FIND_MEM >> simp[]) >>
  SUBGOAL_THEN ``MEM (Var fao)
    (EL i bb.bb_instructions).inst_operands`` assume_tac
  >- (drule venomExecProofsTheory.FIND_P >> simp[]) >>
  conj_tac
  >- suspend "mstore_cond"
  >> suspend "preserve_cond"
QED

(* MSTORE condition: ao in operands with MSTORE ==> IS_SOME pvar *)
Resume m2v_pvars_set_after_dispatch[mstore_cond]:
  rpt strip_tac >>
  (* pointer_confined: both ao and fao occupy the offset slot *)
  mp_tac (Q.SPECL [`fn`,`bb`,`EL i bb.bb_instructions`,`fao`,`fpvar`,
    `fsz`] m2v_pointer_confined_mstore_ao_is_offset) >> simp[] >>
  mp_tac (Q.SPECL [`fn`,`bb`,`EL i bb.bb_instructions`,`ao`,`pvar`,
    `32`] m2v_pointer_confined_mstore_ao_is_offset) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  (* ao=fao since both are first operand; uniqueness gives pvar=fpvar, 32=fsz *)
  mp_tac (Q.SPECL [`fn`,`ao`,`pvar`,`32`,`fpvar`,`fsz`]
    m2v_promo_list_ao_unique) >> simp[] >> strip_tac >> gvs[] >>
  (* MSTORE+sz=32: promote_inst produces ASSIGN to pvar.  Keep the two
     operand-shape branches in separate suspended goals. *)
  gvs[m2v_promote_inst_def]
  >- (gvs[step_inst_non_invoke, is_terminator_def] >>
      suspend "mstore_cond_a_base")
  >- (gvs[step_inst_non_invoke, is_terminator_def] >>
      suspend "mstore_cond_b_base")
QED

Resume m2v_pvars_set_after_dispatch[mstore_cond_a_base]:
  gvs[step_inst_base_def] >> suspend "mstore_cond_a_exec"
QED

Resume m2v_pvars_set_after_dispatch[mstore_cond_b_base]:
  gvs[step_inst_base_def] >> suspend "mstore_cond_b_exec"
QED

Resume m2v_pvars_set_after_dispatch[mstore_cond_a_exec]:
  gvs[exec_read1_def, AllCaseEqs(), lookup_var_update] >>
  rpt strip_tac >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Resume m2v_pvars_set_after_dispatch[mstore_cond_b_exec]:
  gvs[exec_read1_def, AllCaseEqs(), lookup_var_update] >>
  rpt strip_tac >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Preservation condition: IS_SOME preserved across step *)
Resume m2v_pvars_set_after_dispatch[preserve_cond]:
  rpt strip_tac >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = MSTORE /\ fsz = 32`
  >- (
    (* MSTORE+sz=32: promoted to ASSIGN [val_op] [fpvar] *)
    mp_tac (Q.SPECL [`fn`,`bb`,`EL i bb.bb_instructions`,`fao`,`fpvar`,
      `fsz`] m2v_pointer_confined_mstore_ao_is_offset) >> simp[] >>
    strip_tac >> gvs[m2v_promote_inst_def] >>
    Cases_on `pvar = fpvar`
    >- gvs[step_inst_non_invoke, is_terminator_def,
            step_inst_base_def, exec_read1_def, AllCaseEqs(),
            lookup_var_update]
    >> (drule venomInstProofsTheory.step_preserves_non_output_vars >>
        simp[is_terminator_def] >>
        disch_then (qspec_then `pvar` mp_tac) >> simp[]))
  >> Cases_on `(EL i bb.bb_instructions).inst_opcode = MLOAD /\ fsz = 32`
  >- (
    (* MLOAD+sz=32: promoted to ASSIGN [Var fpvar] [out] *)
    gvs[m2v_promote_inst_def] >> every_case_tac >> gvs[] >>
    drule venomInstProofsTheory.step_preserves_non_output_vars >>
    simp[is_terminator_def] >>
    disch_then (qspec_then `pvar` mp_tac) >> simp[] >>
    (impl_tac >- metis_tac[m2v_pvar32_not_in_inst_outputs]) >>
    strip_tac >> gvs[])
  >> (
    (* Neither: promote_inst = [original_inst] *)
    SUBGOAL_THEN ``m2v_promote_inst fpvar fao fsz
        (EL i bb.bb_instructions) = [EL i bb.bb_instructions]``
        (fn th => gvs[th])
    >- (SUBGOAL_THEN ``(EL i bb.bb_instructions).inst_opcode <> RETURN``
          assume_tac
        >- (strip_tac >> gvs[is_terminator_def])
        >> simp[m2v_promote_inst_def])
    >> mp_tac (Q.SPECL [`fn`,`bb`,`EL i bb.bb_instructions`,`ao`,
          `pvar`, `fuel`,`ctx`,`s2`,`v2`]
          m2v_step_preserves_pvar_is_some) >> simp[])
QED

Finalise m2v_pvars_set_after_dispatch


(* MSTORE delegates to exec_write2, which can return only OK or Error. *)
Theorem step_inst_base_mstore_no_abort:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    inst.inst_opcode = MSTORE ==>
    F
Proof
  rpt strip_tac >>
  gvs[step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED

(* Abort simulation for non-terminal non-INVOKE instructions.
   Both sides run the same instruction (rewrite is identity for aborters),
   abort states are halt/revert of input, m2v_inv_noix preserved. *)
(* If step_inst_base aborts for non-term, the inst is not in
   {MSTORE,MLOAD,RETURN}, so FIND over promo_list returns NONE *)
Theorem abort_rewrite_identity:
  !fn inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode /\
    MEM inst (fn_insts fn) ==>
    HD (m2v_rewrite_inst fn inst) = inst
Proof
  rpt strip_tac >>
  simp[m2v_rewrite_inst_def] >>
  Cases_on `FIND (\(ao,_,_). MEM (Var ao) inst.inst_operands)
                 (m2v_promo_list fn)` >> simp[] >>
  rename1 `SOME entry` >> PairCases_on `entry` >>
  drule_all promo_find_inst_opcode >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  gvs[]
  >- (strip_tac >> drule step_inst_base_mstore_no_abort >> simp[])
  >> step_base_result_tac
QED

(* Operand agreement for non-fresh operands — extracted common pattern *)
Theorem m2v_inv_noix_operand_agreement:
  !fn inst s1 s2.
    m2v_inv_noix fn s1 s2 /\
    m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) ==>
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2)
Proof
  rpt strip_tac >>
  gvs[m2v_inv_noix_def] >>
  first_x_assum irule >>
  CCONTR_TAC >> gvs[m2v_fresh_names_disjoint_def]
QED

(* Abort sim: non-term non-INVOKE instructions abort identically on both sides *)
Theorem m2v_nonterminal_abort_sim:
  !fn inst s1 s2 a s1' fuel ctx.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s1 = Abort a s1' /\
    m2v_inv_noix fn s1 s2 /\
    MEM inst (fn_insts fn) /\
    m2v_fresh_names_disjoint fn ==>
    ?s2'. step_inst fuel ctx (HD (m2v_rewrite_inst fn inst)) s2 = Abort a s2' /\
          m2v_inv_noix fn s1' s2'
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  drule_all abort_rewrite_identity >>
  disch_then (fn th => simp[th]) >>
  simp[step_inst_non_invoke] >>
  suspend "body"
QED

Resume m2v_nonterminal_abort_sim[body]:
  (* Get operand agreement *)
  mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`]
    m2v_inv_noix_operand_agreement) >>
  simp[] >>
  strip_tac >>
  (* Get s2 abort *)
  SUBGOAL_THEN ``?s2'. step_inst_base inst s2 = Abort a s2'``
    strip_assume_tac
  >- (mp_tac (Q.SPECL [`inst`,`s1`,`s2`,`a`,`s1'`]
        step_inst_base_abort_input_equiv) >>
      simp[] >> gvs[m2v_inv_noix_def])
  >>
  (* Characterize abort state forms, conclude via abort_state *)
  qexists `s2'` >> simp[] >>
  imp_res_tac step_inst_base_abort_form >> gvs[] >>
  metis_tac[m2v_inv_noix_abort_state]
QED

Finalise m2v_nonterminal_abort_sim



Theorem m2v_fresh_undef_update_idx:
  !fn s k. m2v_fresh_undef fn s ==>
    m2v_fresh_undef fn (s with vs_inst_idx := k)
Proof
  simp[m2v_fresh_undef_def, lookup_var_def]
QED

(*  vs_alloca_next preservation helpers *)

(* MAX a L1 = MAX a L2 /\ a <= c ==> MAX c L1 = MAX c L2.
   Used when alloca_next grows but memory is unchanged. *)
Theorem max_eq_mono:
  !a c L1 L2. MAX a L1 = MAX a L2 /\ a <= c ==>
    MAX c L1 = MAX c L2
Proof simp[arithmeticTheory.MAX_DEF] >> rpt (COND_CASES_TAC >> gvs[])
QED

(* For ops that don't change memory on either side, alloca_next may change.
   Requires alloca_next grows monotonically (a <= c) and agrees on both. *)
Theorem nao_preserved_mem_unchanged:
  !s1 s2 s1' s2'.
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1'.vs_alloca_next = s2'.vs_alloca_next ==>
    s1'.vs_alloca_next = s2'.vs_alloca_next
Proof simp[]
QED

(* For ops that don't change memory or alloca_next on either side *)
Theorem nao_preserved_no_mem_change:
  !s1 s2 s1' s2'.
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1'.vs_memory = s1.vs_memory /\ s2'.vs_memory = s2.vs_memory /\
    s1'.vs_alloca_next = s1.vs_alloca_next /\
    s2'.vs_alloca_next = s2.vs_alloca_next ==>
    s1'.vs_alloca_next = s2'.vs_alloca_next
Proof simp[]
QED

(* For ops where both sides expand memory by the same amount D:
   LENGTH s1'.vs_memory = MAX (LENGTH s1.vs_memory) D, same for s2.
   Then vs_alloca_next is preserved by MAX-associativity. *)
Theorem nao_preserved_same_expansion:
  !s1 s2 s1' s2'.
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1'.vs_alloca_next = s1.vs_alloca_next /\
    s2'.vs_alloca_next = s2.vs_alloca_next ==>
    s1'.vs_alloca_next = s2'.vs_alloca_next
Proof simp[]
QED

(* step_inst preserves memory for any opcode when Eff_MEMORY not in write_effects.
   Unifies alloca and non-alloca cases. *)
Theorem step_inst_mem_preserved:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode /\
    Eff_RETURNDATA NOTIN write_effects inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    s'.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- metis_tac[step_inst_alloca_preserves_memory]
  >> metis_tac[cj 13 step_inst_preserves_all]
QED

(* HD(m2v_promote_inst) inherits Eff_MEMORY exclusion for non-terminators *)
Theorem m2v_promote_inst_no_mem_eff:
  !pvar ao sz inst.
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode /\
    Eff_RETURNDATA NOTIN write_effects inst.inst_opcode /\
    ~is_terminator inst.inst_opcode ==>
    Eff_MEMORY NOTIN write_effects
      (HD (m2v_promote_inst pvar ao sz inst)).inst_opcode
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = MSTORE`
  >- gvs[write_effects_def]
  >>
  Cases_on `inst.inst_opcode = RETURN`
  >- gvs[is_terminator_def]
  >>
  simp[m2v_promote_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  every_case_tac >> gvs[] >>
  simp[write_effects_def, empty_effects_def]
QED

(* HD(m2v_promote_inst) preserves safety predicates from original inst *)
Theorem m2v_promote_inst_hd_safe:
  !pvar ao sz inst.
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    ~is_terminator (HD (m2v_promote_inst pvar ao sz inst)).inst_opcode /\
    ~is_ext_call_op (HD (m2v_promote_inst pvar ao sz inst)).inst_opcode /\
    ~is_alloca_op (HD (m2v_promote_inst pvar ao sz inst)).inst_opcode /\
    (HD (m2v_promote_inst pvar ao sz inst)).inst_opcode <> INVOKE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = RETURN`
  >- gvs[is_terminator_def]
  >>
  simp[m2v_promote_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  every_case_tac >> gvs[] >>
  simp[is_terminator_def, is_ext_call_op_def, is_alloca_op_def]
QED



(* When extract_venom_result is called with the same args on two states,
   both produce the same wmwe expansion D.
   This is the key lemma for showing nao equality across ext_call. *)
Triviality extract_venom_result_same_D:
  !s1 s2 ov retOff retSize rr out1 s1' out2 s2'.
    extract_venom_result s1 ov retOff retSize rr = SOME (out1, s1') /\
    extract_venom_result s2 ov retOff retSize rr = SOME (out2, s2') ==>
    s1'.vs_alloca_next = s1.vs_alloca_next /\
    s2'.vs_alloca_next = s2.vs_alloca_next /\
    ?D. LENGTH s1'.vs_memory = MAX (LENGTH s1.vs_memory) D /\
        LENGTH s2'.vs_memory = MAX (LENGTH s2.vs_memory) D
Proof
  simp[extract_venom_result_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[LENGTH_write_memory_with_expansion] >>
  metis_tac[]
QED

(* extract_venom_result preserves alloca_next and has predictable memory length *)
Triviality extract_venom_result_nao:
  !s output_val retOff retSize run_result out s'.
    extract_venom_result s output_val retOff retSize run_result =
      SOME (out, s') ==>
    s'.vs_alloca_next = s.vs_alloca_next /\
    ?D. LENGTH s'.vs_memory = MAX (LENGTH s.vs_memory) D
Proof
  simp[extract_venom_result_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  simp[LENGTH_write_memory_with_expansion] >>
  metis_tac[]
QED

(* exec_ext_call preserves alloca_next and memory length = MAX old D *)
Triviality exec_ext_call_nao:
  !inst s gas addr value ao as_ ro rs st s'.
    exec_ext_call inst s gas addr value ao as_ ro rs st = OK s' ==>
    s'.vs_alloca_next = s.vs_alloca_next /\
    ?D. LENGTH s'.vs_memory = MAX (LENGTH s.vs_memory) D
Proof
  simp[exec_ext_call_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[extract_venom_result_nao]
QED

(* exec_delegatecall preserves alloca_next and memory length = MAX old D *)
Triviality exec_delegatecall_nao:
  !inst s gas addr ao as_ ro rs s'.
    exec_delegatecall inst s gas addr ao as_ ro rs = OK s' ==>
    s'.vs_alloca_next = s.vs_alloca_next /\
    ?D. LENGTH s'.vs_memory = MAX (LENGTH s.vs_memory) D
Proof
  simp[exec_delegatecall_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[extract_venom_result_nao]
QED

(* exec_create preserves alloca_next and memory length = MAX old D *)
Triviality exec_create_nao:
  !inst s value offset sz salt_opt s'.
    exec_create inst s value offset sz salt_opt = OK s' ==>
    s'.vs_alloca_next = s.vs_alloca_next /\
    ?D. LENGTH s'.vs_memory = MAX (LENGTH s.vs_memory) D
Proof
  simp[exec_create_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[extract_venom_result_nao]
QED

(* Same-D variants: when two states agree on all fields that affect the
   callee construction, exec_* produces the same wmwe expansion D. *)
Triviality exec_ext_call_same_D:
  !inst s1 s2 g a v ao as_ ro rs st s1' s2'.
    exec_ext_call inst s1 g a v ao as_ ro rs st = OK s1' /\
    exec_ext_call inst s2 g a v ao as_ ro rs st = OK s2' /\
    read_memory (w2n ao) (w2n as_) s1 = read_memory (w2n ao) (w2n as_) s2 /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_transient = s2.vs_transient /\
    venom_to_tx_params s1 = venom_to_tx_params s2 ==>
    s1'.vs_alloca_next = s1.vs_alloca_next /\
    s2'.vs_alloca_next = s2.vs_alloca_next /\
    ?D. LENGTH s1'.vs_memory = MAX (LENGTH s1.vs_memory) D /\
        LENGTH s2'.vs_memory = MAX (LENGTH s2.vs_memory) D
Proof
  simp[exec_ext_call_def, LET_THM, AllCaseEqs(),
       make_venom_call_state_def] >>
  rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[extract_venom_result_same_D]
QED

Triviality exec_delegatecall_same_D:
  !inst s1 s2 g a ao as_ ro rs s1' s2'.
    exec_delegatecall inst s1 g a ao as_ ro rs = OK s1' /\
    exec_delegatecall inst s2 g a ao as_ ro rs = OK s2' /\
    read_memory (w2n ao) (w2n as_) s1 = read_memory (w2n ao) (w2n as_) s2 /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_transient = s2.vs_transient /\
    venom_to_tx_params s1 = venom_to_tx_params s2 ==>
    s1'.vs_alloca_next = s1.vs_alloca_next /\
    s2'.vs_alloca_next = s2.vs_alloca_next /\
    ?D. LENGTH s1'.vs_memory = MAX (LENGTH s1.vs_memory) D /\
        LENGTH s2'.vs_memory = MAX (LENGTH s2.vs_memory) D
Proof
  simp[exec_delegatecall_def, LET_THM, AllCaseEqs(),
       make_venom_delegatecall_state_def] >>
  rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[extract_venom_result_same_D]
QED

Triviality exec_create_same_D:
  !inst s1 s2 v off sz salt s1' s2'.
    exec_create inst s1 v off sz salt = OK s1' /\
    exec_create inst s2 v off sz salt = OK s2' /\
    read_memory (w2n off) (w2n sz) s1 = read_memory (w2n off) (w2n sz) s2 /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_transient = s2.vs_transient /\
    venom_to_tx_params s1 = venom_to_tx_params s2 ==>
    s1'.vs_alloca_next = s1.vs_alloca_next /\
    s2'.vs_alloca_next = s2.vs_alloca_next /\
    ?D. LENGTH s1'.vs_memory = MAX (LENGTH s1.vs_memory) D /\
        LENGTH s2'.vs_memory = MAX (LENGTH s2.vs_memory) D
Proof
  simp[exec_create_def, LET_THM, AllCaseEqs(),
       make_venom_create_state_def] >>
  rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[extract_venom_result_same_D]
QED

(* For ext_call ops with FIND=NONE and same callee input: nao preserved.
   Both sides have the same operands and same make_venom_*_state, so run
   produces the same result, and wmwe expansion D is the same. *)
Theorem step_inst_ext_call_nao:
  !inst s1 s2 s1' s2' fn bb.
    is_ext_call_op inst.inst_opcode /\
    step_inst_base inst s1 = OK s1' /\
    step_inst_base inst s2 = OK s2' /\
    m2v_inv_noix fn s1 s2 /\
    m2v_nonpromoted_access_safe fn s1 /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    FIND (\(ao,_0,_1). MEM (Var ao) inst.inst_operands)
         (m2v_promo_list fn) = NONE /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) ==>
    s1'.vs_alloca_next = s2'.vs_alloca_next
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def]) >>
  `inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def]) >>
  qspecl_then [`inst`, `s1`, `s1'`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_alloca_next >>
  simp[] >> strip_tac >>
  qspecl_then [`inst`, `s2`, `s2'`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_alloca_next >>
  simp[]
QED

(* Standalone nao preservation theorem *)
Theorem nao_dispatch_preserved:
  !fn bb idx fuel ctx s1 s2 s1' s2'.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    m2v_promotable_wf fn /\ m2v_fresh_names_disjoint fn /\
    m2v_promo_sizes_bounded fn /\ alloca_pointer_confined fn /\
    alloca_inv s1 /\
    m2v_nonpromoted_access_safe fn s1 /\
    MEM bb fn.fn_blocks /\ bb_well_formed bb /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions - 1 /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    m2v_inv_noix fn s1 s2 /\ m2v_inv_noix fn s1' s2' /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s1 = OK s1' /\
    step_inst fuel ctx (HD (m2v_rewrite_inst fn
        (EL idx bb.bb_instructions))) s2 = OK s2' ==>
    s1'.vs_alloca_next = s2'.vs_alloca_next
Proof
  rpt strip_tac >>
  `MEM (EL idx bb.bb_instructions) bb.bb_instructions` by
    (irule EL_MEM >> simp[]) >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst.inst_opcode <> INVOKE` by
    (gvs[EVERY_MEM] >> res_tac) >>
  gvs[m2v_inv_noix_def]
QED

(* nao_dispatch_preserved is now trivial (vs_alloca_next from m2v_inv_noix).
   Old Resume blocks removed — they handled next_alloca_offset MAX cases. *)


(* m2v_inv_noix + inst_idx agreement = m2v_inv *)
Theorem m2v_inv_noix_to_inv:
  !fn s1 s2.
    m2v_inv_noix fn s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    m2v_inv fn s1 s2
Proof
  rw[m2v_inv_noix_def, m2v_inv_def, m2v_equiv_def,
     in_promoted_region_def, mem_byte_def, mload_def]
QED

(* m2v_inv_noix implies m2v_equiv (just weaken: drop memory/sync/extra) *)
Theorem m2v_inv_noix_implies_equiv:
  !fn s1 s2.
    m2v_inv_noix fn s1 s2 ==>
    m2v_equiv (m2v_fresh_vars fn) s1 s2
Proof
  rw[m2v_inv_noix_def, m2v_equiv_def]
QED

(* Bridge: per_block_sim_at (all m2v_inv_noix) →
   lift_result m2v_inv m2v_equiv m2v_equiv.
   OK case: add inst_idx agreement to get m2v_inv.
   Halt/Abort: weaken m2v_inv_noix to m2v_equiv. *)
(* Bridge: combined_R (m2v_inv_noix /\ m2v_non32_ok /\ ao_undef_sync) →
   OK: m2v_inv /\ m2v_non32_ok /\ ao_undef_sync, Halt/Abort: m2v_equiv *)
Theorem lift_result_bridge:
  !fn r1 r2.
    lift_result (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
                (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
                (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
                r1 r2 /\
    (!s1 s2. r1 = OK s1 /\ r2 = OK s2 ==>
             s1.vs_inst_idx = s2.vs_inst_idx) ==>
    lift_result (\s1 s2. m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
                (m2v_equiv (m2v_fresh_vars fn))
                (m2v_equiv (m2v_fresh_vars fn)) r1 r2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >>
  gvs[lift_result_def] >>
  metis_tac[m2v_inv_noix_to_inv, m2v_inv_noix_implies_equiv]
QED


(* Combined easy terminator: 4-conjunct lift_result including nao.
   Avoids expensive 5x5 case split in caller. *)
Theorem step_inst_result_preserves_alloca_next:
  !fuel ctx inst s s'.
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
    (step_inst fuel ctx inst s = OK s' \/
     step_inst fuel ctx inst s = Halt s' \/
     (?a. step_inst fuel ctx inst s = Abort a s') \/
     (?vs. step_inst fuel ctx inst s = IntRet vs s')) ==>
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  qspecl_then [`inst`, `s`, `s'`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_alloca_next >>
  simp[]
QED

Theorem m2v_step_easy_terminator_full:
  !fn inst s1 s2 fuel ctx.
    m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    m2v_fresh_names_disjoint fn /\
    MEM inst (fn_insts fn) /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> RETURN /\
    inst.inst_opcode <> REVERT /\
    inst.inst_opcode <> DRET /\
    inst.inst_opcode <> RETFMP ==>
    lift_result (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
                (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
                (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`,`fuel`,`ctx`]
    m2v_step_easy_terminator) >> simp[] >> strip_tac >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[lift_result_def]
  >- (mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`,`fuel`,`ctx`]
        nao_easy_terminator) >> simp[]) >>
  metis_tac[step_inst_result_preserves_alloca_next]
QED

(* nao preserved through mstore on s2 followed by halt_state + set_returndata.
   Factors out the nao reasoning that was timing out inline in lift_impl. *)
Theorem nao_return_promoted:
  !fn s1 s2 ao pvar addr_val pval rd.
    m2v_inv_noix fn s1 s2 /\
    alloca_inv s1 /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    MEM (ao,pvar,32) (m2v_promo_list fn) /\
    lookup_var ao s1 = SOME addr_val ==>
    (halt_state (set_returndata rd s1)).vs_alloca_next =
    (halt_state (set_returndata rd (mstore (w2n addr_val) pval s2))).vs_alloca_next
Proof
  rpt strip_tac >>
  simp[nao_halt_revert, mstore_preserves,
       LENGTH_mstore_eq] >>
  `s1.vs_alloca_next = s2.vs_alloca_next` by gvs[m2v_inv_noix_def] >>
  `?ainst. MEM ainst (fn_insts fn) /\ ainst.inst_opcode = ALLOCA /\
           ainst.inst_outputs = [ao]` by metis_tac[m2v_promo_list_is_alloca] >>
  `FLOOKUP s1.vs_allocas ainst.inst_id = SOME (w2n addr_val, 32)` by (
    qpat_x_assum `m2v_inv_noix _ _ _`
      (strip_assume_tac o REWRITE_RULE [m2v_inv_noix_def]) >>
    first_x_assum (qspecl_then [`ao`,`pvar`,`32`,`ainst`] mp_tac) >>
    simp[]) >>
  `w2n addr_val + 32 <= s1.vs_alloca_next` by (
    gvs[alloca_inv_def, alloca_next_valid_def] >> res_tac) >>
  simp[arithmeticTheory.MAX_DEF]
QED

val _ = export_theory();

