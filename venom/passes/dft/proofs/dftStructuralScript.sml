(*
 * DFT Structural Properties
 *
 * Key result: dft_block output non-pseudos are (modulo flip_operands)
 * non-pseudo instructions from the input block.
 *)

Theory dftStructural
Ancestors
  dftDefs venomExecSemantics venomEffects passSharedDefs venomInst fcgDefs

(* ===== flip_operands basic properties ===== *)

Theorem flip_operands_inst_id[simp]:
  !i. (flip_operands i).inst_id = i.inst_id
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[]
QED

Theorem flip_operands_inst_outputs[simp]:
  !i. (flip_operands i).inst_outputs = i.inst_outputs
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[]
QED

(* Flipping operands does not change pseudo-ness of the opcode *)
Theorem flip_operands_is_pseudo:
  !i. is_pseudo (flip_operands i).inst_opcode = is_pseudo i.inst_opcode
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[] >>
  Cases_on `i.inst_opcode` >>
  fs[is_comparator_def, flip_comparison_opcode_def, is_pseudo_def]
QED

(* Flipping operands does not change barrier-ness *)
Theorem flip_operands_is_barrier:
  !i. is_barrier (flip_operands i) = is_barrier i
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[] >>
  Cases_on `i.inst_opcode` >>
  fs[is_comparator_def, flip_comparison_opcode_def, is_barrier_def,
     is_volatile_def, is_alloca_op_def, is_raw_fmp_opcode_def]
QED

(* ===== Helper lemmas ===== *)

Triviality producing_inst_mem:
  !insts var inst.
    producing_inst insts var = SOME inst ==> MEM inst insts
Proof
  Induct >> rw[producing_inst_def] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality operand_producer_mem:
  !block_insts op inst.
    operand_producer block_insts op = SOME inst ==> MEM inst block_insts
Proof
  Cases_on `op` >> rw[operand_producer_def] >>
  metis_tac[producing_inst_mem]
QED

Definition eda_wf_def:
  eda_wf eda block_insts <=>
    !id deps dep. FLOOKUP eda id = SOME deps /\ MEM dep deps ==>
                  MEM dep block_insts /\ ~is_pseudo dep.inst_opcode
End

(* Updating an EDA entry preserves eda_wf if every new dep is valid *)
Theorem eda_wf_update:
  !eda block_insts id new_deps.
    eda_wf eda block_insts /\
    EVERY (\d. MEM d block_insts /\ ~is_pseudo d.inst_opcode) new_deps ==>
    eda_wf (eda |+ (id, new_deps)) block_insts
Proof
  rw[eda_wf_def] >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[listTheory.EVERY_MEM] >>
  metis_tac[]
QED

(* Every dependency of an instruction lies in block_insts ( precondition: eda_wf) *)
Theorem inst_all_deps_mem:
  !block_insts order eda inst dep.
    eda_wf eda block_insts ==>
    MEM dep (inst_all_deps block_insts order eda inst) ==>
    MEM dep block_insts
Proof
  rw[inst_all_deps_def, inst_data_deps_def, eda_wf_def, LET_THM] >>
  fs[listTheory.MEM_nub, listTheory.MEM_APPEND,
     listTheory.MEM_MAP, listTheory.MEM_FILTER,
     optionTheory.IS_SOME_EXISTS] >> gvs[]
  >- metis_tac[operand_producer_mem, optionTheory.THE_DEF]
  >- metis_tac[producing_inst_mem, optionTheory.THE_DEF]
  >- (Cases_on `FLOOKUP eda inst.inst_id` >> gvs[] >> metis_tac[])
  >- metis_tac[operand_producer_mem, optionTheory.THE_DEF]
  >> Cases_on `FLOOKUP eda inst.inst_id` >> gvs[] >> metis_tac[]
QED

Triviality qsort_mem_eq:
  !R l x. MEM x (QSORT R l) <=> MEM x l
Proof
  rpt gen_tac >>
  `PERM l (QSORT R l)` by simp[sortingTheory.QSORT_PERM] >>
  metis_tac[sortingTheory.PERM_MEM_EQ]
QED

(* sort_children is a permutation of its input children *)
Theorem sort_children_mem:
  !block_insts order eda offspring_map parent children x.
    MEM x (sort_children block_insts order eda offspring_map parent children)
    <=> MEM x children
Proof
  rw[sort_children_def, LET_THM, listTheory.MEM_MAP,
     qsort_mem_eq, indexedListsTheory.MEM_MAPi] >>
  eq_tac >> strip_tac
  >- (Cases_on `y` >> gvs[] >> metis_tac[listTheory.MEM_EL])
  >> fs[listTheory.MEM_EL] >>
  qexists_tac `(n, x)` >> simp[]
QED

(* ===== "from_block": instruction is from block_insts modulo flip ===== *)

Definition from_block_def:
  from_block block_insts i <=>
    ?j. MEM j block_insts /\ ~is_pseudo j.inst_opcode /\
        (i = j \/ (i = flip_operands j /\ is_flippable j.inst_opcode))
End

(* flip_operands is an involution *)
Theorem flip_operands_involution:
  !i. flip_operands (flip_operands i) = i
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  Cases_on `is_comparator i.inst_opcode` >> simp[LET_THM] >>
  TRY (simp[instruction_component_equality] >> NO_TAC) >>
  Cases_on `is_comparator (flip_comparison_opcode i.inst_opcode)` >>
  simp[LET_THM, instruction_component_equality] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def]
QED

(* from_block is transitive: if every non-pseudo in L1 satisfies from_block L0,
   and from_block L1 i, then from_block L0 i *)
Theorem from_block_trans:
  !L0 L1 i.
    from_block L1 i /\
    (!j. MEM j L1 /\ ~is_pseudo j.inst_opcode ==> from_block L0 j) ==>
    from_block L0 i
Proof
  rw[from_block_def] >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexists_tac `j'` >> simp[] >>
  metis_tac[flip_operands_involution]
QED

(* ===== DFS output subset property ===== *)

(* Key insight: every instruction emitted by the DFS is a non-pseudo
   instruction from block_insts (possibly with flipped operands). *)

(* Proven via a FUNPOW invariant: every stack item and output element
   satisfies from_block and ~is_pseudo. *)

(* Invariant for DFS FUNPOW proof *)
Definition dfs_good_state_def:
  dfs_good_state block_insts st <=>
    EVERY (\item. case item of
      | DfsEmit i => from_block block_insts i /\ ~is_pseudo i.inst_opcode
      | DfsProcess i => MEM i block_insts) st.ds_stack /\
    EVERY (\i. from_block block_insts i /\ ~is_pseudo i.inst_opcode) st.ds_output
End

(* dfs_step preserves good_state *)
Theorem dfs_step_preserves_good:
  !block_insts order eda offspring_map do_flip st.
    eda_wf eda block_insts ==>
    dfs_good_state block_insts st ==>
    dfs_good_state block_insts
      (dfs_step block_insts order eda offspring_map do_flip st)
Proof
  simp[dfs_good_state_def] >> rpt strip_tac >>
  simp[Once dfs_step_def] >>
  Cases_on `st.ds_stack` >> gvs[] >>
  Cases_on `h` >> gvs[listTheory.EVERY_DEF, listTheory.EVERY_APPEND]
  >> rename1 `DfsProcess inst` >>
  IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  simp[LET_THM, listTheory.EVERY_APPEND, listTheory.EVERY_MAP,
       listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  TRY (fs[sort_children_mem] >> metis_tac[inst_all_deps_mem]) >>
  TRY (simp[from_block_def] >>
       BasicProvers.every_case_tac >> simp[] >> metis_tac[]) >>
  TRY (BasicProvers.every_case_tac >> simp[flip_operands_is_pseudo]) >>
  gvs[listTheory.EVERY_MEM, flip_operands_is_pseudo]
QED

(* FUNPOW preserves good_state *)
Theorem dfs_funpow_preserves_good:
  !n block_insts order eda offspring_map do_flip st.
    eda_wf eda block_insts ==>
    dfs_good_state block_insts st ==>
    dfs_good_state block_insts
      (FUNPOW (dfs_step block_insts order eda offspring_map do_flip) n st)
Proof
  Induct >> simp[arithmeticTheory.FUNPOW_0] >>
  rpt strip_tac >> simp[arithmeticTheory.FUNPOW_SUC] >>
  irule dfs_step_preserves_good >> simp[]
QED

(* Initial state is good *)
Theorem init_dfs_state_good:
  !entries block_insts.
    EVERY (\i. MEM i block_insts) entries ==>
    dfs_good_state block_insts
      <| ds_stack := MAP DfsProcess entries;
         ds_output := []; ds_visited := [] |>
Proof
  rw[dfs_good_state_def, listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> gvs[listTheory.MEM_MAP]
QED

(* Every instruction output by schedule_from_entries is a non-pseudo instruction
   from block_insts (possibly with flipped operands), given well-formed EDA
   and entries all drawn from block_insts *)
Theorem schedule_output_from_block:
  !block_insts order eda offspring_map entries i.
    eda_wf eda block_insts ==>
    EVERY (\i. MEM i block_insts) entries ==>
    MEM i (schedule_from_entries block_insts order eda offspring_map entries) ==>
    from_block block_insts i /\ ~is_pseudo i.inst_opcode
Proof
  rw[schedule_from_entries_def, LET_THM] >>
  `dfs_good_state block_insts
     (FUNPOW (dfs_step block_insts order eda offspring_map T)
        ((LENGTH block_insts + 1) * (LENGTH block_insts + 1))
        <| ds_stack := MAP DfsProcess entries;
           ds_output := []; ds_visited := [] |>)` by
    (irule dfs_funpow_preserves_good >> simp[] >>
     irule init_dfs_state_good >> simp[]) >>
  gvs[dfs_good_state_def, listTheory.EVERY_MEM]
QED

(* ===== build_eda produces well-formed EDA ===== *)

(* Effect tracking well-formedness: all stored instructions are from block
   and non-pseudo (build_eda only processes non-pseudo instructions) *)
Definition et_wf_def:
  et_wf et block_insts <=>
    (!eff w. FLOOKUP et.et_last_write eff = SOME w ==>
             MEM w block_insts /\ ~is_pseudo w.inst_opcode) /\
    (!eff rs r. FLOOKUP et.et_all_reads eff = SOME rs /\ MEM r rs ==>
                MEM r block_insts /\ ~is_pseudo r.inst_opcode)
End

(* Helper: second FOLDL (reads) preserves et_last_write *)
Theorem read_foldl_last_write:
  !effs acc inst.
    (FOLDL (\acc reff.
       acc with et_all_reads :=
         acc.et_all_reads |+ (reff, et_get_reads acc reff ++ [inst]))
       acc effs).et_last_write = acc.et_last_write
Proof
  Induct >> simp[]
QED

(* Helper: write FOLDL stores inst in last_write, everything else from et *)
Theorem write_foldl_last_write:
  !effs et inst eff w.
    FLOOKUP (FOLDL (\acc weff.
       <| et_last_write := acc.et_last_write |+ (weff, inst);
          et_all_reads := acc.et_all_reads |+ (weff, []) |>)
       et effs).et_last_write eff = SOME w ==>
    w = inst \/ FLOOKUP et.et_last_write eff = SOME w
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then
    [`<| et_last_write := et.et_last_write |+ (h, inst);
         et_all_reads := et.et_all_reads |+ (h, []) |>`,
     `inst`, `eff`, `w`] mp_tac) >>
  simp[] >> strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Helper: write FOLDL clears reads *)
Theorem write_foldl_all_reads:
  !effs et inst eff rs.
    FLOOKUP (FOLDL (\acc weff.
       <| et_last_write := acc.et_last_write |+ (weff, inst);
          et_all_reads := acc.et_all_reads |+ (weff, []) |>)
       et effs).et_all_reads eff = SOME rs ==>
    rs = [] \/ FLOOKUP et.et_all_reads eff = SOME rs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then
    [`<| et_last_write := et.et_last_write |+ (h, inst);
         et_all_reads := et.et_all_reads |+ (h, []) |>`,
     `inst`, `eff`, `rs`] mp_tac) >>
  simp[] >> strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Helper: read FOLDL stores inst in reads, rest from input *)
Theorem read_foldl_all_reads:
  !effs acc inst eff rs r.
    FLOOKUP (FOLDL (\acc reff.
       acc with et_all_reads :=
         acc.et_all_reads |+ (reff, et_get_reads acc reff ++ [inst]))
       acc effs).et_all_reads eff = SOME rs /\ MEM r rs ==>
    r = inst \/ (?rs0. FLOOKUP acc.et_all_reads eff = SOME rs0 /\ MEM r rs0)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then
    [`acc with et_all_reads :=
        acc.et_all_reads |+ (h, et_get_reads acc h ++ [inst])`,
     `inst`, `eff`, `rs`, `r`] mp_tac) >>
  simp[] >> strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE, et_get_reads_def] >>
  BasicProvers.every_case_tac >> gvs[listTheory.MEM_APPEND]
QED

(* compute_effect_deps: deps come from et, and et' stores inst.
   Non-pseudo: deps from et are non-pseudo (et_wf), et' stores inst (non-pseudo). *)
Theorem compute_effect_deps_wf:
  !et inst deps et' block_insts.
    compute_effect_deps et inst = (deps, et') /\
    et_wf et block_insts /\
    MEM inst block_insts /\ ~is_pseudo inst.inst_opcode ==>
    (!d. MEM d deps ==> MEM d block_insts /\ ~is_pseudo d.inst_opcode) /\
    et_wf et' block_insts
Proof
  rpt gen_tac \\ strip_tac \\
  fs[compute_effect_deps_def, LET_THM] \\
  rpt (pairarg_tac \\ fs[]) \\
  fs[et_wf_def] \\
  conj_tac
  >- (rpt strip_tac \\
      gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP, listTheory.MEM_nub,
          listTheory.MEM_APPEND, et_get_reads_def,
          listTheory.MEM_FILTER, optionTheory.IS_SOME_EXISTS] \\
      BasicProvers.every_case_tac \\ gvs[] \\ metis_tac[])
  \\ rpt strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
  \\ fs[read_foldl_last_write]
  \\ TRY (drule write_foldl_last_write \\ strip_tac \\ gvs[] \\ metis_tac[])
  \\ drule_all read_foldl_all_reads \\ strip_tac \\ gvs[]
  \\ TRY (metis_tac[])
  \\ drule_all write_foldl_all_reads \\ strip_tac \\ gvs[] \\ metis_tac[]
QED

Triviality build_eda_foldl_inv:
  !non_phis block_insts acc et.
    et_wf et block_insts /\
    (!id deps dep. FLOOKUP acc id = SOME deps /\ MEM dep deps ==>
                   MEM dep block_insts /\ ~is_pseudo dep.inst_opcode) /\
    EVERY (\i. MEM i block_insts /\ ~is_pseudo i.inst_opcode) non_phis ==>
    !id deps dep.
      FLOOKUP (FST (FOLDL (\(acc_map, et) inst.
        (\(deps, et'). (acc_map |+ (inst.inst_id, deps), et'))
          (compute_effect_deps et inst))
        (acc, et) non_phis)) id = SOME deps /\ MEM dep deps ==>
      MEM dep block_insts /\ ~is_pseudo dep.inst_opcode
Proof
  Induct
  >- (simp[] >> metis_tac[])
  >> rpt gen_tac >> strip_tac
  >> fs[listTheory.EVERY_DEF]
  >> Cases_on `compute_effect_deps et h`
  >> rename1 `compute_effect_deps et h = (nd, ne)`
  >> `(!d. MEM d nd ==> MEM d block_insts /\ ~is_pseudo d.inst_opcode) /\
      et_wf ne block_insts` by
       (irule compute_effect_deps_wf >> qexistsl [`et`, `h`] >> simp[])
  >> first_x_assum (qspecl_then [`block_insts`, `acc |+ (h.inst_id, nd)`, `ne`] mp_tac)
  >> impl_tac
  >- (rpt strip_tac
      >- simp[]
      >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
      >> BasicProvers.every_case_tac >> gvs[] >> metis_tac[])
  >> simp[]
QED

(* build_eda produces a well-formed EDA: every dependency is a non-pseudo
   instruction from block_insts *)
Theorem build_eda_wf:
  !block_insts. eda_wf (build_eda block_insts) block_insts
Proof
  simp[eda_wf_def, build_eda_def, LET_THM] >>
  gen_tac >>
  mp_tac (Q.SPECL [`FILTER (\ i. ~is_pseudo i.inst_opcode) block_insts`,
                    `block_insts`, `FEMPTY`, `empty_effect_track`]
          build_eda_foldl_inv) >>
  impl_tac
  >- simp[et_wf_def, empty_effect_track_def, finite_mapTheory.FLOOKUP_DEF,
          listTheory.EVERY_FILTER, listTheory.EVERY_MEM]
  >> metis_tac[]
QED

(* ===== add_chain_deps preserves eda_wf ===== *)

Triviality add_chain_deps_foldl_wf:
  !matching block_insts acc prev.
    eda_wf acc block_insts /\
    EVERY (\i. MEM i block_insts /\ ~is_pseudo i.inst_opcode) matching /\
    (!p. prev = SOME p ==>
         MEM p block_insts /\ ~is_pseudo p.inst_opcode) ==>
    eda_wf (FST (FOLDL (\(acc, prev) inst.
      let old_deps = case FLOOKUP acc inst.inst_id of
                       NONE => [] | SOME ds => ds in
      let new_deps = case prev of
                       NONE => old_deps
                     | SOME p => if MEM p old_deps then old_deps
                                 else p :: old_deps in
      (acc |+ (inst.inst_id, new_deps), SOME inst))
    (acc, prev) matching)) block_insts
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[listTheory.EVERY_DEF] >>
  first_x_assum irule >> simp[] >>
  simp[eda_wf_def] >> rpt strip_tac >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `h.inst_id = id` >> gvs[] >>
  Cases_on `prev` >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[eda_wf_def] >>
  metis_tac[]
QED

Theorem add_chain_deps_wf:
  !P block_insts eda.
    eda_wf eda block_insts ==>
    eda_wf (add_chain_deps P block_insts eda) block_insts
Proof
  rw[add_chain_deps_def, LET_THM] >>
  irule (SRULE [LET_THM] add_chain_deps_foldl_wf) >>
  simp[listTheory.EVERY_FILTER, listTheory.EVERY_MEM,
       listTheory.MEM_FILTER]
QED

(* ===== add_barrier_deps preserves eda_wf ===== *)

(* Helper: membership in FOLDL that adds list elements *)
Triviality foldl_add_mem:
  !prev init x.
    MEM x (FOLDL (\ds (p:instruction). if MEM p ds then ds else p :: ds)
             init prev) ==>
    MEM x init \/ MEM x prev
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `MEM h init` >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

(* Pass 1 wf: add_deps_on_barrier only adds last_bar as dep *)
Triviality add_deps_on_barrier_foldl_wf:
  !non_phis block_insts acc last_bar.
    eda_wf acc block_insts /\
    EVERY (\i. MEM i block_insts /\ ~is_pseudo i.inst_opcode) non_phis /\
    (!b. last_bar = SOME b ==>
         MEM b block_insts /\ ~is_pseudo b.inst_opcode) ==>
    eda_wf (FST (FOLDL (\(acc, last_bar) inst.
      let old_deps = case FLOOKUP acc inst.inst_id of
                       NONE => [] | SOME ds => ds in
      if is_barrier inst then
        (acc, SOME inst)
      else
        let new_deps = case last_bar of
                         NONE => old_deps
                       | SOME b => if MEM b old_deps then old_deps
                                   else b :: old_deps in
        (acc |+ (inst.inst_id, new_deps), last_bar))
    (acc, last_bar) non_phis)) block_insts
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[listTheory.EVERY_DEF] >>
  Cases_on `is_barrier h` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  irule eda_wf_update >>
  Cases_on `last_bar` >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[] >>
  simp[listTheory.EVERY_DEF] >>
  gvs[eda_wf_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem add_deps_on_barrier_wf:
  !block_insts eda.
    eda_wf eda block_insts ==>
    eda_wf (add_deps_on_barrier block_insts eda) block_insts
Proof
  rw[add_deps_on_barrier_def] >>
  irule (SRULE [LET_THM] add_deps_on_barrier_foldl_wf) >>
  simp[listTheory.EVERY_FILTER, listTheory.EVERY_MEM,
       listTheory.MEM_FILTER]
QED

(* Pass 2 wf: add_deps_from_barrier adds prev_insts as deps for barriers *)
Triviality add_deps_from_barrier_foldl_wf:
  !non_phis block_insts acc prev_insts.
    eda_wf acc block_insts /\
    EVERY (\i. MEM i block_insts /\ ~is_pseudo i.inst_opcode) non_phis /\
    EVERY (\i. MEM i block_insts /\ ~is_pseudo i.inst_opcode) prev_insts ==>
    eda_wf (FST (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        let old_deps = case FLOOKUP acc inst.inst_id of
                         NONE => [] | SOME ds => ds in
        let new_deps = FOLDL (\ds p.
              if MEM p ds then ds else p :: ds) old_deps prev_insts in
        (acc |+ (inst.inst_id, new_deps), prev_insts ++ [inst])
      else
        (acc, prev_insts ++ [inst]))
    (acc, prev_insts) non_phis)) block_insts
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[listTheory.EVERY_DEF] >>
  Cases_on `is_barrier h` >> gvs[] >>
  first_x_assum irule >>
  simp[listTheory.EVERY_APPEND, listTheory.EVERY_DEF] >>
  irule eda_wf_update >>
  `!x. MEM x (FOLDL (\ds p. if MEM p ds then ds else p :: ds)
         (case FLOOKUP acc h.inst_id of NONE => [] | SOME ds => ds)
         prev_insts) ==>
       MEM x block_insts /\ ~is_pseudo x.inst_opcode` by
    (rpt strip_tac >> drule foldl_add_mem >> strip_tac >> gvs[] >>
     BasicProvers.every_case_tac >> gvs[] >>
     gvs[listTheory.EVERY_MEM] >> metis_tac[eda_wf_def]) >>
  simp[listTheory.EVERY_MEM]
QED

Theorem add_deps_from_barrier_wf:
  !block_insts eda.
    eda_wf eda block_insts ==>
    eda_wf (add_deps_from_barrier block_insts eda) block_insts
Proof
  rw[add_deps_from_barrier_def] >>
  irule (SRULE [LET_THM] add_deps_from_barrier_foldl_wf) >>
  simp[listTheory.EVERY_FILTER, listTheory.EVERY_MEM,
       listTheory.MEM_FILTER]
QED

(* Adding barrier dependencies preserves EDA well-formedness *)
Theorem add_barrier_deps_wf:
  !block_insts eda.
    eda_wf eda block_insts ==>
    eda_wf (add_barrier_deps block_insts eda) block_insts
Proof
  rw[add_barrier_deps_def] >>
  irule add_deps_from_barrier_wf >>
  irule add_deps_on_barrier_wf >> simp[]
QED

(* The full EDA (effect deps + barrier deps + chain deps) is well-formed *)
Theorem build_full_eda_wf:
  !block_insts. eda_wf (build_full_eda block_insts) block_insts
Proof
  rw[build_full_eda_def, add_alloca_deps_def, add_abort_deps_def] >>
  irule add_chain_deps_wf >>
  irule add_barrier_deps_wf >>
  irule add_chain_deps_wf >>
  simp[build_eda_wf]
QED

(* ===== entry_instructions are from block_insts ===== *)

(* Entry instructions are all members of block_insts *)
Theorem entry_instructions_mem:
  !block_insts order eda.
    EVERY (\i. MEM i block_insts) (entry_instructions block_insts order eda)
Proof
  rw[entry_instructions_def, LET_THM, listTheory.EVERY_FILTER,
     listTheory.EVERY_MEM, listTheory.MEM_FILTER]
QED

(* ===== dft_block output non-pseudos are from original block ===== *)

(* Every non-pseudo instruction in dft_block's output is either identical to
   or a flipped version of a non-pseudo instruction from the input block *)
Theorem dft_block_from_orig:
  !order bb i.
    MEM i (FILTER (\i. ~is_pseudo i.inst_opcode)
             (dft_block order bb).bb_instructions) ==>
    from_block bb.bb_instructions i
Proof
  rpt strip_tac >>
  fs[dft_block_def, LET_THM, listTheory.MEM_FILTER, listTheory.MEM_APPEND]
  (* pseudo case: contradicts ~is_pseudo *)
  >- gvs[listTheory.MEM_FILTER]
  (* scheduled case *)
  >> metis_tac[schedule_output_from_block, build_full_eda_wf, entry_instructions_mem]
QED

(* ===== Phis are preserved by dft_block ===== *)

(* Pseudo-instructions (PHIs) are unchanged by dft_block *)
Theorem dft_block_phis:
  !order bb.
    FILTER (\i. is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions
Proof
  rw[dft_block_def, LET_THM, rich_listTheory.FILTER_APPEND] >>
  simp[rich_listTheory.FILTER_FILTER] >>
  `FILTER (\i. is_pseudo i.inst_opcode)
    (schedule_from_entries bb.bb_instructions order
      (build_full_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions order)
      (entry_instructions bb.bb_instructions order
        (build_full_eda bb.bb_instructions))) = []` suffices_by simp[] >>
  simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  metis_tac[schedule_output_from_block, build_full_eda_wf, entry_instructions_mem]
QED



Definition dft_inst_invokes_target_def:
  dft_inst_invokes_target target inst <=>
    inst.inst_opcode = INVOKE /\
    ?rest. inst.inst_operands = Label target :: rest
End

Definition dft_invoke_targets_def:
  dft_invoke_targets blocks =
    MAP FST (get_invoke_targets (fn_insts_blocks blocks))
End

Definition dft_invoke_subset_def:
  dft_invoke_subset before after <=>
    EVERY (\target. MEM target (dft_invoke_targets before))
      (dft_invoke_targets after)
End

Theorem dft_target_mem_insts[local]:
  MEM target (MAP FST (get_invoke_targets insts)) <=>
  EXISTS (dft_inst_invokes_target target) insts
Proof
  Induct_on `insts`
  >- simp[get_invoke_targets_def]
  >> gen_tac >> Cases_on `h.inst_opcode = INVOKE`
  >- (Cases_on `h.inst_operands`
      >- simp[get_invoke_targets_def, dft_inst_invokes_target_def]
      >> Cases_on `h'` >>
         simp[get_invoke_targets_def, dft_inst_invokes_target_def] >>
         metis_tac[])
  >> simp[get_invoke_targets_def, dft_inst_invokes_target_def] >>
     metis_tac[]
QED

Theorem dft_target_mem_blocks[local]:
  MEM target (dft_invoke_targets blocks) <=>
  ?bb. MEM bb blocks /\
       MEM target (MAP FST (get_invoke_targets bb.bb_instructions))
Proof
  simp[dft_invoke_targets_def, dft_target_mem_insts] >>
  eq_tac >> strip_tac
  >- (gvs[listTheory.EXISTS_MEM] >>
      Induct_on `blocks`
      >- gvs[fn_insts_blocks_def]
      >> gvs[fn_insts_blocks_def] >> metis_tac[])
  >> gvs[dft_target_mem_insts, listTheory.EXISTS_MEM] >>
     Induct_on `blocks`
  >- gvs[]
  >> gvs[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem dft_flippable_not_invoke[local]:
  is_flippable op ==> op <> INVOKE
Proof
  Cases_on `op` >> EVAL_TAC
QED

Theorem dft_flip_opcode_not_invoke[local]:
  is_flippable inst.inst_opcode ==>
  (flip_operands inst).inst_opcode <> INVOKE
Proof
  rpt strip_tac >>
  imp_res_tac dft_flippable_not_invoke >>
  Cases_on `inst.inst_operands` >> fs[flip_operands_def] >>
  Cases_on `t` >> fs[flip_operands_def] >>
  Cases_on `t'` >> fs[flip_operands_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_flippable_def, is_commutative_def, is_comparator_def,
      flip_comparison_opcode_def]
QED

Theorem dft_block_invoke_subset:
  EVERY
    (\target. MEM target
      (MAP FST (get_invoke_targets bb.bb_instructions)))
    (MAP FST (get_invoke_targets (dft_block order bb).bb_instructions))
Proof
  simp[listTheory.EVERY_MEM, dft_target_mem_insts] >>
  rpt strip_tac >>
  qpat_x_assum `EXISTS _ _` mp_tac >>
  simp[listTheory.EXISTS_MEM] >> strip_tac >>
  rename1 `dft_inst_invokes_target target inst` >>
  `MEM inst (FILTER (\i. ~is_pseudo i.inst_opcode)
      (dft_block order bb).bb_instructions)` by
    (gvs[dft_inst_invokes_target_def, listTheory.MEM_FILTER] >>
     simp[is_pseudo_def]) >>
  drule dft_block_from_orig >>
  simp[from_block_def] >> strip_tac
  >- (qexists `j` >> gvs[])
  >> imp_res_tac dft_flip_opcode_not_invoke >>
     gvs[dft_inst_invokes_target_def]
QED

Theorem dft_invoke_subset_refl:
  dft_invoke_subset blocks blocks
Proof
  simp[dft_invoke_subset_def, listTheory.EVERY_MEM]
QED

Theorem dft_invoke_subset_trans:
  dft_invoke_subset a b /\ dft_invoke_subset b c ==>
  dft_invoke_subset a c
Proof
  simp[dft_invoke_subset_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem dft_FIND_MEM[local]:
  FIND P xs = SOME x ==> MEM x xs
Proof
  qid_spec_tac `x` >> Induct_on `xs` >>
  simp[listTheory.FIND_thm] >> rw[] >> metis_tac[]
QED

Theorem dft_map_update_invoke_subset[local]:
  MEM chosen blocks ==>
  dft_invoke_subset blocks
    (MAP (\b. if b.bb_label = lbl then dft_block order chosen else b) blocks)
Proof
  strip_tac >> simp[dft_invoke_subset_def, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  gvs[dft_target_mem_blocks, listTheory.MEM_MAP] >>
  Cases_on `b.bb_label = lbl` >> gvs[]
  >- (`EVERY
         (\target. MEM target
           (MAP FST (get_invoke_targets chosen.bb_instructions)))
         (MAP FST (get_invoke_targets
           (dft_block order chosen).bb_instructions))` by
        irule dft_block_invoke_subset >>
      qpat_x_assum `EVERY _ _` mp_tac >>
      simp[listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
      disch_then (qspec_then `FST y` mp_tac) >>
      simp[listTheory.MEM_MAP] >> strip_tac >>
      simp[dft_target_mem_blocks] >> metis_tac[])
  >> simp[dft_target_mem_blocks] >> metis_tac[]
QED

Theorem dft_process_one_invoke_subset:
  dft_invoke_subset st.dls_blocks
    (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  simp[dft_process_one_def] >>
  Cases_on `lookup_block lbl st.dls_blocks`
  >- simp[dft_invoke_subset_refl]
  >> simp[] >>
     rpt (pairarg_tac >> gvs[]) >>
     Cases_on `FLOOKUP st.dls_last_order lbl` >> gvs[]
  >- (Cases_on `x = q` >> gvs[dft_invoke_subset_refl] >>
      irule dft_map_update_invoke_subset >>
      gvs[lookup_block_def] >> metis_tac[dft_FIND_MEM])
  >> Cases_on `x' = order` >> gvs[dft_invoke_subset_refl] >>
     irule dft_map_update_invoke_subset >>
     gvs[lookup_block_def] >> metis_tac[dft_FIND_MEM]
QED

Theorem dft_loop_step_invoke_subset:
  dft_invoke_subset (FST trip).dls_blocks
    (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  Cases_on `trip` >> PairCases_on `r` >>
  simp[dft_loop_step_def] >>
  Cases_on `r1` >> simp[dft_invoke_subset_refl] >>
  Cases_on `r0` >> simp[dft_invoke_subset_refl] >>
  Cases_on `dft_process_one cfg lr fn q h` >>
  PairCases_on `r` >> simp[] >>
  Cases_on `r1` >> simp[] >>
  Cases_on `r0` >> simp[] >>
  `dft_invoke_subset q.dls_blocks
     (FST (dft_process_one cfg lr fn q h)).dls_blocks` by
    irule dft_process_one_invoke_subset >>
  gvs[]
QED

Theorem dft_funpow_invoke_subset:
  !trip. dft_invoke_subset (FST trip).dls_blocks
    (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct_on `n`
  >- simp[dft_invoke_subset_refl]
  >> gen_tac >> simp[arithmeticTheory.FUNPOW_SUC] >>
     metis_tac[dft_loop_step_invoke_subset, dft_invoke_subset_trans]
QED

Theorem dft_fn_invoke_subset:
  EVERY (\target. MEM target (MAP FST (fcg_scan_function fn)))
    (MAP FST (fcg_scan_function (dft_fn fn)))
Proof
  simp[dft_fn_def, fcg_scan_function_def, fn_insts_def] >>
  pairarg_tac >> gvs[] >>
  `dft_invoke_subset fn.fn_blocks final_st.dls_blocks` by
    (`dft_invoke_subset
       (FST
         (<| dls_blocks := fn.fn_blocks; dls_from_to := FEMPTY;
              dls_last_order := FEMPTY |>,
          (cfg_analyze fn).cfg_dfs_post, F)).dls_blocks
       (FST
         (FUNPOW
           (dft_loop_step (cfg_analyze fn) (liveness_analyze fn) fn)
           (LENGTH fn.fn_blocks * LENGTH fn.fn_blocks)
           (<| dls_blocks := fn.fn_blocks; dls_from_to := FEMPTY;
                dls_last_order := FEMPTY |>,
            (cfg_analyze fn).cfg_dfs_post, F))).dls_blocks` by
       irule dft_funpow_invoke_subset >>
     gvs[]) >>
  gvs[dft_invoke_subset_def, dft_invoke_targets_def]
QED


(* ===== Raw FMP opcode preservation ===== *)
Theorem dft_flip_no_raw[local]:
  is_flippable inst.inst_opcode /\
  ~is_raw_fmp_opcode inst.inst_opcode ==>
  ~is_raw_fmp_opcode (flip_operands inst).inst_opcode
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >> fs[flip_operands_def] >>
  Cases_on `t` >> fs[flip_operands_def] >>
  Cases_on `t'` >> fs[flip_operands_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_flippable_def, is_commutative_def, is_comparator_def,
      flip_comparison_opcode_def, is_raw_fmp_opcode_def]
QED

Theorem from_block_no_raw[local]:
  from_block block_insts i /\
  EVERY (\j. ~is_raw_fmp_opcode j.inst_opcode) block_insts ==>
  ~is_raw_fmp_opcode i.inst_opcode
Proof
  simp[from_block_def, listTheory.EVERY_MEM] >>
  metis_tac[dft_flip_no_raw]
QED

Theorem dft_block_no_raw[local]:
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) bb.bb_instructions ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
        (dft_block order bb).bb_instructions
Proof
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  Cases_on `is_pseudo i.inst_opcode`
  >- (`MEM i (FILTER (\i. is_pseudo i.inst_opcode)
                  (dft_block order bb).bb_instructions)` by
        (simp[listTheory.MEM_FILTER]) >>
      qpat_x_assum `MEM i (FILTER _ _)` mp_tac >>
      rewrite_tac[dft_block_phis] >>
      simp[listTheory.MEM_FILTER] >>
      metis_tac[]) >>
  `MEM i (FILTER (\i. ~is_pseudo i.inst_opcode)
                (dft_block order bb).bb_instructions)` by
    (simp[listTheory.MEM_FILTER]) >>
  drule dft_block_from_orig >>
  simp[from_block_def] >> metis_tac[dft_flip_no_raw]
QED

Definition dft_blocks_no_raw_def[local]:
  dft_blocks_no_raw blocks <=>
    EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                       bb.bb_instructions) blocks
End

Theorem dft_blocks_no_raw_fn_insts[local]:
  dft_blocks_no_raw blocks <=>
  !inst. MEM inst (fn_insts_blocks blocks) ==>
         ~is_raw_fmp_opcode inst.inst_opcode
Proof
  rewrite_tac[dft_blocks_no_raw_def] >>
  Induct_on `blocks` >>
  simp[fn_insts_blocks_def, listTheory.EVERY_MEM,
       listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem dft_map_update_no_raw[local]:
  dft_blocks_no_raw blocks /\ MEM chosen blocks ==>
  dft_blocks_no_raw
    (MAP (\b. if b.bb_label = lbl then dft_block order chosen else b) blocks)
Proof
  simp[dft_blocks_no_raw_def, listTheory.EVERY_MAP] >>
  strip_tac >>
  irule listTheory.EVERY_MONOTONIC >>
  qexists `\b. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                  b.bb_instructions` >> simp[] >>
  rpt strip_tac >> Cases_on `x.bb_label = lbl` >> simp[] >>
  irule dft_block_no_raw >>
  qpat_x_assum `EVERY _ blocks` mp_tac >>
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem dft_process_one_no_raw[local]:
  dft_blocks_no_raw st.dls_blocks ==>
  dft_blocks_no_raw (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  strip_tac >> simp[dft_process_one_def] >>
  Cases_on `lookup_block lbl st.dls_blocks`
  >- simp[]
  >> simp[] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `FLOOKUP st.dls_last_order lbl` >> gvs[]
  >- (Cases_on `x = q` >> gvs[] >>
      irule dft_map_update_no_raw >> simp[] >>
      gvs[lookup_block_def] >> metis_tac[dft_FIND_MEM])
  >> Cases_on `x' = order` >> gvs[] >>
     irule dft_map_update_no_raw >> simp[] >>
     gvs[lookup_block_def] >> metis_tac[dft_FIND_MEM]
QED

Theorem dft_loop_step_no_raw[local]:
  dft_blocks_no_raw (FST trip).dls_blocks ==>
  dft_blocks_no_raw (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  Cases_on `trip` >> PairCases_on `r` >>
  simp[dft_loop_step_def] >>
  Cases_on `r1` >> simp[] >>
  Cases_on `r0` >> simp[] >>
  Cases_on `dft_process_one cfg lr fn q h` >>
  PairCases_on `r` >> simp[] >>
  Cases_on `r1` >> simp[] >>
  Cases_on `r0` >> simp[] >>
  strip_tac >>
  `dft_blocks_no_raw
     (FST (dft_process_one cfg lr fn q h)).dls_blocks` by
    (irule dft_process_one_no_raw >> simp[]) >>
  gvs[]
QED

Theorem dft_funpow_no_raw[local]:
  !trip. dft_blocks_no_raw (FST trip).dls_blocks ==>
    dft_blocks_no_raw
      (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct_on `n`
  >- simp[] >>
  gen_tac >> simp[arithmeticTheory.FUNPOW_SUC] >>
  metis_tac[dft_loop_step_no_raw]
QED

Theorem dft_fn_no_raw_fmp_ops:
  no_raw_fmp_ops fn ==> no_raw_fmp_ops (dft_fn fn)
Proof
  simp[dft_fn_def, no_raw_fmp_ops_def, fn_insts_def,
       GSYM dft_blocks_no_raw_fn_insts] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  `dft_blocks_no_raw
     (FST
       (FUNPOW
         (dft_loop_step (cfg_analyze fn) (liveness_analyze fn) fn)
         (LENGTH fn.fn_blocks * LENGTH fn.fn_blocks)
         (<| dls_blocks := fn.fn_blocks; dls_from_to := FEMPTY;
              dls_last_order := FEMPTY |>,
          (cfg_analyze fn).cfg_dfs_post, F))).dls_blocks` by
    (irule dft_funpow_no_raw >> simp[]) >>
  gvs[]
QED
