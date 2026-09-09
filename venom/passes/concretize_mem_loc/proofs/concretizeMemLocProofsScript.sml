(*
 * Concretize Memory Locations — Proofs
 *
 * Three components:
 * 1. Allocator soundness: allocate_with_livesets produces non-overlapping
 *    regions for simultaneously-live allocations.
 * 2. Liveness + allocator combined: compute_alloc_map produces an
 *    allocation that's non-overlapping for simultaneously-live allocas.
 * 3. Transform correctness: given memory safety + live non-overlap +
 *    write-before-read, the concretized program simulates the original.
 *
 * KEY DESIGN: the allocator reuses addresses for non-simultaneously-live
 * allocas. When alloca B reuses dead alloca A's address, A's stale bytes
 * remain on side 2. The relation uses per-byte initialization tracking
 * (init_map) to handle this: only bytes written since the current alloca
 * became live need to correspond. The write-before-read precondition
 * ensures reads never access stale bytes.
 *
 * Framework: does NOT use block_sim_function. Fully custom proof.
 *)

Theory concretizeMemLocProofs
Ancestors
  concretizeMemLocDefs allocaRemapDefs pointerConfinedDefs
  passSimulationProps passSimulationDefs passSharedProps passSharedDefs
  venomWf venomExecSemantics venomExecProofs opcodeClass
  venomMemDefs venomMemProofs stateEquiv
  venomInst venomState
  list finite_map pair arithmetic sorting enumeral toto
  words pred_set combin
Libs
  fcpLib

(* Batch-safe dimindex(:256) = 256 via fcpLib.INDEX_CONV *)
val dim256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

(* ===== Bridge: amap ↔ alloca inst_id ===== *)

(* Map alloca inst_id to its concrete address from amap. *)
Definition alloca_concrete_addr_def:
  alloca_concrete_addr (amap : alloc_map) fn aid =
    case FIND (\inst. inst.inst_id = aid /\
                      is_alloca_op inst.inst_opcode)
              (fn_insts fn) of
      SOME inst =>
        (case inst.inst_outputs of
           [out] => FLOOKUP amap out
         | _ => NONE)
    | NONE => NONE
End

(* ===== Liveness-aware non-overlap ===== *)

Definition alloca_live_at_def:
  alloca_live_at (livesets : (allocation, inst_addr list) fmap)
                 aid (point : inst_addr) <=>
    case FLOOKUP livesets (Allocation aid) of
      SOME ls => MEM point ls
    | NONE => F
End

(* Simultaneously-live allocas have non-overlapping concrete regions. *)
Definition live_non_overlapping_def:
  live_non_overlapping (livesets : (allocation, inst_addr list) fmap)
                       (amap : alloc_map) fn <=>
    !v1 v2 addr1 addr2 aid1 aid2 sz1 sz2 ls1 ls2.
      FLOOKUP amap v1 = SOME addr1 /\
      FLOOKUP amap v2 = SOME addr2 /\
      fn_alloca_id_of_var fn v1 = SOME aid1 /\
      fn_alloca_id_of_var fn v2 = SOME aid2 /\
      v1 <> v2 /\
      FLOOKUP livesets (Allocation aid1) = SOME ls1 /\
      FLOOKUP livesets (Allocation aid2) = SOME ls2 /\
      sinter inst_addr_to ls1 ls2 <> [] /\
      get_alloca_size fn (Allocation aid1) = sz1 /\
      get_alloca_size fn (Allocation aid2) = sz2 ==>
      w2n addr1 + sz1 <= w2n addr2 \/
      w2n addr2 + sz2 <= w2n addr1
End

(* Address falls within a concrete alloca region. *)
Definition in_concrete_region_def:
  in_concrete_region (amap : alloc_map) fn i <=>
    ?v addr aid sz.
      FLOOKUP amap v = SOME addr /\
      fn_alloca_id_of_var fn v = SOME aid /\
      get_alloca_size fn (Allocation aid) = sz /\
      w2n addr <= i /\ i < w2n addr + sz
End

(* ===== Concretize-specific pointer wrappers ===== *)

Definition concretize_pointer_derived_def:
  concretize_pointer_derived fn (amap : alloc_map) =
    pointer_derived_vars fn (FDOM amap)
End

Definition concretize_pointer_confined_def:
  concretize_pointer_confined fn (amap : alloc_map) <=>
    pointer_confined fn (FDOM amap)
End

(* ===== Per-byte initialization tracking ===== *)

(* Tracks which bytes of each alloca region have been written since
   the alloca last became live. When an alloca's memory is reused
   from a dead alloca, unwritten bytes may have stale data on side 2.
   Only written (initialized) bytes need to correspond. *)
Type init_map = ``:(num, num set) fmap``

Definition is_initialized_def:
  is_initialized (init : init_map) aid i <=>
    case FLOOKUP init aid of SOME s => i IN s | NONE => F
End

(* ===== Write-before-read precondition ===== *)

(* Per-state invariant: for each memory-reading instruction, the
   address operand's alloca has all its bytes initialized.
   The address must be contained in the alloca (off <= w2n w < off+sz),
   the alloca must be live, and all bytes must be initialized.

   Specifically: if a MLOAD/SHA3/MCOPY reads through a pv address w
   that is in alloca [off, off+sz), then that alloca is live and
   fully initialized.

   True for Vyper: allocas are zeroed immediately after creation. *)
Definition alloca_write_before_read_def:
  alloca_write_before_read fn (roots : string set)
      (livesets : (allocation, inst_addr list) fmap)
      (init : init_map) s <=>
    let pv = pointer_derived_vars fn roots in
    !v w aid off sz.
      v IN pv /\
      lookup_var v s = SOME w /\
      FLOOKUP s.vs_allocas aid = SOME (off, sz) /\
      off <= w2n w /\ w2n w < off + sz ==>
      alloca_live_at livesets aid (s.vs_current_bb, 0) /\
      (!i. i < sz ==> is_initialized init aid i)
End

(* ===== State relation: concretize_rel ===== *)

(* Relates original state (s1, with runtime allocas) to transformed
   state (s2, with compile-time assigns).
   
   Parameterized by:
   - livesets: from mem_liveness_analyze
   - init: which bytes have been written since each alloca became live
   
   Key: clause 3 uses is_initialized — only written bytes of live
   alloca regions need to correspond. Unwritten bytes may have stale
   data on side 2 from a dead alloca that previously used the address. *)
Definition concretize_rel_def:
  concretize_rel (amap : alloc_map) fn
                 (livesets : (allocation, inst_addr list) fmap)
                 (init : init_map) s1 s2 <=>
    let roots = FDOM amap in
    let pv = pointer_derived_vars fn roots in
    let point = (s1.vs_current_bb, 0:num) in
    (* 1. Non-pointer variables agree *)
    (!v. v NOTIN pv ==>
         lookup_var v s1 = lookup_var v s2) /\
    (* 2. Pointer-derived variables: displacement invariant.
       Holds for ALL pv vars, even dead allocas (SSA: set once).
       Containment: w1 is within the alloca region [orig_off, orig_off+sz).
       Maintained by pointer_arith_in_region for derived pointers
       and trivially holds at ALLOCA (w1 = n2w orig_off, sz > 0). *)
    (!v. v IN pv ==>
       lookup_var v s1 = NONE /\ lookup_var v s2 = NONE \/
       ?w1 w2 aid orig_off sz addr.
         FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
         alloca_concrete_addr amap fn aid = SOME addr /\
         lookup_var v s1 = SOME w1 /\
         lookup_var v s2 = SOME w2 /\
         orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
         w1 - n2w orig_off = w2 - addr /\
         orig_off + sz < dimword (:256) /\
         w2n addr + sz < dimword (:256)) /\
    (* 3. Memory: INITIALIZED bytes of LIVE alloca regions correspond.
       Uninitialized bytes may differ (stale from dead alloca). *)
    (!aid orig_off sz addr i.
       FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
       alloca_concrete_addr amap fn aid = SOME addr /\
       alloca_live_at livesets aid point /\
       is_initialized init aid i /\
       i < sz ==>
       mem_byte_at s1.vs_memory (orig_off + i) =
       mem_byte_at s2.vs_memory (w2n addr + i)) /\
    (* 4. Memory OUTSIDE alloca regions (both sides) is byte-identical.
       Excludes s1's bump-allocated regions AND s2's concrete regions.
       Positions inside one but not the other may differ. *)
    (!i. ~in_alloca_region s1 i /\ ~in_concrete_region amap fn i ==>
         mem_byte_at s1.vs_memory i =
         mem_byte_at s2.vs_memory i) /\
    (* 5. Non-overlapping regions in s1 *)
    allocas_non_overlapping s1 /\
    (* 6. Scalar state fields agree *)
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token
End

(* ===== 1. Allocator Soundness ===== *)

(* -- first_fit_pos helpers -- *)

(* first_fit_pos avoids all reserved regions. *)
Triviality pos_cmp_transitive:
  transitive (\(p1:num,_) (p2,_). p1 <= p2)
Proof
  simp[relationTheory.transitive_def, FORALL_PROD]
QED

Triviality pos_cmp_total:
  relation$total (\(p1:num,_) (p2,_). p1 <= p2)
Proof
  simp[relationTheory.total_def, FORALL_PROD]
QED

Triviality sorted_pos_mem:
  !h0 h1 t.
    SORTED (\(p1:num,_:num) (p2,_). p1 <= p2) ((h0,h1)::t) ==>
    !p s. MEM (p,s) t ==> h0 <= p
Proof
  rpt strip_tac >>
  imp_res_tac (iffLR (SORTED_EQ
    |> Q.ISPEC `\(p1:num,_:num) (p2:num,_:num). p1 <= p2`
    |> SIMP_RULE std_ss [pos_cmp_transitive, FORALL_PROD]))
QED

(* first_fit_pos returns a position at or after `start` that does not overlap
   any reserved region. *)
Theorem first_fit_pos_correct:
  !reserved size start.
    SORTED (\(p1:num,_:num) (p2,_). p1 <= p2) reserved ==>
    start <= first_fit_pos reserved size start /\
    !rpos rsz. MEM (rpos, rsz) reserved ==>
      first_fit_pos reserved size start + size <= rpos \/
      rpos + rsz <= first_fit_pos reserved size start
Proof
  Induct >- simp[Once first_fit_pos_def]
  >> Cases >> rpt gen_tac >> rename1 `(hp,hs)::rest`
  >> once_rewrite_tac[first_fit_pos_def] >> simp[] >> strip_tac
  >> imp_res_tac SORTED_TL
  >> drule sorted_pos_mem >> strip_tac
  >> IF_CASES_TAC >> gvs[]
  >- suspend "skip"
  >> IF_CASES_TAC >> gvs[]
  >- suspend "gap"
  >> suspend "overlap"
QED

Resume first_fit_pos_correct[skip]:
  first_x_assum (qspecl_then [`size'`, `start`] strip_assume_tac)
  >> rpt strip_tac >> gvs[]
  >> disj2_tac >> irule LESS_EQ_TRANS
  >> qexists `start` >> simp[]
QED

Resume first_fit_pos_correct[gap]:
  rpt strip_tac >> gvs[]
  >> metis_tac[LESS_EQ_TRANS]
QED

Resume first_fit_pos_correct[overlap]:
  first_x_assum (qspecl_then [`size'`, `hp + hs`] strip_assume_tac)
  >> conj_tac >- metis_tac[LESS_EQ_TRANS,
    LESS_IMP_LESS_OR_EQ, NOT_LESS_EQUAL]
  >> rpt strip_tac >> gvs[]
QED

Finalise first_fit_pos_correct

(* allocate_one produces a position that does not overlap any reserved region. *)
Theorem allocate_one_avoids:
  !reserved sz pos rest.
    allocate_one reserved sz = (pos, rest) ==>
    !rpos rsz. MEM (rpos, rsz) reserved ==>
      pos + sz <= rpos \/ rpos + rsz <= pos
Proof
  rw[allocate_one_def]
  >> `SORTED (\(p1:num,_) (p2,_). p1 <= p2)
             (QSORT (\(p1:num,_) (p2,_). p1 <= p2) reserved)`
    by (irule QSORT_SORTED
      >> simp[pos_cmp_transitive, pos_cmp_total])
  >> drule first_fit_pos_correct >> strip_tac
  >> `MEM (rpos,rsz) (QSORT (\(p1:num,_) (p2,_). p1 <= p2) reserved)`
    by simp[QSORT_MEM]
  >> res_tac >> simp[]
QED

(* -- Main allocator theorem -- *)

(* Helper: MEM through MAP of FILTER *)
Triviality mem_map_drop_pos:
  !a l sz already.
    MEM (a,l,sz) (MAP (\(a,l,p,s). (a,l,s)) already) ==>
    ?p. MEM (a,l,p,sz) already
Proof
  Induct_on `already` >> simp[FORALL_PROD] >> rw[] >> metis_tac[]
QED

Triviality mem_map_filter_already:
  !a l p s already live_insts.
    MEM (a,l,p,s) already /\
    sinter inst_addr_to l live_insts <> [] ==>
    MEM (p,s) (MAP (\(_,_,pos,asz). (pos,asz))
      (FILTER (\(_,other_live,_,_).
        sinter inst_addr_to other_live live_insts <> []) already))
Proof
  Induct_on `already` >> simp[FORALL_PROD] >> rw[] >> metis_tac[]
QED

(* allocate_with_livesets extends an allocation so that simultaneously-live
   allocas have non-overlapping positions. Existing allocations are preserved;
   new allocations are placed without overlapping any simultaneously-live
   already-allocated entry. *)
Theorem allocate_with_livesets_non_overlapping:
  !global already to_alloc result.
    (!a l p s. MEM (a,l,p,s) already ==> FLOOKUP result a = SOME p) /\
    (!a1 a2 l1 l2 p1 p2 s1 s2.
       MEM (a1,l1,p1,s1) already /\
       MEM (a2,l2,p2,s2) already /\
       a1 <> a2 /\
       sinter inst_addr_to l1 l2 <> [] ==>
       p1 + s1 <= p2 \/ p2 + s2 <= p1) /\
    (!a l s. MEM (a,l,s) to_alloc ==>
       !l' p' s'. ~MEM (a,l',p',s') already) /\
    ALL_DISTINCT (MAP FST to_alloc) ==>
    let result' = allocate_with_livesets global already to_alloc result in
    !a1 a2 ls1 ls2 p1 p2 sz1 sz2.
      FLOOKUP result' a1 = SOME p1 /\
      FLOOKUP result' a2 = SOME p2 /\
      a1 <> a2 /\
      MEM (a1, ls1, sz1) (MAP (\(a,l,p,s). (a,l,s)) already ++
                           MAP (\(a,l,s). (a,l,s)) to_alloc) /\
      MEM (a2, ls2, sz2) (MAP (\(a,l,p,s). (a,l,s)) already ++
                           MAP (\(a,l,s). (a,l,s)) to_alloc) /\
      sinter inst_addr_to ls1 ls2 <> [] ==>
      p1 + sz1 <= p2 \/ p2 + sz2 <= p1
Proof
  ho_match_mp_tac allocate_with_livesets_ind
  >> rpt conj_tac
  >- suspend "base"
  >> suspend "step"
QED

Resume allocate_with_livesets_non_overlapping[base]:
  simp[allocate_with_livesets_def]
  >> rpt strip_tac
  >> `?p1'. MEM (a1,ls1,p1',sz1) already` by metis_tac[mem_map_drop_pos]
  >> `?p2'. MEM (a2,ls2,p2',sz2) already` by metis_tac[mem_map_drop_pos]
  >> `FLOOKUP result a1 = SOME p1'` by metis_tac[]
  >> `FLOOKUP result a2 = SOME p2'` by metis_tac[]
  >> `p1' = p1` by gvs[]
  >> `p2' = p2` by gvs[]
  >> gvs[] >> metis_tac[]
QED

Triviality sinter_nonempty_comm:
  !cmp l m. sinter cmp l m <> [] ==> sinter cmp m l <> []
Proof
  ho_match_mp_tac sinter_ind >> rpt conj_tac
  >- simp[sinter]
  >- simp[sinter]
  >- simp[sinter]
  >> rpt gen_tac >> strip_tac
  >> once_rewrite_tac[sinter] >> strip_tac
  >> Cases_on `apto cmp x y` >> gvs[]
  >> simp[Once toto_swap_cases]
QED

(* Step invariant: after allocating one alloca with allocate_one,
   the FLOOKUP, non-overlap, freshness, and ALL_DISTINCT invariants of
   allocate_with_livesets are preserved in the extended state. *)
Theorem awl_step_invs:
  !global already alloc live_insts pos sz to_alloc result _0.
    (!a l p s. MEM (a,l,p,s) already ==> FLOOKUP result a = SOME p) /\
    (!a1 a2 l1 l2 p1 p2 s1 s2.
       MEM (a1,l1,p1,s1) already /\
       MEM (a2,l2,p2,s2) already /\ a1 <> a2 /\
       sinter inst_addr_to l1 l2 <> [] ==>
       p1 + s1 <= p2 \/ p2 + s2 <= p1) /\
    (!a l s. MEM (a,l,s) ((alloc,live_insts,sz)::to_alloc) ==>
       !l' p' s'. ~MEM (a,l',p',s') already) /\
    ALL_DISTINCT (MAP FST ((alloc,live_insts,sz)::to_alloc)) /\
    allocate_one
      (global ++ MAP (\(_1,_2,pos,asz). (pos,asz))
        (FILTER (\(_3,other_live,_4,_5).
          sinter inst_addr_to other_live live_insts <> []) already)) sz =
      (pos, _0) ==>
    (* Extended invariants *)
    (!a l p s.
       MEM (a,l,p,s) (already ++ [(alloc,live_insts,pos,sz)]) ==>
       FLOOKUP (result |+ (alloc,pos)) a = SOME p) /\
    (!a1 a2 l1 l2 p1 p2 s1 s2.
       MEM (a1,l1,p1,s1) (already ++ [(alloc,live_insts,pos,sz)]) /\
       MEM (a2,l2,p2,s2) (already ++ [(alloc,live_insts,pos,sz)]) /\ a1 <> a2 /\
       sinter inst_addr_to l1 l2 <> [] ==>
       p1 + s1 <= p2 \/ p2 + s2 <= p1) /\
    (!a l s. MEM (a,l,s) to_alloc ==>
       !l' p' s'. ~MEM (a,l',p',s') (already ++ [(alloc,live_insts,pos,sz)])) /\
    ALL_DISTINCT (MAP FST to_alloc)
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- suspend "inv1"
  >- suspend "inv2"
  >- suspend "inv3"
  >> suspend "inv4"
QED

Resume awl_step_invs[inv1]:
  rpt strip_tac >> gvs[MEM_APPEND, FLOOKUP_UPDATE]
  >> Cases_on `alloc = a` >> gvs[] >> metis_tac[]
QED

Resume awl_step_invs[inv2]:
  rpt strip_tac >> gvs[MEM_APPEND, FLOOKUP_UPDATE]
  >| [
    (* old-old *)
    metis_tac[],
    (* old-new: a2 = alloc, need allocate_one_avoids *)
    drule mem_map_filter_already
    >> disch_then (qspec_then `l2` mp_tac) >> simp[]
    >> strip_tac
    >> drule allocate_one_avoids
    >> disch_then (qspecl_then [`p1`,`s1`] mp_tac)
    >> simp[MEM_APPEND],
    (* new-old: a1 = alloc, need sinter_nonempty_comm *)
    drule mem_map_filter_already
    >> disch_then (qspec_then `l1` mp_tac)
    >> (impl_tac >- metis_tac[sinter_nonempty_comm])
    >> strip_tac
    >> drule allocate_one_avoids
    >> disch_then (qspecl_then [`p2`,`s2`] mp_tac)
    >> simp[MEM_APPEND]
  ]
QED

Resume awl_step_invs[inv3]:
  rpt strip_tac >> gvs[MEM_APPEND]
  >| [
    first_x_assum (qspecl_then [`a`,`l`,`s`] mp_tac) >> simp[]
    >> metis_tac[],
    gvs[MEM_MAP, FORALL_PROD, EXISTS_PROD]
  ]
QED

Resume awl_step_invs[inv4]:
  gvs[ALL_DISTINCT]
QED

Finalise awl_step_invs

Resume allocate_with_livesets_non_overlapping[step]:
  rpt gen_tac >> strip_tac >> rpt strip_tac
  >> simp[Once allocate_with_livesets_def]
  >> pairarg_tac >> simp[]
  >> first_x_assum (mp_tac o Q.SPECL [`global ++ MAP (\(_1,_2,pos',asz). (pos',asz)) (FILTER (\(_3,other_live,_4,_5). sinter inst_addr_to other_live live_insts <> []) already)`, `pos`, `_0`])
  >> impl_tac >- simp[]
  >> impl_tac >- (irule awl_step_invs >> metis_tac[])
  >> simp[LET_THM, MAP_APPEND, MEM_APPEND, MEM, FORALL_PROD, DISJ_ASSOC]
QED

Finalise allocate_with_livesets_non_overlapping

(* ===== 2. Liveness + Allocator Combined ===== *)

(* Per-instruction step for alloc_result_to_map fold *)
Definition arm_step_def:
  arm_step result amap inst =
    if is_alloca_op inst.inst_opcode then
      case inst.inst_outputs of
        [out] =>
          (case FLOOKUP result (Allocation inst.inst_id) of
             SOME pos => amap |+ (out, n2w pos)
           | NONE => amap)
      | _ => amap
    else amap
End

Triviality foldl_cong_step:
  !l result acc.
    FOLDL (\amap' inst.
      if is_alloca_op inst.inst_opcode then
        case inst.inst_outputs of
          [out] =>
            (case FLOOKUP result (Allocation inst.inst_id) of
               SOME pos => amap' |+ (out, n2w pos)
             | NONE => amap')
        | _ => amap'
      else amap') acc l =
    FOLDL (arm_step result) acc l
Proof
  Induct >> simp[arm_step_def]
QED

Triviality arm_foldl_blocks:
  !bbs result acc.
    FOLDL (\amap bb.
      FOLDL (\amap' inst.
        if is_alloca_op inst.inst_opcode then
          case inst.inst_outputs of
            [out] =>
              (case FLOOKUP result (Allocation inst.inst_id) of
                 SOME pos => amap' |+ (out, n2w pos)
               | NONE => amap')
          | _ => amap'
        else amap')
        amap bb.bb_instructions)
      acc bbs =
    FOLDL (arm_step result) acc (fn_insts_blocks bbs)
Proof
  Induct >> simp[venomInstTheory.fn_insts_blocks_def]
  >> rpt gen_tac
  >> simp[rich_listTheory.FOLDL_APPEND, foldl_cong_step]
QED

Triviality arm_flatten:
  !fn result.
    alloc_result_to_map fn result =
    FOLDL (arm_step result) FEMPTY (fn_insts fn)
Proof
  simp[alloc_result_to_map_def, venomInstTheory.fn_insts_def,
       arm_foldl_blocks]
QED

(* arm_step preserves FLOOKUP for variables not in inst outputs *)
Triviality arm_step_other:
  !result amap inst v.
    ~MEM v inst.inst_outputs ==>
    FLOOKUP (arm_step result amap inst) v = FLOOKUP amap v
Proof
  rpt strip_tac >> simp[arm_step_def]
  >> rpt CASE_TAC >> gvs[FLOOKUP_UPDATE]
QED

(* FOLDL arm_step preserves FLOOKUP for variables not in any outputs *)
Triviality arm_foldl_other:
  !insts result acc v.
    ~MEM v (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    FLOOKUP (FOLDL (arm_step result) acc insts) v = FLOOKUP acc v
Proof
  Induct >> simp[] >> rpt strip_tac
  >> first_x_assum drule >> disch_then (fn th => simp[th])
  >> irule arm_step_other >> simp[]
QED

(* Key inductive lemma: FLOOKUP after FOLDL under ALL_DISTINCT outputs *)
Triviality arm_foldl_flookup:
  !insts result acc v (addr : 'a word).
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
    (!v'. MEM v' (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
          v' NOTIN FDOM acc) /\
    FLOOKUP (FOLDL (arm_step result) acc insts) v = SOME addr /\
    FLOOKUP acc v = NONE ==>
    ?inst pos. MEM inst insts /\
           is_alloca_op inst.inst_opcode /\
           inst.inst_outputs = [v] /\
           FLOOKUP result (Allocation inst.inst_id) = SOME pos /\
           addr = n2w pos
Proof
  Induct >- simp[FLOOKUP_DEF]
  >> rpt gen_tac >> strip_tac >> rename1 `i::insts`
  >> gvs[ALL_DISTINCT_APPEND]
  >> reverse (Cases_on `is_alloca_op i.inst_opcode`) >> gvs[arm_step_def]
  (* non-alloca: identity *)
  >- (last_x_assum (qspecl_then [`result`, `acc`, `v`, `addr`] mp_tac)
      >> simp[] >> metis_tac[])
  >> Cases_on `i.inst_outputs` >> gvs[]
  >- (last_x_assum (qspecl_then [`result`, `acc`, `v`, `addr`] mp_tac)
      >> simp[] >> metis_tac[])
  >> Cases_on `t` >> gvs[]
  >~ [`_::_::_`]
  >- (last_x_assum (qspecl_then [`result`, `acc`, `v`, `addr`] mp_tac)
      >> simp[] >> metis_tac[])
  >> rename1 `i.inst_outputs = [out]`
  >> Cases_on `FLOOKUP result (Allocation i.inst_id)` >> gvs[]
  >- (last_x_assum (qspecl_then [`result`, `acc`, `v`, `addr`] mp_tac)
      >> simp[] >> metis_tac[])
  >> rename1 `FLOOKUP result (Allocation i.inst_id) = SOME pos`
  >> Cases_on `v = out` >> gvs[]
  (* v = out *)
  >- (
    qexistsl [`i`, `pos`] >> simp[]
    >> qpat_x_assum `FLOOKUP _ out = SOME addr` mp_tac
    >> `~MEM out (FLAT (MAP (\i. i.inst_outputs) insts))` by simp[]
    >> drule arm_foldl_other
    >> disch_then (qspecl_then [`result`, `acc |+ (out, n2w pos)`] mp_tac)
    >> simp[FLOOKUP_UPDATE]
  )
  (* v <> out *)
  >> last_x_assum (qspecl_then [`result`, `acc |+ (out, n2w pos)`, `v`, `addr`] mp_tac)
  >> simp[FLOOKUP_UPDATE, FDOM_FUPDATE]
  >> metis_tac[]
QED

(* FIND on same list finds the same instruction under ALL_DISTINCT *)
Triviality find_mem_alloca:
  !insts v inst.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
    MEM inst insts /\
    is_alloca_op inst.inst_opcode /\
    inst.inst_outputs = [v] ==>
    FIND (\i. is_alloca_op i.inst_opcode /\ i.inst_outputs = [v]) insts
    = SOME inst
Proof
  Induct
  >- simp[FIND_thm]
  >> rpt gen_tac >> simp[FIND_thm]
  >> strip_tac >> gvs[]
  (* gvs resolves inst=h case; remaining: MEM inst insts *)
  >> IF_CASES_TAC >> gvs[]
  >- ((* h matches v too — but v not in tail, yet inst in tail has v *)
      gvs[MEM_FLAT, MEM_MAP] >> metis_tac[MEM])
  >> first_x_assum irule >> simp[]
  >> qpat_x_assum `ALL_DISTINCT _` mp_tac
  >> simp[ALL_DISTINCT_APPEND]
QED

(* Bridge: alloc_result_to_map → fn_alloca_id_of_var + result FLOOKUP *)
Triviality alloc_result_to_map_flookup:
  !fn result v addr.
    ssa_form fn /\
    FLOOKUP (alloc_result_to_map fn result) v = SOME (addr : 256 word) ==>
    ?aid pos. fn_alloca_id_of_var fn v = SOME aid /\
          FLOOKUP result (Allocation aid) = SOME pos /\
          addr = n2w pos
Proof
  rpt strip_tac >> gvs[arm_flatten]
  >> `?inst pos. MEM inst (fn_insts fn) /\
             is_alloca_op inst.inst_opcode /\
             inst.inst_outputs = [v] /\
             FLOOKUP result (Allocation inst.inst_id) = SOME pos /\
             addr = n2w pos` by (
       qspecl_then [`fn_insts fn`, `result`, `FEMPTY`, `v`, `addr`]
         mp_tac arm_foldl_flookup
       >> simp[FLOOKUP_DEF, ssa_form_def] >> gvs[ssa_form_def])
  >> `FIND (\i. is_alloca_op i.inst_opcode /\ i.inst_outputs = [v])
           (fn_insts fn) = SOME inst` by (
       irule find_mem_alloca >> gvs[ssa_form_def])
  >> simp[fn_alloca_id_of_var_def]
QED

(* Injectivity from ALL_DISTINCT MAP *)
Triviality ALL_DISTINCT_MAP_MEM_INJ:
  !f l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ f x = f y ==> x = y
Proof
  rpt strip_tac >> gvs[MEM_EL]
  >> metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]
QED

Triviality FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rpt strip_tac
  >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Triviality FIND_P:
  !P l x. FIND P l = SOME x ==> P x
Proof
  Induct_on `l` >> simp[FIND_thm] >> rpt strip_tac
  >> gvs[AllCaseEqs()] >> metis_tac[]
QED

(* fn_inst_ids_distinct ↔ ALL_DISTINCT on fn_insts *)
Triviality fn_inst_ids_distinct_alt:
  !fn. fn_inst_ids_distinct fn <=>
       ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  simp[fn_inst_ids_distinct_def, fn_insts_def]
  >> gen_tac
  >> `!bbs. fn_insts_blocks bbs =
            FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
       (Induct >> simp[fn_insts_blocks_def])
  >> simp[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

(* fn_alloca_id_of_var is injective under SSA + distinct inst IDs *)
Triviality fn_alloca_id_of_var_injective:
  !fn v1 v2 aid.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    fn_alloca_id_of_var fn v1 = SOME aid /\
    fn_alloca_id_of_var fn v2 = SOME aid ==>
    v1 = v2
Proof
  rpt strip_tac
  >> gvs[fn_alloca_id_of_var_def, AllCaseEqs()]
  >> imp_res_tac FIND_MEM >> imp_res_tac FIND_P
  >> `inst = inst'` by
       metis_tac[ALL_DISTINCT_MAP_MEM_INJ, fn_inst_ids_distinct_alt]
  >> gvs[]
QED

(* compute_alloc_map + alloc_result_to_map produces an amap satisfying
   live_non_overlapping: simultaneously-live allocas map to
   non-overlapping concrete addresses. *)
Theorem compute_alloc_map_live_non_overlapping:
  !fn bpr mems_used live_pallocas cfg pre_allocated global_reserved.
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    (let alloca_sz = get_alloca_size fn in
     let alloca_sz_opt = \a. let sz = alloca_sz a in
                             if sz = 0 then NONE else SOME sz in
     let livesets = mem_liveness_analyze bpr mems_used alloca_sz_opt
                      live_pallocas cfg fn in
     let result = compute_alloc_map fn bpr mems_used live_pallocas cfg
                    pre_allocated global_reserved in
       (!a p. FLOOKUP result a = SOME p ==> p < dimword (:256)) /\
       (!a1 a2 ls1 ls2 p1 p2 sz1 sz2.
          FLOOKUP result a1 = SOME p1 /\
          FLOOKUP result a2 = SOME p2 /\
          a1 <> a2 /\
          FLOOKUP livesets a1 = SOME ls1 /\
          FLOOKUP livesets a2 = SOME ls2 /\
          sinter inst_addr_to ls1 ls2 <> [] /\
          get_alloca_size fn a1 = sz1 /\
          get_alloca_size fn a2 = sz2 ==>
          p1 + sz1 <= p2 \/ p2 + sz2 <= p1)) ==>
    let alloca_sz = get_alloca_size fn in
    let alloca_sz_opt = \a. let sz = alloca_sz a in
                            if sz = 0 then NONE else SOME sz in
    let livesets = mem_liveness_analyze bpr mems_used alloca_sz_opt
                     live_pallocas cfg fn in
    let amap = alloc_result_to_map fn
      (compute_alloc_map fn bpr mems_used live_pallocas cfg
         pre_allocated global_reserved) in
    live_non_overlapping livesets amap fn
Proof
  rpt gen_tac >> strip_tac >>
  gvs[LET_THM, live_non_overlapping_def] >>
  rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `FLOOKUP (alloc_result_to_map fn result) v1` >>
  qmatch_asmsub_abbrev_tac `FLOOKUP livesets (Allocation aid1)` >>
  `?aid1' pos1.
     fn_alloca_id_of_var fn v1 = SOME aid1' /\
     FLOOKUP result (Allocation aid1') = SOME pos1 /\
     addr1 = n2w pos1` by
    (irule alloc_result_to_map_flookup >> simp[Abbr `result`]) >>
  `?aid2' pos2.
     fn_alloca_id_of_var fn v2 = SOME aid2' /\
     FLOOKUP result (Allocation aid2') = SOME pos2 /\
     addr2 = n2w pos2` by
    (irule alloc_result_to_map_flookup >> simp[Abbr `result`]) >>
  `aid1' = aid1` by gvs[] >>
  `aid2' = aid2` by gvs[] >>
  gvs[] >>
  `aid1 <> aid2` by metis_tac[fn_alloca_id_of_var_injective] >>
  `pos1 < dimword (:256) /\ pos2 < dimword (:256)` by metis_tac[] >>
  first_x_assum (qspecl_then
    [`Allocation aid1`, `Allocation aid2`, `ls1`, `ls2`, `pos1`, `pos2`] mp_tac) >>
  simp[Abbr `result`, Abbr `livesets`] >>
  strip_tac >> simp[]
QED

(* ===== 3. Transform Correctness ===== *)

(* Alias: lookup_block_map is in passSimulationProps (Ancestors) *)
val lookup_block_map_proof = lookup_block_map;

(* --- 3a. concretize_rel is preserved by state_equiv on the right ---
   Used to compose the core simulation (fmt level) with clear_nops. *)

Triviality state_equiv_empty_eq:
  !s2 s3. state_equiv {} s2 s3 ==> s2 = s3
Proof
  rw[state_equiv_def, execution_equiv_def, NOT_IN_EMPTY,
     venom_state_component_equality, lookup_var_def] >>
  metis_tac[fmap_eq_flookup]
QED

(* execution_equiv {} preserves concretize_rel on the right,
   IF current_bb and prev_bb also match. *)
Triviality concretize_rel_right_exec_equiv_ext:
  !amap fn livesets init s1 s2 s3.
    concretize_rel amap fn livesets init s1 s2 /\
    execution_equiv {} s2 s3 /\
    s2.vs_current_bb = s3.vs_current_bb /\
    s2.vs_prev_bb = s3.vs_prev_bb ==>
    concretize_rel amap fn livesets init s1 s3
Proof
  rpt strip_tac >>
  fs[concretize_rel_def, LET_THM, execution_equiv_def, NOT_IN_EMPTY,
     lookup_var_def, allocas_non_overlapping_def, in_alloca_region_def] >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> fs[] >>
  metis_tac[fmap_eq_flookup]
QED

(* concretize_rel is preserved on the right when s2 is replaced by
   a state_equiv {} s3 — any state equal on all variable-free fields
   preserves the concretize simulation relation. *)
Theorem concretize_rel_right_state_equiv:
  !amap fn livesets init s1 s2 s3.
    concretize_rel amap fn livesets init s1 s2 /\
    state_equiv {} s2 s3 ==>
    concretize_rel amap fn livesets init s1 s3
Proof
  rpt strip_tac >> imp_res_tac state_equiv_empty_eq >> gvs[]
QED


(* concretize_function = function_map_transform with a composite bt *)
Triviality concretize_function_as_fmt:
  !amap fn.
    concretize_function amap fn =
    function_map_transform
      (\bb. clear_nops_block (block_map_transform (concretize_inst amap) bb))
      fn
Proof
  rw[concretize_function_def, clear_nops_function_def,
     function_map_transform_def, MAP_MAP_o, o_DEF]
QED

(* The composite block transform preserves bb_label *)
Triviality concretize_bt_preserves_label:
  !amap bb.
    (clear_nops_block (block_map_transform (concretize_inst amap) bb)).bb_label
    = bb.bb_label
Proof
  rw[clear_nops_block_def, block_map_transform_def]
QED

(* --- 3b. Per-block simulation ---

   Architecture: Direct induction on exec_block via run_defs_ind, following
   the clear_nops_block_gen pattern but with custom concretize_rel instead
   of result_equiv.

   Side 1 runs bb (original), side 2 runs clear_nops_block(bmt(ci amap) bb).
   Instruction index mapping: side 2's index tracks the number of non-NOP
   transformed instructions seen so far (NOPs from original + alloca→NOP).

   Per-instruction cases:
   - NOP (original or alloca not in amap → NOP): side 1 steps, side 2 skips
   - ALLOCA in amap → ASSIGN: side 1 bump-allocates, side 2 assigns address
   - Non-alloca, non-INVOKE: same instruction on both CR-related states
   - INVOKE: excluded by the block-level theorem precondition
   - Terminator: same terminator, CR transfer through result
*)

(* All alloca outputs in function are mapped by amap.
   Needed: prevents alloca executing on side 1 while NOP is filtered
   on side 2, which would break CR clause 1 (non-pv var disagreement). *)
Definition all_allocas_mapped_def:
  all_allocas_mapped fn (amap : alloc_map) <=>
    !bb inst out.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      is_alloca_op inst.inst_opcode /\ inst.inst_outputs = [out] ==>
      out IN FDOM amap
End

(* concretize_inst produces NOP only for:
   1. Original NOP instructions (not alloca)
   2. Alloca with single output not in amap (turned into mk_nop_inst)
   Note: alloca with [] or 2+ outputs passes through unchanged. *)
Triviality ci_nop_cases:
  !amap inst.
    (concretize_inst amap inst).inst_opcode = NOP <=>
    (~is_alloca_op inst.inst_opcode /\ inst.inst_opcode = NOP) \/
    (is_alloca_op inst.inst_opcode /\
     ?out. inst.inst_outputs = [out] /\ FLOOKUP amap out = NONE)
Proof
  rpt gen_tac >> simp[concretize_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt CASE_TAC >>
  gvs[mk_nop_inst_def, mk_assign_inst_def, is_alloca_op_def] >>
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]
QED

(* Under all_allocas_mapped, ci produces NOP only for original NOPs. *)
Triviality ci_nop_from_nop:
  !amap inst bb fn.
    all_allocas_mapped fn amap /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    (concretize_inst amap inst).inst_opcode = NOP ==>
    inst.inst_opcode = NOP
Proof
  rw[ci_nop_cases, all_allocas_mapped_def, FLOOKUP_DEF] >> metis_tac[]
QED

(* --- Helpers for per-instruction simulation --- *)

(* Roots (FDOM amap) are in pointer_derived_vars *)
Triviality pointer_use_vars_mem:
  !fn vars v. MEM v vars ==> MEM v (pointer_use_vars fn vars)
Proof
  rpt gen_tac >> strip_tac >>
  simp[pointer_use_vars_def] >>
  qabbrev_tac `g = \w:string list + string list.
    case pointer_use_step_step fn (OUTL w) of
      NONE => INR (OUTL w) | SOME vs => INL vs` >>
  Cases_on `OWHILE ISL g (INL vars)`
  >- simp[] >>
  rename1 `SOME res` >> Cases_on `res`
  >- simp[] >>
  rename1 `SOME (INR result)` >>
  simp[] >>
  `(\s. case s of INL l => MEM v l | INR l => MEM v l) (INR result)` by (
    irule (DB.fetch "While" "OWHILE_INV_IND"
      |> INST_TYPE [alpha |-> ``:string list + string list``]) >>
    qexistsl [`ISL`, `g`, `INL vars`] >> simp[] >>
    rpt strip_tac >> rename1 `ISL xx` >>
    Cases_on `xx` >> gvs[Abbr`g`] >>
    Cases_on `pointer_use_step_step fn x` >> simp[] >>
    gvs[pointer_use_step_step_def, LET_DEF] >>
    rw[] >> simp[]) >>
  gvs[]
QED

(* Every element of pointer_use_step is a PP instruction output *)
Triviality pointer_use_step_pp_output:
  !fn vars v. MEM v (pointer_use_step fn vars) ==>
    ?bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      is_pointer_preserving_op inst.inst_opcode /\ MEM v inst.inst_outputs
Proof
  rw[pointer_use_step_def, MEM_FLAT, MEM_MAP] >>
  rename1 `MEM bb fn.fn_blocks` >>
  qexists `bb` >> simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  rename1 `MEM inst bb.bb_instructions` >>
  qexists `inst` >>
  gvs[] >> BasicProvers.every_case_tac >> gvs[]
QED

(* Stronger: pointer_use_step element also has a Var operand in vars *)
Triviality pointer_use_step_has_var_operand:
  !fn vars v. MEM v (pointer_use_step fn vars) ==>
    ?bb inst v'. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      is_pointer_preserving_op inst.inst_opcode /\ MEM v inst.inst_outputs /\
      MEM (Var v') inst.inst_operands /\ MEM v' vars
Proof
  rw[pointer_use_step_def, MEM_FLAT, MEM_MAP] >>
  rename1 `MEM bb fn.fn_blocks` >>
  qexists `bb` >> simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  rename1 `MEM inst bb.bb_instructions` >>
  qexists `inst` >>
  BasicProvers.every_case_tac >> gvs[EXISTS_MEM] >>
  rename1 `MEM op inst.inst_operands` >>
  Cases_on `op` >> gvs[] >>
  metis_tac[]
QED

(* Non-root members of pointer_use_vars are PP outputs *)
Triviality pointer_use_vars_non_root_pp_output:
  !fn vars v. MEM v (pointer_use_vars fn vars) /\ ~MEM v vars ==>
    ?bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      is_pointer_preserving_op inst.inst_opcode /\ MEM v inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  simp[pointer_use_vars_def] >>
  qpat_x_assum `MEM v (pointer_use_vars fn vars)` mp_tac >>
  simp[pointer_use_vars_def] >>
  qabbrev_tac `g = \w:string list + string list.
    case pointer_use_step_step fn (OUTL w) of
      NONE => INR (OUTL w) | SOME vs => INL vs` >>
  Cases_on `OWHILE ISL g (INL vars)`
  >- simp[] >>
  rename1 `SOME res` >> Cases_on `res`
  >- simp[] >>
  rename1 `SOME (INR result)` >>
  simp[] >> strip_tac >>
  (* Invariant: every non-root member is a PP output *)
  `(\s. case s of
      INL l => !v. MEM v l /\ ~MEM v vars ==>
        ?bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
          is_pointer_preserving_op inst.inst_opcode /\ MEM v inst.inst_outputs
    | INR l => !v. MEM v l /\ ~MEM v vars ==>
        ?bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
          is_pointer_preserving_op inst.inst_opcode /\ MEM v inst.inst_outputs)
   (INR result)` by (
    irule (DB.fetch "While" "OWHILE_INV_IND"
      |> INST_TYPE [alpha |-> ``:string list + string list``]) >>
    qexistsl [`ISL`, `g`, `INL vars`] >> simp[] >>
    rpt strip_tac >> rename1 `ISL xx` >>
    Cases_on `xx` >> gvs[Abbr`g`] >>
    Cases_on `pointer_use_step_step fn x` >> simp[] >>
    gvs[pointer_use_step_step_def, LET_DEF] >>
    rw[] >> simp[] >>
    gvs[MEM_FILTER, MEM_APPEND] >>
    metis_tac[pointer_use_step_pp_output]
  ) >>
  gvs[]
QED

(* Key: pv membership for non-roots implies PP output *)
Triviality pv_non_root_is_pp_output:
  !fn (roots : string set) v.
    FINITE roots /\
    v IN pointer_derived_vars fn roots /\ v NOTIN roots ==>
    ?bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      is_pointer_preserving_op inst.inst_opcode /\ MEM v inst.inst_outputs
Proof
  rw[pointer_derived_vars_def] >>
  `~MEM v (SET_TO_LIST roots)` by simp[MEM_SET_TO_LIST] >>
  metis_tac[pointer_use_vars_non_root_pp_output]
QED

(* If ALL_DISTINCT (FLAT (MAP f l)), same element can't be in two
   different sublists. Generic list fact. *)
Triviality all_distinct_flat_map_cross:
  !f l (x:'a) y (v:'b).
    ALL_DISTINCT (FLAT (MAP f l)) /\
    MEM x l /\ MEM y l /\ x <> y /\
    MEM v (f x) /\ MEM v (f y) ==> F
Proof
  Induct_on `l` >> rw[MEM_FLAT, MEM_MAP, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* fn_insts_blocks is FLAT MAP *)
Triviality fn_insts_blocks_flat:
  !bbs. fn_insts_blocks bbs =
        FLAT (MAP (\bb:basic_block. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* MEM in fn_insts from block membership *)
Triviality MEM_fn_insts:
  !fn bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  rw[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

(* SSA uniqueness: same output var ⇒ same instruction *)
Triviality ssa_unique_output_inst:
  !fn bb1 inst1 bb2 inst2 v.
    ssa_form fn /\
    MEM bb1 fn.fn_blocks /\ MEM inst1 bb1.bb_instructions /\
    MEM v inst1.inst_outputs /\
    MEM bb2 fn.fn_blocks /\ MEM inst2 bb2.bb_instructions /\
    MEM v inst2.inst_outputs ==> inst1 = inst2
Proof
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  gvs[ssa_form_def] >>
  `MEM inst1 (fn_insts fn) /\ MEM inst2 (fn_insts fn)` by
    metis_tac[MEM_fn_insts] >>
  metis_tac[all_distinct_flat_map_cross]
QED

(* amap keys are alloca output variables *)
Definition amap_from_allocas_def:
  amap_from_allocas fn (amap : alloc_map) <=>
    !v. v IN FDOM amap ==>
      ?bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
                is_alloca_op inst.inst_opcode /\ MEM v inst.inst_outputs
End

(* Non-address operands of memory ops are non-pv.
   In Vyper: memory sizes are always constants or non-pointer variables.
   Needed because concretize_rel displaces pointer-derived values, so
   both sides must agree on sizes (TAKE count) for SHA3, MCOPY, etc. *)
Definition mem_size_non_pv_def:
  mem_size_non_pv fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst ops v.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      (mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops) /\
      (ops.iao_size = SOME (Var v) \/ ops.iao_max_size = SOME (Var v)) ==>
      v NOTIN pv
End

(* For memory-writing ops where offset = first operand, non-first-operand
   Var arguments are not pointer-derived.
   Position-based (uses TL) to correctly handle degenerate cases where the
   same pv variable appears in both offset and non-offset positions.
   Covers: MSTORE, MSTORE8, ISTORE, CALLDATACOPY, CODECOPY, DLOADBYTES,
           RETURNDATACOPY (offset is always first operand).
   Does NOT cover: MCOPY (src is also pv), external CALL ops (offset not first).
   Subsumes mem_write_data_non_pv for MSTORE/MSTORE8. *)
Definition mem_write_tail_non_pv_def:
  mem_write_tail_non_pv fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst v.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      IS_SOME (mem_write_ops inst) /\
      MEM (Var v) (TL inst.inst_operands) ==>
      v NOTIN pv
End

(* For MSTORE/MSTORE8, the data operand (second operand) is not pointer-derived.
   Ensures written bytes agree between original and concretized states.
   True for Vyper: MSTORE's value comes from computation, not pointer arithmetic.
   Mirrors mem_size_non_pv but for VALUE operands rather than SIZE operands. *)
Definition mem_write_data_non_pv_def:
  mem_write_data_non_pv fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst v.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      (inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8) /\
      (?addr. inst.inst_operands = [addr; Var v]) ==>
      v NOTIN pv
End

(* Sum of alloca sizes for not-yet-executed ALLOCA instructions.
   Decreases by w2n sz when ALLOCA with inst_id executes fresh;
   unchanged on reuse (inst_id already in vs_allocas) or non-ALLOCA. *)
Definition fn_remaining_alloca_size_def:
  fn_remaining_alloca_size fn s =
    SUM (MAP (\inst. case inst.inst_operands of
                       [Lit sz] => w2n sz
                     | _ => 0)
      (FILTER (\inst. inst.inst_opcode = ALLOCA /\
                      inst.inst_id NOTIN FDOM s.vs_allocas)
        (fn_insts fn)))
End

(* Overflow safety: concrete addresses and alloca offsets don't wrap.
   Key invariant: vs_alloca_next + remaining_alloca_size < dimword.
   After fresh ALLOCA(sz): vs_alloca_next grows by sz, remaining shrinks by sz.
   Sum is constant => invariant preserved.
   Non-ALLOCA: both sides unchanged => trivially preserved. *)
Definition alloca_overflow_safe_def:
  alloca_overflow_safe fn (amap : alloc_map) s <=>
    (* Static: each concrete addr + alloca size fits *)
    (!bb inst out addr sz.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
      inst.inst_outputs = [out] /\ FLOOKUP amap out = SOME addr ==>
      w2n addr + w2n sz < dimword (:256)) /\
    (* Static: alloca sizes are positive *)
    (!bb inst sz.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] ==>
      0 < w2n sz) /\
    (* Dynamic: vs_alloca_next + remaining unexecuted alloca sizes fits *)
    s.vs_alloca_next + fn_remaining_alloca_size fn s < dimword (:256) /\
    (* Memory within alloca region: ensures nao = vs_alloca_next *)
    LENGTH s.vs_memory <= s.vs_alloca_next /\
    (* Per-existing-alloca: concrete addr + runtime size fits, size > 0 *)
    (!aid off sz addr'.
       FLOOKUP s.vs_allocas aid = SOME (off, sz) /\
       alloca_concrete_addr amap fn aid = SOME addr' ==>
       0 < sz /\ w2n addr' + sz < dimword (:256))
End

Definition concrete_allocas_non_overlapping_def:
  concrete_allocas_non_overlapping (amap : alloc_map) fn (s : venom_state) <=>
    !aid1 aid2 off1 sz1 addr1 off2 sz2 addr2.
      aid1 <> aid2 /\
      FLOOKUP s.vs_allocas aid1 = SOME (off1, sz1) /\
      alloca_concrete_addr amap fn aid1 = SOME addr1 /\
      FLOOKUP s.vs_allocas aid2 = SOME (off2, sz2) /\
      alloca_concrete_addr amap fn aid2 = SOME addr2 ==>
      w2n addr1 + sz1 <= w2n addr2 \/ w2n addr2 + sz2 <= w2n addr1
End

(* Runtime alloca size matches static alloca size from instruction definition.
   Invariant: exec_alloca stores (offset, w2n alloc_size) where alloc_size = Lit sz_op.
   get_alloca_size reads w2n sz_op from the same instruction. So they match. *)
Definition alloca_sizes_match_def:
  alloca_sizes_match fn (s : venom_state) <=>
    !aid off sz.
      FLOOKUP s.vs_allocas aid = SOME (off, sz) ==>
      sz = get_alloca_size fn (Allocation aid)
End

(* Non-alloca non-PP outputs are not in pv (under SSA + amap_from_allocas) *)
Triviality non_alloca_non_pp_output_not_pv:
  !fn (amap : alloc_map) bb inst v.
    ssa_form fn /\ amap_from_allocas fn amap /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    MEM v inst.inst_outputs ==>
    v NOTIN pointer_derived_vars fn (FDOM amap)
Proof
  rpt gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  Cases_on `v IN FDOM amap`
  >- (
    fs[amap_from_allocas_def] >>
    res_tac >> metis_tac[ssa_unique_output_inst]
  ) >>
  `FINITE (FDOM amap)` by simp[] >>
  drule pv_non_root_is_pp_output >>
  disch_then drule >>
  simp[] >> strip_tac >>
  metis_tac[ssa_unique_output_inst]
QED

(* Inner fold: keys come from acc or alloca instructions in list *)
Triviality arm_foldl_inst_fdom:
  !insts (result : (allocation, num) fmap) acc v.
    v IN FDOM (FOLDL
      (\amap' inst. if is_alloca_op inst.inst_opcode then
         case inst.inst_outputs of
           [] => amap' | [out] =>
             (case FLOOKUP result (Allocation inst.inst_id) of
                NONE => amap' | SOME pos => amap' |+ (out, n2w pos))
           | _ => amap'
         else amap') acc insts) ==>
    v IN FDOM acc \/
    ?inst. MEM inst insts /\ is_alloca_op inst.inst_opcode /\
           MEM v inst.inst_outputs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`result`,
    `if is_alloca_op h.inst_opcode then
       case h.inst_outputs of
         [] => acc | [out] =>
           (case FLOOKUP result (Allocation h.inst_id) of
              NONE => acc | SOME pos => acc |+ (out, n2w pos))
         | _ => acc
     else acc`, `v`] mp_tac) >>
  simp[] >> strip_tac
  >- (
    BasicProvers.every_case_tac >> gvs[FDOM_FUPDATE] >>
    disj2_tac >> qexists `h` >> simp[])
  >> (disj2_tac >> rename1 `MEM i insts` >>
      qexists `i` >> simp[])
QED

(* Outer fold: keys come from acc or alloca instructions in blocks *)
Triviality arm_foldl_block_fdom:
  !bbs (result : (allocation, num) fmap) acc v.
    v IN FDOM (FOLDL
      (\amap bb. FOLDL
        (\amap' inst. if is_alloca_op inst.inst_opcode then
           case inst.inst_outputs of
             [] => amap' | [out] =>
               (case FLOOKUP result (Allocation inst.inst_id) of
                  NONE => amap' | SOME pos => amap' |+ (out, n2w pos))
             | _ => amap'
           else amap') amap bb.bb_instructions)
      acc bbs) ==>
    v IN FDOM acc \/
    ?bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
              is_alloca_op inst.inst_opcode /\ MEM v inst.inst_outputs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `FOLDL _ inner_acc bbs` >>
  first_x_assum (qspecl_then [`result`, `inner_acc`, `v`] mp_tac) >>
  simp[] >> strip_tac
  >- (simp[Abbr `inner_acc`] >>
      drule arm_foldl_inst_fdom >> strip_tac
      >- metis_tac[]
      >> (disj2_tac >> qexistsl [`h`, `inst`] >> simp[]))
  >> (disj2_tac >> qexistsl [`bb`, `inst`] >> simp[])
QED

(* alloc_result_to_map only inserts keys from alloca instructions *)
Triviality alloc_result_to_map_amap_from_allocas:
  !fn result. amap_from_allocas fn (alloc_result_to_map fn result)
Proof
  rw[amap_from_allocas_def, alloc_result_to_map_def] >>
  drule arm_foldl_block_fdom >> simp[]
QED

(* Non-root members of pointer_use_vars have a pv Var operand *)
Triviality pointer_use_vars_non_root_has_var_operand:
  !fn vars v. MEM v (pointer_use_vars fn vars) /\ ~MEM v vars ==>
    ?bb inst v'. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      is_pointer_preserving_op inst.inst_opcode /\ MEM v inst.inst_outputs /\
      MEM (Var v') inst.inst_operands /\ MEM v' (pointer_use_vars fn vars)
Proof
  rpt gen_tac >> strip_tac >>
  simp[pointer_use_vars_def] >>
  qpat_x_assum `MEM v (pointer_use_vars fn vars)` mp_tac >>
  simp[pointer_use_vars_def] >>
  qabbrev_tac `g = \w:string list + string list.
    case pointer_use_step_step fn (OUTL w) of
      NONE => INR (OUTL w) | SOME vs => INL vs` >>
  Cases_on `OWHILE ISL g (INL vars)`
  >- simp[] >>
  rename1 `SOME res` >> Cases_on `res`
  >- simp[] >>
  rename1 `SOME (INR result)` >>
  simp[] >> strip_tac >>
  (* Invariant: every non-root member has a Var operand in acc *)
  `(\s. case s of
      INL l => !v. MEM v l /\ ~MEM v vars ==>
        ?bb inst v'. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
          is_pointer_preserving_op inst.inst_opcode /\
          MEM v inst.inst_outputs /\
          MEM (Var v') inst.inst_operands /\ MEM v' l
    | INR l => !v. MEM v l /\ ~MEM v vars ==>
        ?bb inst v'. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
          is_pointer_preserving_op inst.inst_opcode /\
          MEM v inst.inst_outputs /\
          MEM (Var v') inst.inst_operands /\ MEM v' l)
   (INR result)` by (
    irule (DB.fetch "While" "OWHILE_INV_IND"
      |> INST_TYPE [alpha |-> ``:string list + string list``]) >>
    qexistsl [`ISL`, `g`, `INL vars`] >> simp[] >>
    rpt strip_tac >> rename1 `ISL xx` >>
    Cases_on `xx` >> gvs[Abbr`g`] >>
    Cases_on `pointer_use_step_step fn x` >> simp[] >>
    gvs[pointer_use_step_step_def, LET_DEF] >>
    rw[] >> simp[] >>
    gvs[MEM_FILTER, MEM_APPEND] >>
    metis_tac[pointer_use_step_has_var_operand, MEM_APPEND]
  ) >>
  gvs[]
QED

(* If output ∈ pv for a pp instruction, some Var operand is in pv.
   Why true: pointer_derived_vars is a fixpoint of pointer_use_step.
   An output enters pv only when pointer_use_step finds a pv Var operand.
   Under SSA, each variable has a unique definition site, so the
   contributing instruction must be our instruction.
   Roots (alloca outputs) can't be pp outputs under SSA. *)
Triviality pp_pv_output_has_pv_operand:
  !fn (amap : alloc_map) bb inst v.
    ssa_form fn /\ amap_from_allocas fn amap /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM v inst.inst_outputs /\
    v IN pointer_derived_vars fn (FDOM amap) ==>
    ?v'. MEM (Var v') inst.inst_operands /\
         v' IN pointer_derived_vars fn (FDOM amap)
Proof
  rpt strip_tac >>
  qabbrev_tac `pv = pointer_derived_vars fn (FDOM amap)` >>
  qabbrev_tac `roots = SET_TO_LIST (FDOM amap)` >>
  (* Step 1: v ∉ FDOM amap (SSA uniqueness: alloca ≠ pp) *)
  `v NOTIN FDOM amap` by (
    spose_not_then assume_tac >>
    `?bb2 inst2. MEM bb2 fn.fn_blocks /\ MEM inst2 bb2.bb_instructions /\
                 is_alloca_op inst2.inst_opcode /\
                 MEM v inst2.inst_outputs` by
      (fs[amap_from_allocas_def, FLOOKUP_DEF] >> metis_tac[]) >>
    `inst2 = inst` by metis_tac[ssa_unique_output_inst] >>
    gvs[] >> Cases_on `inst.inst_opcode` >>
    fs[is_pointer_preserving_op_def, is_alloca_op_def]
  ) >>
  (* Step 2: v ∉ roots, so fixpoint gave it a Var operand in pv *)
  `~MEM v roots` by simp[Abbr`roots`, MEM_SET_TO_LIST] >>
  `MEM v (pointer_use_vars fn roots)` by
    (simp[Abbr`pv`, pointer_derived_vars_def, Abbr`roots`] >>
     gvs[pointer_derived_vars_def]) >>
  drule_all pointer_use_vars_non_root_has_var_operand >> strip_tac >>
  (* Step 3: SSA uniqueness: the inst from fixpoint = our inst *)
  `inst' = inst` by metis_tac[ssa_unique_output_inst] >>
  gvs[] >>
  qexists `v'` >> simp[] >>
  simp[Abbr`pv`, pointer_derived_vars_def, Abbr`roots`]
QED

Triviality roots_in_pv:
  !fn roots v. FINITE roots /\ v IN roots ==>
    v IN pointer_derived_vars fn roots
Proof
  rw[pointer_derived_vars_def, MEM_SET_TO_LIST] >>
  irule pointer_use_vars_mem >> simp[MEM_SET_TO_LIST]
QED

(* FLOOKUP amap v = SOME x implies v is pointer-derived *)
Triviality flookup_in_pv:
  !fn amap v x. FLOOKUP amap v = SOME x ==>
    v IN pointer_derived_vars fn (FDOM amap)
Proof
  rpt strip_tac >> irule roots_in_pv >>
  simp[FDOM_FINITE] >> gvs[flookup_thm]
QED

(* FIND with inst_id predicate finds the given instruction when ids are distinct *)
Triviality find_by_inst_id:
  !Q l inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) l) /\
    MEM inst l /\ Q inst ==>
    FIND (\i. i.inst_id = inst.inst_id /\ Q i) l = SOME inst
Proof
  gen_tac >>
  Induct >> simp[FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[ALL_DISTINCT_APPEND, MEM_MAP]
QED

(* General membership in fn_insts from block membership *)
Triviality mem_fn_insts:
  !fn bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
               MEM inst (fn_insts fn)
Proof
  rw[fn_insts_def] >>
  `!bbs. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
         MEM inst (fn_insts_blocks bbs)` suffices_by metis_tac[] >>
  Induct >> simp[fn_insts_blocks_def, MEM_APPEND] >> metis_tac[]
QED

(* alloca_concrete_addr connects inst_id to amap via fn_insts *)
Triviality alloca_concrete_addr_from_inst:
  !amap fn inst bb out addr.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_alloca_op inst.inst_opcode /\
    inst.inst_outputs = [out] /\
    FLOOKUP amap out = SOME addr /\
    fn_inst_ids_distinct fn ==>
    alloca_concrete_addr amap fn inst.inst_id = SOME addr
Proof
  rw[alloca_concrete_addr_def] >>
  `MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts] >>
  gvs[fn_inst_ids_distinct_alt] >>
  `FIND (\i. i.inst_id = inst.inst_id /\ is_alloca_op i.inst_opcode)
        (fn_insts fn) = SOME inst` by
    (match_mp_tac (find_by_inst_id |> Q.SPEC `is_alloca_op o inst_opcode`
       |> SIMP_RULE (srw_ss()) []) >> simp[]) >>
  simp[]
QED

(* eval_operand agrees for non-pv operands under CR *)
Triviality cr_eval_operand_non_pv:
  !amap fn livesets init s1 s2.
    concretize_rel amap fn livesets init s1 s2 ==>
    !op. (!v. op = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def] >>
  fs[concretize_rel_def, LET_THM, lookup_var_def]
QED

(* CR preserved by state_equiv on both sides when changed vars are
   non-pv and agree in the result states. Generalizes cr_update_var_non_pv
   to multiple output vars and arbitrary state_equiv transformations.

   Why true: state_equiv says non-changed vars, memory, allocas, scalars
   are unchanged. CR clauses for those carry over. Changed vars are non-pv
   and agree → CR clause 1 holds. CR clause 2 for pv vars: pv vars are
   not in changed set (since changed vars are non-pv), so lookup_var
   agrees with original state where CR held. *)
Triviality cr_state_equiv_non_pv:
  !amap fn livesets init s1 s2 s1' s2' changed.
    concretize_rel amap fn livesets init s1 s2 /\
    state_equiv changed s1 s1' /\
    state_equiv changed s2 s2' /\
    (!v. v IN changed ==>
         v NOTIN pointer_derived_vars fn (FDOM amap) /\
         lookup_var v s1' = lookup_var v s2') ==>
    concretize_rel amap fn livesets init s1' s2'
Proof
  rpt strip_tac >>
  (* Expand state_equiv once, get all equalities *)
  fs[state_equiv_def, execution_equiv_def] >>
  (* Now expand CR for hypothesis and goal *)
  fs[concretize_rel_def, LET_THM,
     allocas_non_overlapping_def, in_alloca_region_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  (* clause 1: non-pv vars *)
  >- (
    Cases_on `v IN changed`
    >- (res_tac >> fs[])
    >> (res_tac >> fs[])
  )
  (* clause 2: pv vars — v NOTIN changed since v IN pv *)
  >- suspend "c2"
  (* clause 3: initialized memory bytes — memory unchanged *)
  >- (res_tac >> fs[])
  (* clause 4: non-alloca memory — memory unchanged *)
  >- (res_tac >> fs[])
  (* clause 5: allocas_non_overlapping — allocas unchanged *)
  >- (res_tac >> fs[])
  (* scalars — all preserved by state_equiv *)
  >> fs[]
QED

Resume cr_state_equiv_non_pv[c2]:
  `v NOTIN changed` by metis_tac[] >>
  `lookup_var v s1 = lookup_var v s1'` by metis_tac[] >>
  `lookup_var v s2 = lookup_var v s2'` by metis_tac[] >>
  qpat_x_assum `lookup_var v s1 = _` (SUBST1_TAC o GSYM) >>
  qpat_x_assum `lookup_var v s2 = _` (SUBST1_TAC o GSYM) >>
  res_tac >> fs[]
QED

Finalise cr_state_equiv_non_pv

Triviality lookup_var_update_var:
  !x y w s.
    lookup_var x (update_var y w s) =
    if x = y then SOME w else lookup_var x s
Proof
  rw[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Triviality in_alloca_region_update_var:
  !s out w i.
    in_alloca_region (update_var out w s) i <=> in_alloca_region s i
Proof
  rw[in_alloca_region_def, update_var_def]
QED

Triviality allocas_non_overlapping_update_var:
  !s out w.
    allocas_non_overlapping (update_var out w s) <=>
    allocas_non_overlapping s
Proof
  rw[allocas_non_overlapping_def, update_var_def]
QED

(* CR preserved by update_var with same value on non-pv output *)
Triviality cr_update_var_non_pv:
  !amap fn livesets init s1 s2 out v.
    concretize_rel amap fn livesets init s1 s2 /\
    out NOTIN pointer_derived_vars fn (FDOM amap) ==>
    concretize_rel amap fn livesets init
      (update_var out v s1) (update_var out v s2)
Proof
  rpt strip_tac >>
  fs[concretize_rel_def, LET_THM, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE, allocas_non_overlapping_def, in_alloca_region_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  TRY (IF_CASES_TAC >> gvs[]) >>
  res_tac >> fs[]
QED

(* Extract alloca bound from alloca_inv: off + sz <= vs_alloca_next *)
Triviality alloca_inv_alloca_bound:
  !s aid off sz.
    alloca_inv s /\
    FLOOKUP s.vs_allocas aid = SOME (off, sz) ==>
    off + sz <= s.vs_alloca_next
Proof
  rw[alloca_inv_def, alloca_next_valid_def] >> res_tac
QED

(* CR preserved by update_var with displaced value on pv output.
   update_var stores SOME val in vs_vars, so lookup_var returns SOME.
   Requires containment: w1 in [orig_off, orig_off+sz). *)
Triviality cr_update_var_pv:
  !amap fn livesets init s1 s2 out w1 w2 aid orig_off sz addr.
    concretize_rel amap fn livesets init s1 s2 /\
    out IN pointer_derived_vars fn (FDOM amap) /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
    w1 - n2w orig_off = w2 - addr /\
    orig_off + sz < dimword (:256) /\
    w2n addr + sz < dimword (:256) ==>
    concretize_rel amap fn livesets init
      (update_var out w1 s1) (update_var out w2 s2)
Proof
  rpt strip_tac >>
  fs[concretize_rel_def, LET_THM] >>
  simp[concretize_rel_def, LET_THM, lookup_var_update_var,
       in_alloca_region_update_var, allocas_non_overlapping_update_var,
       update_var_def] >>
  rpt conj_tac
  >- (
    rpt strip_tac >>
    Cases_on `v = out` >> gvs[] >>
    qpat_x_assum `!v. v NOTIN pointer_derived_vars fn (FDOM amap) ==> _`
      drule >> simp[])
  >- (
    rpt strip_tac >>
    Cases_on `v = out` >> gvs[]
    >- (
      qexistsl_tac [`aid`, `orig_off`, `sz`, `addr`] >>
      simp[]) >>
    qpat_x_assum `!v. v IN pointer_derived_vars fn (FDOM amap) ==> _`
      drule >> simp[])
  >> metis_tac[]
QED

(* CR preserved by update_var on alloca reuse: side1 gets n2w off,
   side2 gets concrete addr. Wraps cr_update_var_pv with zero displacement.
   Requires 0 < sz for containment (off <= off < off + sz). *)
Triviality cr_update_var_alloca_reuse:
  !amap fn livesets init s1 s2 out aid off sz addr.
    concretize_rel amap fn livesets init s1 s2 /\
    out IN pointer_derived_vars fn (FDOM amap) /\
    FLOOKUP s1.vs_allocas aid = SOME (off, sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    0 < sz /\
    off + sz < dimword (:256) /\
    w2n addr + sz < dimword (:256) ==>
    concretize_rel amap fn livesets init
      (update_var out (n2w off) s1) (update_var out addr s2)
Proof
  rpt strip_tac >>
  irule cr_update_var_pv >>
  conj_tac
  >- (qexistsl [`addr`, `aid`, `off`, `sz`] >> simp[WORD_SUB_REFL])
  >> simp[]
QED

(* The exact reuse case goal: all preconditions of concretize_step_alloca_assign
   in the SOME (reuse) branch, conclusion is CR preservation via update_var. *)
Triviality step_alloca_reuse_goal:
  !inst bb amap fn livesets init s1 s2 out addr alloc_size entry0 entry1.
    inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit alloc_size] /\
    inst.inst_outputs = [out] /\
    FLOOKUP amap out = SOME addr /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    alloca_inv s1 /\
    s1.vs_alloca_next < dimword (:256) /\
    w2n addr + w2n alloc_size < dimword (:256) /\
    (!aid off sz addr'.
       FLOOKUP s1.vs_allocas aid = SOME (off, sz) /\
       alloca_concrete_addr amap fn aid = SOME addr' ==>
       0 < sz /\ sz + w2n addr' < dimword (:256)) /\
    concretize_pointer_confined fn amap /\
    concretize_rel amap fn livesets init s1 s2 /\
    FLOOKUP s1.vs_allocas inst.inst_id = SOME (entry0, entry1) ==>
    concretize_rel amap fn livesets init
      (update_var out (n2w entry0) s1) (update_var out addr s2)
Proof
  rpt strip_tac >>
  `is_alloca_op inst.inst_opcode` by simp[is_alloca_op_def] >>
  imp_res_tac alloca_concrete_addr_from_inst >>
  `out IN pointer_derived_vars fn (FDOM amap)` by
    metis_tac[flookup_in_pv] >>
  `0 < entry1 /\ entry1 + w2n addr < dimword (:256)` by
    (first_x_assum
       (qspecl_then [`inst.inst_id`, `entry0`, `entry1`, `addr`] mp_tac) >>
     simp[]) >>
  `entry0 + entry1 < dimword (:256)` by (
    imp_res_tac alloca_inv_alloca_bound >>
    fs[MAX_DEF]) >>
  irule cr_update_var_alloca_reuse >>
  conj_tac >- (qexistsl [`inst.inst_id`, `entry1`] >> simp[])
  >> simp[]
QED

Triviality nao_ge_alloca_end:
  !s aid off sz.
    alloca_inv s /\
    FLOOKUP s.vs_allocas aid = SOME (off, sz) ==>
    off + sz <= s.vs_alloca_next
Proof
  rw[alloca_inv_def, alloca_next_valid_def] >>
  res_tac >> simp[MAX_DEF]
QED

(* Fresh alloca case: side 1 bump-allocates, side 2 assigns concrete addr.
   New alloca at vs_alloca_next doesn't overlap existing because
   alloca_inv ensures off + sz <= vs_alloca_next <= nao. *)
Triviality step_alloca_fresh_goal:
  !inst bb amap fn livesets init s1 s2 out addr alloc_size.
    inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit alloc_size] /\
    inst.inst_outputs = [out] /\
    FLOOKUP amap out = SOME addr /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ssa_form fn /\ fn_inst_ids_distinct fn /\
    alloca_inv s1 /\
    0 < w2n alloc_size /\
    s1.vs_alloca_next + w2n alloc_size < dimword (:256) /\
    w2n addr + w2n alloc_size < dimword (:256) /\
    (!aid off sz addr'.
       FLOOKUP s1.vs_allocas aid = SOME (off, sz) /\
       alloca_concrete_addr amap fn aid = SOME addr' ==>
       0 < sz /\ sz + w2n addr' < dimword (:256)) /\
    concretize_pointer_confined fn amap /\
    concretize_rel amap fn livesets init s1 s2 /\
    FLOOKUP s1.vs_allocas inst.inst_id = NONE ==>
    concretize_rel amap fn livesets (init \\ inst.inst_id)
      (s1 with
       <|vs_vars := s1.vs_vars |+ (out, n2w (s1.vs_alloca_next));
         vs_allocas :=
           s1.vs_allocas |+ (inst.inst_id,
             (s1.vs_alloca_next, w2n alloc_size));
         vs_alloca_next :=
           s1.vs_alloca_next + w2n alloc_size|>)
      (s2 with vs_vars := s2.vs_vars |+ (out, addr))
Proof
  rpt strip_tac >>
  qabbrev_tac `nao = s1.vs_alloca_next` >>
  `is_alloca_op inst.inst_opcode` by simp[is_alloca_op_def] >>
  imp_res_tac alloca_concrete_addr_from_inst >>
  imp_res_tac flookup_in_pv >>
  fs[concretize_rel_def, LET_THM, lookup_var_def, FLOOKUP_UPDATE,
     allocas_non_overlapping_def, in_alloca_region_def] >>
  rpt conj_tac
  >- suspend "c1"
  >- suspend "c2"
  >- suspend "c3"
  >- suspend "c4"
  >- suspend "c5"
  >> simp[]
QED

(* Clause 1: non-pv vars agree *)
Resume step_alloca_fresh_goal[c1]:
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

(* Clause 2: pv vars displacement — extracted as standalone triviality *)
Triviality step_alloca_fresh_c2:
  !amap fn inst out addr nao alloc_size livesets init s1 s2 v.
    FLOOKUP amap out = SOME addr /\
    alloca_concrete_addr amap fn inst.inst_id = SOME addr /\
    FLOOKUP s1.vs_allocas inst.inst_id = NONE /\
    0 < w2n alloc_size /\
    nao + w2n alloc_size < dimword (:256) /\
    w2n addr + w2n alloc_size < dimword (:256) /\
    out IN pointer_derived_vars fn (FDOM amap) /\
    (!v. v IN pointer_derived_vars fn (FDOM amap) ==>
       FLOOKUP s1.vs_vars v = NONE /\ FLOOKUP s2.vs_vars v = NONE \/
       ?w1 w2 aid orig_off sz addr'.
         FLOOKUP s1.vs_allocas aid = SOME (orig_off,sz) /\
         alloca_concrete_addr amap fn aid = SOME addr' /\
         FLOOKUP s1.vs_vars v = SOME w1 /\ FLOOKUP s2.vs_vars v = SOME w2 /\
         orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
         w1 - n2w orig_off = w2 - addr' /\ orig_off + sz < dimword (:256) /\
         sz + w2n addr' < dimword (:256)) /\
    v IN pointer_derived_vars fn (FDOM amap) ==>
    (out <> v /\ FLOOKUP s1.vs_vars v = NONE) /\ out <> v /\
    FLOOKUP s2.vs_vars v = NONE \/
    ?w1 w2 aid orig_off sz addr'.
      (if inst.inst_id = aid then SOME (nao,w2n alloc_size)
       else FLOOKUP s1.vs_allocas aid) = SOME (orig_off,sz) /\
      alloca_concrete_addr amap fn aid = SOME addr' /\
      (if out = v then SOME (n2w nao) else FLOOKUP s1.vs_vars v) = SOME w1 /\
      (if out = v then SOME addr else FLOOKUP s2.vs_vars v) = SOME w2 /\
      orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
      w1 - n2w orig_off = w2 - addr' /\ orig_off + sz < dimword (:256) /\
      sz + w2n addr' < dimword (:256)
Proof
  rpt strip_tac >>
  Cases_on `out = v`
  >- suspend "eq"
  >> suspend "neq"
QED

Resume step_alloca_fresh_c2[eq]:
  gvs[] >>
  qexistsl [`inst.inst_id`, `nao`, `w2n alloc_size`, `addr`] >>
  simp[WORD_SUB_REFL] >>
  simp[]
QED

Resume step_alloca_fresh_c2[neq]:
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  disch_then strip_assume_tac
  >- (disj1_tac >> simp[])
  >> disj2_tac >>
     `aid <> inst.inst_id` by (CCONTR_TAC >> gvs[]) >>
     qexistsl [`w1`, `w2`, `aid`, `orig_off`, `sz`, `addr'`] >>
     simp[]
QED

Finalise step_alloca_fresh_c2

Resume step_alloca_fresh_goal[c2]:
  rpt strip_tac >>
  irule step_alloca_fresh_c2 >> simp[] >> metis_tac[]
QED

(* Clause 3: initialized bytes — new alloca has no init via DOMSUB *)
Resume step_alloca_fresh_goal[c3]:
  rpt strip_tac >>
  Cases_on `aid = inst.inst_id`
  >- gvs[is_initialized_def, DOMSUB_FLOOKUP_THM]
  >> `is_initialized init aid i` by
       gvs[is_initialized_def, DOMSUB_FLOOKUP_THM] >>
     gvs[] >> first_x_assum irule >>
     qexistsl [`aid`, `sz`] >> gvs[]
QED

(* Clause 4: memory outside alloca regions *)
Resume step_alloca_fresh_goal[c4]:
  rpt strip_tac >> first_x_assum irule >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  Cases_on `inst.inst_id = aid` >> gvs[]
QED

(* Clause 5: allocas_non_overlapping *)
Resume step_alloca_fresh_goal[c5]:
  rpt strip_tac >>
  Cases_on `inst.inst_id = a1`
  >- (Cases_on `inst.inst_id = a2`
      >- metis_tac[]
      >- (gvs[] >>
          drule_all nao_ge_alloca_end >> simp[]))
  >- (Cases_on `inst.inst_id = a2`
      >- (gvs[] >>
          drule_all nao_ge_alloca_end >> simp[])
      >- (gvs[] >> metis_tac[]))
QED

Finalise step_alloca_fresh_goal

(* Helper: effect-free ops are not terminators, ext calls, or alloca *)
Triviality is_effect_free_op_classes:
  !op. is_effect_free_op op ==>
       ~is_terminator op /\ ~is_ext_call_op op /\ ~is_alloca_op op
Proof
  Cases >> simp[is_effect_free_op_def, is_terminator_def,
                is_ext_call_op_def, is_alloca_op_def]
QED

(* General: no mem ops + not PP → all Var operands non-pv.
   Subsumes effect_free_non_mem_operands_non_pv. *)
Triviality no_mem_ops_operands_non_pv:
  !inst bb fn roots.
    pointer_confined fn roots /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    mem_write_ops inst = NONE /\
    mem_read_ops inst = NONE ==>
    !v. MEM (Var v) inst.inst_operands ==>
        v NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  fs[pointer_confined_def, LET_THM] >>
  first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
  simp[]
QED

(* Combined: for non-mem, non-pointer-preserving ops, eval_operand agrees
   on all operands by CR + pointer_confined. *)
Triviality cr_non_mem_eval_operand_agree:
  !inst bb amap fn livesets init s1 s2.
    concretize_rel amap fn livesets init s1 s2 /\
    concretize_pointer_confined fn amap /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    mem_write_ops inst = NONE /\
    mem_read_ops inst = NONE ==>
    !op. MEM op inst.inst_operands ==>
         eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >>
  drule cr_eval_operand_non_pv >> disch_then irule >>
  rpt strip_tac >>
  metis_tac[no_mem_ops_operands_non_pv, concretize_pointer_confined_def]
QED

(* Helper: effect-free non-memory non-pp ops have no pv operands *)
Triviality effect_free_non_mem_operands_non_pv:
  !inst bb fn roots.
    pointer_confined fn roots /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_effect_free_op inst.inst_opcode /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    ~is_pointer_preserving_op inst.inst_opcode ==>
    !v. MEM (Var v) inst.inst_operands ==>
        v NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  `mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by
    (Cases_on `inst.inst_opcode` >>
     fs[is_effect_free_op_def, venomEffectsTheory.read_effects_def,
        venomEffectsTheory.empty_effects_def,
        memLocDefsTheory.mem_write_ops_def,
        memLocDefsTheory.mem_read_ops_def]) >>
  metis_tac[no_mem_ops_operands_non_pv]
QED

(* Helper: pointer-preserving ops with non-pv outputs have no pv operands.
   Contrapositive of pointer_confined's third disjunct. *)
Triviality pp_non_pv_output_operands_non_pv:
  !inst bb fn roots.
    pointer_confined fn roots /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_outputs <> [] /\
    (!v. MEM v inst.inst_outputs ==>
         v NOTIN pointer_derived_vars fn roots) ==>
    !v. MEM (Var v) inst.inst_operands ==>
        v NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  fs[pointer_confined_def, LET_THM] >>
  first_x_assum drule_all >>
  strip_tac >> gvs[SUBSET_DEF]
  >- (Cases_on `inst.inst_opcode` >>
      fs[is_pointer_preserving_op_def,
         memLocDefsTheory.mem_write_ops_def])
  >- (Cases_on `inst.inst_opcode` >>
      fs[is_pointer_preserving_op_def,
         memLocDefsTheory.mem_read_ops_def])
  >> Cases_on `inst.inst_outputs` >> gvs[] >> metis_tac[]
QED

(* exec_pureN and exec_readN never return Halt/Abort/IntRet *)
val exec_ok_or_error_thms = let
  open BasicProvers
  fun prove_for def = let
    val t = lhs (concl (SPEC_ALL def))
    val fvs = free_vars t
  in GENL fvs (prove(
    ``(!v. ^t <> Halt v) /\ (!a w. ^t <> Abort a w) /\
      (!l w. ^t <> IntRet l w)``,
    rw[def] >> rpt TOP_CASE_TAC >> simp[])) end
in
  map prove_for
    [exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def]
end;

Triviality exec_result_helpers_not_intret_cml[simp]:
  (!f inst s vals s'. exec_pure1 f inst s <> IntRet vals s') /\
  (!f inst s vals s'. exec_pure2 f inst s <> IntRet vals s') /\
  (!f inst s vals s'. exec_pure3 f inst s <> IntRet vals s') /\
  (!f inst s vals s'. exec_read0 f inst s <> IntRet vals s') /\
  (!f inst s vals s'. exec_read1 f inst s <> IntRet vals s') /\
  (!f inst s vals s'. exec_write2 f inst s <> IntRet vals s') /\
  (!inst s alloc_size vals s'. exec_alloca inst s alloc_size <> IntRet vals s') /\
  (!inst s g a v ao as_ ro rs is_s vals s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> IntRet vals s') /\
  (!inst s g a ao as_ ro rs vals s'.
     exec_delegatecall inst s g a ao as_ ro rs <> IntRet vals s') /\
  (!inst s v off sz salt vals s'.
     exec_create inst s v off sz salt <> IntRet vals s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def, exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Triviality step_inst_base_intret_terminator[local]:
  !inst s vals s'.
    step_inst_base inst s = IntRet vals s' ==>
    is_terminator inst.inst_opcode
Proof
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def]
QED

(* Effect-free ops only return OK or Error *)
Triviality effect_free_step_not_halt_abort_intret:
  !inst s. is_effect_free_op inst.inst_opcode ==>
  (!v. step_inst_base inst s <> Halt v) /\
  (!a w. step_inst_base inst s <> Abort a w) /\
  (!l w. step_inst_base inst s <> IntRet l w)
Proof
  rpt gen_tac >> strip_tac >>
  `~is_terminator inst.inst_opcode` by
    metis_tac[is_effect_free_op_classes] >>
  rpt conj_tac
  >- (spose_not_then strip_assume_tac >>
      drule opcodeClassTheory.step_inst_base_halt_opcodes >>
      strip_tac >> gvs[is_effect_free_op_def])
  >- (spose_not_then strip_assume_tac >>
      drule opcodeClassTheory.step_inst_base_abort_opcodes >>
      strip_tac >> gvs[is_effect_free_op_def]) >>
  spose_not_then strip_assume_tac >>
  drule step_inst_base_intret_terminator >> gvs[]
QED

(* Common effect-free non-pv simulation: given that ALL Var operands
   and ALL outputs are non-pv, both sides compute identically and CR
   is preserved. Used by both pure_non_pv and pointer_preserving
   (non-pv output branch). *)
Triviality concretize_step_effect_free_non_pv:
  !inst amap fn livesets init s1 s2.
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> NOP /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    (!v. MEM (Var v) inst.inst_operands ==>
         v NOTIN pointer_derived_vars fn (FDOM amap)) /\
    (!v. MEM v inst.inst_outputs ==>
         v NOTIN pointer_derived_vars fn (FDOM amap)) /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `~is_terminator inst.inst_opcode /\ ~is_ext_call_op inst.inst_opcode /\
   ~is_alloca_op inst.inst_opcode` by
    metis_tac[is_effect_free_op_classes] >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_effect_free_op_def]) >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2` by (
    rpt strip_tac >>
    drule cr_eval_operand_non_pv >>
    disch_then (qspec_then `op` mp_tac) >>
    (impl_tac >- (simp[] >> rpt strip_tac >> gvs[] >> res_tac)) >>
    simp[]
  ) >>
  `s1.vs_prev_bb = s2.vs_prev_bb /\
   s1.vs_params = s2.vs_params /\
   s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\
   s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_data_section = s2.vs_data_section /\
   s1.vs_labels = s2.vs_labels /\
   s1.vs_code = s2.vs_code /\
   s1.vs_prev_hashes = s2.vs_prev_hashes /\
   s1.vs_returndata = s2.vs_returndata /\
   s1.vs_accounts = s2.vs_accounts /\
   s1.vs_transient = s2.vs_transient /\
   s1.vs_logs = s2.vs_logs /\
   s1.vs_fmp = s2.vs_fmp /\
   s1.vs_initial_fmp = s2.vs_initial_fmp /\
   s1.vs_return_pc_token = s2.vs_return_pc_token` by
    fs[concretize_rel_def, LET_THM] >>
  (* ok_transfer both ways *)
  `!v1. step_inst_base inst s1 = OK v1 ==>
        ?v2. step_inst_base inst s2 = OK v2` by (
    rpt strip_tac >>
    qspecl_then [`inst`, `s1`, `v1`, `s2`]
      mp_tac step_inst_base_ok_transfer >> simp[]
  ) >>
  `!v2. step_inst_base inst s2 = OK v2 ==>
        ?v1. step_inst_base inst s1 = OK v1` by (
    rpt strip_tac >>
    qspecl_then [`inst`, `s2`, `v2`, `s1`]
      mp_tac step_inst_base_ok_transfer >>
    simp[] >> rpt strip_tac >> metis_tac[]
  ) >>
  Cases_on `step_inst_base inst s1` >>
  Cases_on `step_inst_base inst s2` >>
  simp[lift_result_def]
  >- (
    rename1 `step_inst_base inst s1 = OK v1` >>
    rename1 `step_inst_base inst s2 = OK v2` >>
    `Eff_IMMUTABLES NOTIN read_effects inst.inst_opcode` by
      (Cases_on `inst.inst_opcode` >>
       gvs[is_effect_free_op_def, venomEffectsTheory.read_effects_def,
           venomEffectsTheory.all_effects_def,
           venomEffectsTheory.empty_effects_def]) >>
    `!v. MEM v inst.inst_outputs ==>
         lookup_var v v1 = lookup_var v v2` by (
      `inst.inst_opcode <> PHI` by
        (CCONTR_TAC >>
         `inst.inst_opcode = PHI` by metis_tac[] >>
         qpat_x_assum `step_inst_base inst s1 = OK v1` mp_tac >>
         simp[step_inst_base_def]) >>
      qspecl_then [`inst`, `s1`, `s2`, `v1`, `v2`]
        mp_tac step_inst_base_effect_free_output_determined_vars >>
      simp[]
    ) >>
    `state_equiv (set inst.inst_outputs) s1 v1` by (
      `step_inst ARB ARB inst s1 = OK v1` by
        simp[step_inst_non_invoke] >>
      metis_tac[venomInstPropsTheory.step_effect_free_state_equiv]
    ) >>
    `state_equiv (set inst.inst_outputs) s2 v2` by (
      `step_inst ARB ARB inst s2 = OK v2` by
        simp[step_inst_non_invoke] >>
      metis_tac[venomInstPropsTheory.step_effect_free_state_equiv]
    ) >>
    irule cr_state_equiv_non_pv >>
    qexistsl [`set inst.inst_outputs`, `s1:venom_state`,
              `s2:venom_state`] >> simp[]
  )
  >> gvs[effect_free_step_not_halt_abort_intret]
QED

(* Per-instruction simulation for effect-free non-memory non-pp ops.
   Operands all non-pv, output non-pv. Both sides compute identically.
   Now just establishes operands-non-pv and delegates to the common helper. *)
Triviality concretize_step_pure_non_pv:
  !inst bb amap fn livesets init s1 s2.
    is_effect_free_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> NOP /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    concretize_pointer_confined fn amap /\
    (!v. MEM v inst.inst_outputs ==>
         v NOTIN pointer_derived_vars fn (FDOM amap)) /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  irule concretize_step_effect_free_non_pv >> simp[] >>
  metis_tac[effect_free_non_mem_operands_non_pv,
            concretize_pointer_confined_def]
QED

(* Pointer-preserving ops (ADD/SUB with pv, PHI, ASSIGN):
   displacement invariant maintained for pv outputs.

   Why true: for ADD with pv operand w1 and non-pv operand c,
   result is w1+c on side 1 and w2+c on side 2. Since
   w1-base1 = w2-base2, we get (w1+c)-base1 = (w2+c)-base2.
   SUB: pv only in first operand (affine_pointer_ops), same reasoning.
   PHI/ASSIGN: direct copy preserves displacement. *)

(* Well-formed PHI + resolve_phi succeeds → result is a Var *)
Triviality phi_resolve_is_var:
  !prev ops val_op.
    phi_well_formed ops /\ resolve_phi prev ops = SOME val_op ==>
    ?v. val_op = Var v
Proof
  Induct_on `ops` using phi_well_formed_ind >>
  rw[phi_well_formed_def, resolve_phi_def] >> gvs[] >> metis_tac[]
QED

Triviality pointer_preserving_no_mem_ops[local]:
  !inst.
    is_pointer_preserving_op inst.inst_opcode ==>
    mem_write_ops inst = NONE /\ mem_read_ops inst = NONE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_pointer_preserving_op_def,
      memLocDefsTheory.mem_write_ops_def,
      memLocDefsTheory.mem_read_ops_def]
QED

(* pp op + pv output + pointer_confined → outputs ⊆ pv *)
Triviality pp_pv_outputs_subset_pv:
  !fn (amap : alloc_map) bb inst.
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_pointer_preserving_op inst.inst_opcode /\
    (?v. MEM v inst.inst_outputs /\
         v IN pointer_derived_vars fn (FDOM amap)) ==>
    set inst.inst_outputs SUBSET pointer_derived_vars fn (FDOM amap) /\
    ?v'. MEM (Var v') inst.inst_operands /\
         v' IN pointer_derived_vars fn (FDOM amap)
Proof
  rpt strip_tac
  >- (drule_all pp_pv_output_has_pv_operand >> strip_tac >>
      fs[concretize_pointer_confined_def, pointer_confined_def, LET_THM] >>
      qpat_x_assum `!bb inst v. _`
        (qspecl_then [`bb`, `inst`, `v'`] mp_tac) >>
      simp[] >> strip_tac >>
      drule pointer_preserving_no_mem_ops >> strip_tac >>
      gvs[]) >>
  drule_all pp_pv_output_has_pv_operand >> simp[]
QED

(* Word displacement preserved by addition *)
Triviality word_displ_add:
  !(w1:'a word) w2 b1 b2 c.
    w1 - b1 = w2 - b2 ==> (w1 + c) - b1 = (w2 + c) - b2
Proof
  rw[wordsTheory.word_sub_def] >>
  metis_tac[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_ADD_ASSOC]
QED

(* Word displacement preserved by subtraction (SUB uses + -c) *)
Triviality word_displ_neg:
  !(w1:'a word) w2 b1 b2 c.
    w1 - b1 = w2 - b2 ==> (w1 + -c) - b1 = (w2 + -c) - b2
Proof
  rw[wordsTheory.word_sub_def] >>
  metis_tac[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_ADD_ASSOC]
QED

(* CR pv clause: extract displacement + containment for a pv Var *)
Triviality cr_pv_var_displacement:
  !amap fn livesets init s1 s2 v.
    concretize_rel amap fn livesets init s1 s2 /\
    v IN pointer_derived_vars fn (FDOM amap) /\
    lookup_var v s1 <> NONE ==>
    ?w1 w2 aid orig_off sz addr.
      lookup_var v s1 = SOME w1 /\
      lookup_var v s2 = SOME w2 /\
      FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
      alloca_concrete_addr amap fn aid = SOME addr /\
      orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
      w1 - n2w orig_off = w2 - addr /\
      orig_off + sz < dimword (:256) /\
      w2n addr + sz < dimword (:256)
Proof
  rw[concretize_rel_def, LET_THM] >> res_tac >> gvs[] >> metis_tac[]
QED

(* CR pv clause: if pv var is NONE on s1, it's NONE on s2 *)
Triviality cr_pv_var_none:
  !amap fn livesets init s1 s2.
    concretize_rel amap fn livesets init s1 s2 ==>
    !v. v IN pointer_derived_vars fn (FDOM amap) ==>
    lookup_var v s1 = NONE ==>
    lookup_var v s2 = NONE
Proof
  rw[concretize_rel_def, LET_THM] >> res_tac >> gvs[]
QED

Triviality exec_pure2_empty_outputs_error:
  !f inst s. inst.inst_outputs = [] ==>
    ?e. exec_pure2 f inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >> simp[exec_pure2_def] >>
  Cases_on `t` >> simp[exec_pure2_def] >>
  Cases_on `t'` >> simp[exec_pure2_def] >>
  Cases_on `eval_operand h s` >> simp[exec_pure2_def] >>
  Cases_on `eval_operand h' s` >> simp[exec_pure2_def]
QED

Triviality pp_empty_outputs_error:
  !inst s. is_pointer_preserving_op inst.inst_opcode /\
           inst.inst_outputs = [] ==>
           ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_pointer_preserving_op_def] >>
  simp[step_inst_base_def] >>
  qpat_x_assum `inst.inst_outputs = []`
    (fn th => PURE_REWRITE_TAC[exec_pure2_def, th]) >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[]
QED

(* Helper: binary pv op, Case 1: first operand is pv Var *)
Triviality add_pv_case1:
  !amap fn livesets init s1 s2 v' op2 h t bb inst.
    concretize_rel amap fn livesets init s1 s2 /\
    v' IN pointer_derived_vars fn (FDOM amap) /\
    (!v2. op2 = Var v2 ==> v2 NOTIN pointer_derived_vars fn (FDOM amap)) /\
    h IN pointer_derived_vars fn (FDOM amap) /\
    set t SUBSET pointer_derived_vars fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = ADD /\ inst.inst_operands = [Var v'; op2] /\
    inst.inst_outputs = h::t /\
    pointer_arith_in_region fn (FDOM amap) ==>
    lift_result (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (case eval_operand (Var v') s1 of
         NONE => Error "undefined operand"
       | SOME v1 =>
         case eval_operand op2 s1 of
           NONE => Error "undefined operand"
         | SOME v2 =>
           case t of
             [] => OK (update_var h (v1 + v2) s1)
           | v8::v9 => Error "pure2 requires single output")
      (case eval_operand (Var v') s2 of
         NONE => Error "undefined operand"
       | SOME v1 =>
         case eval_operand op2 s2 of
           NONE => Error "undefined operand"
         | SOME v2 =>
           case t of
             [] => OK (update_var h (v1 + v2) s2)
           | v8::v9 => Error "pure2 requires single output")
Proof
  rpt strip_tac >>
  `eval_operand op2 s1 = eval_operand op2 s2` by (
    drule cr_eval_operand_non_pv >>
    disch_then (qspec_then `op2` mp_tac) >> simp[]) >>
  simp[eval_operand_def] >>
  Cases_on `lookup_var v' s1`
  >- (`lookup_var v' s2 = NONE` by (
        drule cr_pv_var_none >>
        disch_then (qspec_then `v'` mp_tac) >> simp[]) >>
      simp[lift_result_def]) >>
  rename1 `lookup_var v' s1 = SOME w1` >>
  `lookup_var v' s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
  Cases_on `eval_operand op2 s2` >> simp[lift_result_def] >>
  Cases_on `t` >> simp[lift_result_def] >>
  irule cr_update_var_pv >> asm_rewrite_tac[] >>
  qexistsl [`addr`, `aid`, `orig_off`, `sz`] >>
  simp[] >>
  (* containment from pointer_arith_in_region *)
  `orig_off <= w2n (w1 + x) /\ w2n (w1 + x) < orig_off + sz` by (
    fs[pointer_arith_in_region_def, LET_THM] >>
    first_x_assum (qspecl_then
      [`bb`, `inst`, `s1`, `update_var h (w1 + x) s1`,
       `h`, `w1 + x`, `v'`, `w1`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[is_pointer_preserving_op_def,
         step_inst_base_def, exec_pure2_def, eval_operand_def,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  ) >>
  simp[] >> metis_tac[word_displ_add]
QED

(* Helper: binary pv op, Case 2: second operand is pv Var *)
Triviality add_pv_case2:
  !amap fn livesets init s1 s2 v' op1 h t bb inst.
    concretize_rel amap fn livesets init s1 s2 /\
    v' IN pointer_derived_vars fn (FDOM amap) /\
    (!v1. op1 = Var v1 ==> v1 NOTIN pointer_derived_vars fn (FDOM amap)) /\
    h IN pointer_derived_vars fn (FDOM amap) /\
    set t SUBSET pointer_derived_vars fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = ADD /\ inst.inst_operands = [op1; Var v'] /\
    inst.inst_outputs = h::t /\
    pointer_arith_in_region fn (FDOM amap) ==>
    lift_result (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (case eval_operand op1 s1 of
         NONE => Error "undefined operand"
       | SOME v1 =>
         case eval_operand (Var v') s1 of
           NONE => Error "undefined operand"
         | SOME v2 =>
           case t of
             [] => OK (update_var h (v1 + v2) s1)
           | v8::v9 => Error "pure2 requires single output")
      (case eval_operand op1 s2 of
         NONE => Error "undefined operand"
       | SOME v1 =>
         case eval_operand (Var v') s2 of
           NONE => Error "undefined operand"
         | SOME v2 =>
           case t of
             [] => OK (update_var h (v1 + v2) s2)
           | v8::v9 => Error "pure2 requires single output")
Proof
  rpt strip_tac >>
  `eval_operand op1 s1 = eval_operand op1 s2` by (
    drule cr_eval_operand_non_pv >>
    disch_then (qspec_then `op1` mp_tac) >> simp[]) >>
  simp[eval_operand_def] >>
  Cases_on `lookup_var v' s1`
  >- (`lookup_var v' s2 = NONE` by (
        drule cr_pv_var_none >>
        disch_then (qspec_then `v'` mp_tac) >> simp[]) >>
      Cases_on `eval_operand op1 s2` >> simp[lift_result_def]) >>
  rename1 `lookup_var v' s1 = SOME w1` >>
  `lookup_var v' s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
  Cases_on `eval_operand op1 s2` >> simp[lift_result_def] >>
  Cases_on `t` >> simp[lift_result_def] >>
  irule cr_update_var_pv >> asm_rewrite_tac[] >>
  qexistsl [`addr`, `aid`, `orig_off`, `sz`] >>
  simp[] >>
  (* containment from pointer_arith_in_region *)
  `orig_off <= w2n (x + w1) /\ w2n (x + w1) < orig_off + sz` by (
    fs[pointer_arith_in_region_def, LET_THM] >>
    first_x_assum (qspecl_then
      [`bb`, `inst`, `s1`, `update_var h (x + w1) s1`,
       `h`, `x + w1`, `v'`, `w1`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[is_pointer_preserving_op_def,
         step_inst_base_def, exec_pure2_def, eval_operand_def,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  ) >>
  simp[] >> metis_tac[word_displ_add, WORD_ADD_COMM]
QED

(* Helper: binary pv op, SUB case: first operand is pv Var *)
Triviality sub_pv_case:
  !amap fn livesets init s1 s2 v' op2 h t bb inst.
    concretize_rel amap fn livesets init s1 s2 /\
    v' IN pointer_derived_vars fn (FDOM amap) /\
    (!v2. op2 = Var v2 ==> v2 NOTIN pointer_derived_vars fn (FDOM amap)) /\
    h IN pointer_derived_vars fn (FDOM amap) /\
    set t SUBSET pointer_derived_vars fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = SUB /\ inst.inst_operands = [Var v'; op2] /\
    inst.inst_outputs = h::t /\
    pointer_arith_in_region fn (FDOM amap) ==>
    lift_result (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (case eval_operand (Var v') s1 of
         NONE => Error "undefined operand"
       | SOME v1 =>
         case eval_operand op2 s1 of
           NONE => Error "undefined operand"
         | SOME v2 =>
           case t of
             [] => OK (update_var h (v1 - v2) s1)
           | v8::v9 => Error "pure2 requires single output")
      (case eval_operand (Var v') s2 of
         NONE => Error "undefined operand"
       | SOME v1 =>
         case eval_operand op2 s2 of
           NONE => Error "undefined operand"
         | SOME v2 =>
           case t of
             [] => OK (update_var h (v1 - v2) s2)
           | v8::v9 => Error "pure2 requires single output")
Proof
  rpt strip_tac >>
  `eval_operand op2 s1 = eval_operand op2 s2` by (
    drule cr_eval_operand_non_pv >>
    disch_then (qspec_then `op2` mp_tac) >> simp[]) >>
  simp[eval_operand_def] >>
  Cases_on `lookup_var v' s1`
  >- (`lookup_var v' s2 = NONE` by (
        drule cr_pv_var_none >>
        disch_then (qspec_then `v'` mp_tac) >> simp[]) >>
      simp[lift_result_def]) >>
  rename1 `lookup_var v' s1 = SOME w1` >>
  `lookup_var v' s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
  Cases_on `eval_operand op2 s2` >> simp[lift_result_def] >>
  Cases_on `t` >> simp[lift_result_def] >>
  irule cr_update_var_pv >> asm_rewrite_tac[] >>
  qexistsl [`addr`, `aid`, `orig_off`, `sz`] >>
  simp[] >>
  (* containment from pointer_arith_in_region *)
  `orig_off <= w2n (w1 - x) /\ w2n (w1 - x) < orig_off + sz` by (
    fs[pointer_arith_in_region_def, LET_THM] >>
    first_x_assum (qspecl_then
      [`bb`, `inst`, `s1`, `update_var h (w1 - x) s1`,
       `h`, `w1 - x`, `v'`, `w1`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[is_pointer_preserving_op_def,
         step_inst_base_def, exec_pure2_def, eval_operand_def,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE]
  ) >>
  simp[] >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  REWRITE_TAC[GSYM word_sub_def] >>
  rpt strip_tac >>
  drule word_displ_neg >> disch_then (qspec_then `x` mp_tac) >>
  simp[word_sub_def]
QED

Triviality concretize_step_pointer_preserving:
  !inst bb amap fn livesets init s1 s2.
    is_pointer_preserving_op inst.inst_opcode /\
    inst.inst_opcode <> NOP /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `is_effect_free_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >>
     fs[is_pointer_preserving_op_def, is_effect_free_op_def]) >>
  `~is_terminator inst.inst_opcode /\ ~is_ext_call_op inst.inst_opcode /\
   ~is_alloca_op inst.inst_opcode` by
    metis_tac[is_effect_free_op_classes] >>
  `Eff_MEMORY NOTIN read_effects inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >>
     fs[is_pointer_preserving_op_def,
        venomEffectsTheory.read_effects_def,
        venomEffectsTheory.empty_effects_def]) >>
  qabbrev_tac `pv = pointer_derived_vars fn (FDOM amap)` >>
  (* Split on empty vs non-empty outputs *)
  Cases_on `inst.inst_outputs`
  >- (
    (* Empty outputs: all pp ops return Error on [] outputs *)
    `(?e. step_inst_base inst s1 = Error e) /\
     (?e. step_inst_base inst s2 = Error e)` by
      (conj_tac >> irule pp_empty_outputs_error >> simp[]) >>
    gvs[lift_result_def]
  ) >>
  (* Non-empty outputs. Split: all non-pv, or some pv? *)
  Cases_on `!v. MEM v (h::t) ==> v NOTIN pv`
  >- (
    (* non_pv_output case *)
    qunabbrev_tac `pv` >>
    `!v. MEM (Var v) inst.inst_operands ==>
         v NOTIN pointer_derived_vars fn (FDOM amap)` by (
      rpt strip_tac >>
      spose_not_then assume_tac >>
      `pointer_confined fn (FDOM amap)` by
        fs[concretize_pointer_confined_def] >>
      fs[pointer_confined_def, LET_THM] >>
      first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >> simp[] >>
      strip_tac >> gvs[SUBSET_DEF]
      >- (Cases_on `inst.inst_opcode` >>
          fs[is_pointer_preserving_op_def,
             memLocDefsTheory.mem_write_ops_def])
      >- (Cases_on `inst.inst_opcode` >>
          fs[is_pointer_preserving_op_def,
             memLocDefsTheory.mem_read_ops_def])
      >> metis_tac[MEM]
    ) >>
    irule concretize_step_effect_free_non_pv >> asm_rewrite_tac[]
  ) >>
  (* Some output is pv. Get pv subset + pv Var operand *)
  pop_assum mp_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_pointer_preserving_op_def] >>
  disch_tac
  >- (
    (* ADD pv case *)
    qunabbrev_tac `pv` >>
    `set inst.inst_outputs SUBSET pointer_derived_vars fn (FDOM amap) /\
     ?v'. MEM (Var v') inst.inst_operands /\
          v' IN pointer_derived_vars fn (FDOM amap)` by (
      irule pp_pv_outputs_subset_pv >>
      simp[is_pointer_preserving_op_def] >>
      qpat_x_assum `∃v. _` mp_tac >> simp[] >> metis_tac[MEM]
    ) >>
    qpat_x_assum `∃v. _` kall_tac >>
    asm_rewrite_tac[step_inst_base_def] >>
    simp[exec_pure2_def] >>
    Cases_on `inst.inst_operands`
    >- simp[lift_result_def] >>
    rename1 `inst.inst_operands = op1::rest1` >>
    Cases_on `rest1`
    >- simp[lift_result_def] >>
    rename1 `inst.inst_operands = op1::op2::rest2` >>
    reverse (Cases_on `rest2`)
    >- simp[lift_result_def] >>
    simp[] >>
    (* affine_pointer_ops: not both pv *)
    `~(?v1 v2. op1 = Var v1 /\ op2 = Var v2 /\
        v1 IN pointer_derived_vars fn (FDOM amap) /\
        v2 IN pointer_derived_vars fn (FDOM amap))` by (
      fs[affine_pointer_ops_def, LET_THM] >>
      first_x_assum (qspecl_then [`bb`, `inst`, `op1`, `op2`] mp_tac) >>
      simp[]
    ) >>
    `MEM (Var v') [op1; op2]` by simp[] >>
    fs[MEM] >> gvs[]
    >- (irule add_pv_case1 >> simp[] >>
        fs[SUBSET_DEF] >> metis_tac[])
    >- (irule add_pv_case2 >> simp[] >>
        fs[SUBSET_DEF] >> metis_tac[])
  )
  >- (
    (* SUB pv case *)
    qunabbrev_tac `pv` >>
    `set inst.inst_outputs SUBSET pointer_derived_vars fn (FDOM amap) /\
     ?v'. MEM (Var v') inst.inst_operands /\
          v' IN pointer_derived_vars fn (FDOM amap)` by (
      irule pp_pv_outputs_subset_pv >>
      simp[is_pointer_preserving_op_def] >>
      qpat_x_assum `∃v. _` mp_tac >> simp[] >> metis_tac[MEM]
    ) >>
    qpat_x_assum `∃v. _` kall_tac >>
    asm_rewrite_tac[step_inst_base_def] >>
    simp[exec_pure2_def] >>
    Cases_on `inst.inst_operands`
    >- simp[lift_result_def] >>
    rename1 `inst.inst_operands = op1::rest1` >>
    Cases_on `rest1`
    >- simp[lift_result_def] >>
    rename1 `inst.inst_operands = op1::op2::rest2` >>
    reverse (Cases_on `rest2`)
    >- simp[lift_result_def] >>
    simp[] >>
    `!u. op2 = Var u ==> u NOTIN pointer_derived_vars fn (FDOM amap)` by (
      rpt strip_tac >>
      fs[affine_pointer_ops_def, LET_THM] >>
      first_x_assum (qspecl_then [`bb`, `inst`, `op1`, `op2`] mp_tac) >>
      simp[]
    ) >>
    `MEM (Var v') [op1; op2]` by simp[] >>
    fs[MEM] >> gvs[] >>
    irule sub_pv_case >> simp[] >> metis_tac[]
  )
  >- (
    (* PHI pv case: sequential PHI execution is impossible under final semantics. *)
    simp[step_inst_base_def, lift_result_def]
  )
  >- (
    (* ASSIGN pv case *)
    qunabbrev_tac `pv` >>
    `set inst.inst_outputs SUBSET pointer_derived_vars fn (FDOM amap) /\
     ?v'. MEM (Var v') inst.inst_operands /\
          v' IN pointer_derived_vars fn (FDOM amap)` by (
      irule pp_pv_outputs_subset_pv >>
      simp[is_pointer_preserving_op_def] >>
      qpat_x_assum `∃v. _` mp_tac >> simp[] >> metis_tac[MEM]
    ) >>
    asm_rewrite_tac[step_inst_base_def] >>
    Cases_on `inst.inst_operands`
    >- simp[lift_result_def] >>
    rename1 `inst.inst_operands = op1::ops` >>
    Cases_on `ops`
    >- (
      Cases_on `t` >> simp[lift_result_def, eval_operand_def] >>
      Cases_on `op1` >> gvs[lift_result_def, eval_operand_def]
      >- (
        rename1 `lookup_var pv_v s1` >>
        `pv_v IN pointer_derived_vars fn (FDOM amap)` by metis_tac[MEM] >>
        Cases_on `lookup_var pv_v s1`
        >- (`lookup_var pv_v s2 = NONE` by (
              drule cr_pv_var_none >>
              disch_then (qspec_then `pv_v` mp_tac) >> simp[]) >>
            simp[lift_result_def]) >>
        rename1 `lookup_var pv_v s1 = SOME w1` >>
        `lookup_var pv_v s1 <> NONE` by simp[] >>
        drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
        simp[lift_result_def] >>
        irule cr_update_var_pv >> asm_rewrite_tac[] >>
        qexistsl [`addr`, `aid`, `orig_off`, `sz`] >> simp[])
      >> metis_tac[MEM])
    >> (Cases_on `t` >> simp[lift_result_def])
  )
QED

(* General CR frame: if t1, t2 agree on all fields CR tracks and carry
   forward vars/memory/allocas from s1, s2 resp., then CR transfers. *)
Triviality concretize_rel_frame:
  !amap fn livesets init s1 s2 t1 t2.
    concretize_rel amap fn livesets init s1 s2 /\
    t1.vs_vars = s1.vs_vars /\ t2.vs_vars = s2.vs_vars /\
    t1.vs_memory = s1.vs_memory /\ t2.vs_memory = s2.vs_memory /\
    t1.vs_allocas = s1.vs_allocas /\
    t1.vs_current_bb = s1.vs_current_bb /\
    (t1.vs_halted <=> t2.vs_halted) /\
    t1.vs_returndata = t2.vs_returndata /\
    t1.vs_accounts = t2.vs_accounts /\
    t1.vs_transient = t2.vs_transient /\
    t1.vs_call_ctx = t2.vs_call_ctx /\
    t1.vs_tx_ctx = t2.vs_tx_ctx /\
    t1.vs_block_ctx = t2.vs_block_ctx /\
    t1.vs_logs = t2.vs_logs /\
    t1.vs_data_section = t2.vs_data_section /\
    t1.vs_labels = t2.vs_labels /\
    t1.vs_code = t2.vs_code /\
    t1.vs_params = t2.vs_params /\
    t1.vs_prev_bb = t2.vs_prev_bb /\
    t1.vs_current_bb = t2.vs_current_bb /\
    t1.vs_prev_hashes = t2.vs_prev_hashes /\
    t1.vs_fmp = t2.vs_fmp /\
    t1.vs_call_entry_fmp = t2.vs_call_entry_fmp /\
    t1.vs_initial_fmp = t2.vs_initial_fmp /\
    t1.vs_return_pc_token = t2.vs_return_pc_token ==>
    concretize_rel amap fn livesets init t1 t2
Proof
  rpt strip_tac >>
  fs[concretize_rel_def, LET_THM, lookup_var_def,
     allocas_non_overlapping_def, in_alloca_region_def,
     in_concrete_region_def, mem_byte_at_def] >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> fs[]
QED

(* Replacing the free-memory pointer by the same value on both sides
   preserves the concretization relation. *)
Triviality concretize_rel_update_fmp_same:
  !amap fn livesets init s1 s2 fmp.
    concretize_rel amap fn livesets init s1 s2 ==>
    concretize_rel amap fn livesets init
      (s1 with vs_fmp := fmp) (s2 with vs_fmp := fmp)
Proof
  rpt strip_tac >>
  fs[concretize_rel_def, LET_THM, lookup_var_def,
     allocas_non_overlapping_def, in_alloca_region_def,
     in_concrete_region_def, mem_byte_at_def] >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> fs[]
QED

Triviality eval_operands_agree:
  !ops s1 s2.
    (!op. MEM op ops ==> eval_operand op s1 = eval_operand op s2) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> rw[eval_operands_def] >>
  first_x_assum (qspecl_then [`s1`, `s2`] mp_tac) >> simp[] >>
  strip_tac >> `eval_operand h s1 = eval_operand h s2` by simp[] >>
  Cases_on `eval_operand h s1` >> simp[] >>
  Cases_on `eval_operands ops s1` >> simp[]
QED


(* DALLOCA updates the FMP and then writes the old FMP to one non-PV output. *)
Triviality concretize_step_dalloca:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = DALLOCA /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by
    simp[memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def] >>
  `~is_pointer_preserving_op inst.inst_opcode` by
    simp[is_pointer_preserving_op_def] >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2` by
    metis_tac[cr_non_mem_eval_operand_agree] >>
  `s1.vs_fmp = s2.vs_fmp` by fs[concretize_rel_def, LET_THM] >>
  Cases_on `inst.inst_operands` >> gvs[step_inst_base_def, lift_result_def] >>
  Cases_on `t` >> gvs[step_inst_base_def, lift_result_def] >>
  Cases_on `inst.inst_outputs` >> gvs[step_inst_base_def, lift_result_def] >>
  Cases_on `t` >> gvs[step_inst_base_def, lift_result_def] >>
  `h' NOTIN pointer_derived_vars fn (FDOM amap)` by
    metis_tac[non_alloca_non_pp_output_not_pv,
              is_pointer_preserving_op_def, is_alloca_op_def, MEM] >>
  Cases_on `eval_operand h s1` >> gvs[step_inst_base_def, lift_result_def] >>
  Cases_on `eval_operand h s2` >> gvs[lift_result_def] >>
  irule cr_update_var_non_pv >> simp[] >>
  irule concretize_rel_update_fmp_same >> simp[]
QED
(* Non-memory, non-ext-call, non-effect-free, non-branch ops:
   Covers SSTORE, TSTORE, and non-branch terminators (STOP, SINK,
   INVALID, SELFDESTRUCT, RET). Operands non-pv, scalar fields agree,
   results related by frame or eval_operands agreement. *)
Triviality concretize_step_non_mem_identity:
  !inst bb amap fn livesets init s1 s2.
    ~is_effect_free_op inst.inst_opcode /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> DALLOCA /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> NOP /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    concretize_pointer_confined fn amap /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  (* Steps 1-3: operand evaluations agree (non-mem, non-pp, pointer_confined) *)
  `mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by (
    Cases_on `inst.inst_opcode` >>
    gvs[is_effect_free_op_def, is_pointer_preserving_op_def,
        is_alloca_op_def, is_ext_call_op_def,
        venomEffectsTheory.read_effects_def,
        venomEffectsTheory.write_effects_def,
        venomEffectsTheory.all_effects_def,
        venomEffectsTheory.empty_effects_def,
        memLocDefsTheory.mem_write_ops_def,
        memLocDefsTheory.mem_read_ops_def]
  ) >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2` by
    metis_tac[cr_non_mem_eval_operand_agree] >>
  (* Step 3b: eval_operands agrees (needed for RET) *)
  `eval_operands inst.inst_operands s1 =
   eval_operands inst.inst_operands s2` by
    (irule eval_operands_agree >> simp[]) >>
  (* Step 4: extract scalar field equalities from CR *)
  `s1.vs_prev_bb = s2.vs_prev_bb /\
   s1.vs_current_bb = s2.vs_current_bb /\
   s1.vs_halted = s2.vs_halted /\
   s1.vs_params = s2.vs_params /\
   s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\
   s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_data_section = s2.vs_data_section /\
   s1.vs_labels = s2.vs_labels /\
   s1.vs_code = s2.vs_code /\
   s1.vs_prev_hashes = s2.vs_prev_hashes /\
   s1.vs_returndata = s2.vs_returndata /\
   s1.vs_accounts = s2.vs_accounts /\
   s1.vs_transient = s2.vs_transient /\
   s1.vs_logs = s2.vs_logs /\
   s1.vs_fmp = s2.vs_fmp /\
   s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
   s1.vs_initial_fmp = s2.vs_initial_fmp /\
   s1.vs_return_pc_token = s2.vs_return_pc_token` by
    fs[concretize_rel_def, LET_THM] >>
  (* Step 5: case split on opcode — SSTORE, TSTORE, STOP, SINK,
     INVALID, SELFDESTRUCT, RET remain (RETURN/REVERT eliminated by
     Eff_MEMORY ∉ read_effects) *)
  Cases_on `inst.inst_opcode` >>
  gvs[is_effect_free_op_def, is_pointer_preserving_op_def,
      is_alloca_op_def, is_ext_call_op_def,
      venomEffectsTheory.read_effects_def,
      venomEffectsTheory.write_effects_def,
      venomEffectsTheory.all_effects_def,
      venomEffectsTheory.empty_effects_def] >>
  (* Expand step_inst_base and case split operands *)
  asm_rewrite_tac[step_inst_base_def] >>
  simp[exec_write2_def, lift_result_def] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
  (* Frame lemma closes all remaining goals *)
  simp[sstore_def, tstore_def, contract_storage_def, contract_transient_def,
       halt_state_def, set_returndata_def, revert_state_def, update_var_def,
       vfmStateTheory.lookup_account_def] >>
  irule concretize_rel_frame >>
  simp[sstore_def, tstore_def, contract_storage_def, contract_transient_def,
       halt_state_def, set_returndata_def, revert_state_def, update_var_def,
       vfmStateTheory.lookup_account_def] >>
  goal_term (fn tm =>
    if is_exists tm then qexistsl [`s1`, `s2`] else all_tac) >>
  simp[]
QED

(* CR preserved through jump_to with FEMPTY init.
   jump_to only changes vs_prev_bb, vs_current_bb, vs_inst_idx.
   Variables, memory, allocas unchanged. Choose FEMPTY to avoid
   liveness issues at the new basic block. *)
Triviality concretize_rel_jump_to:
  !amap fn livesets init lbl s1 s2.
    concretize_rel amap fn livesets init s1 s2 ==>
    concretize_rel amap fn livesets FEMPTY (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[concretize_rel_def, LET_THM, jump_to_def, lookup_var_def,
     allocas_non_overlapping_def, in_alloca_region_def,
     is_initialized_def, FLOOKUP_DEF]
QED

(* Branch terminator simulation: JMP/JNZ/DJMP.
   Operands are Labels (not pv vars by pointer_confined), so both sides
   jump to the same target. *)
Triviality concretize_step_branch_terminator:
  !inst bb amap fn livesets init s1 s2.
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    concretize_pointer_confined fn amap /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets FEMPTY)
      (concretize_rel amap fn livesets FEMPTY)
      (concretize_rel amap fn livesets FEMPTY)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> (
    (* All three: establish eval_operand agreement, expand, case split *)
    `mem_write_ops inst = NONE /\ mem_read_ops inst = NONE /\
     ~is_pointer_preserving_op inst.inst_opcode` by
      simp[memLocDefsTheory.mem_write_ops_def,
           memLocDefsTheory.mem_read_ops_def,
           is_pointer_preserving_op_def] >>
    `!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2` by
      metis_tac[cr_non_mem_eval_operand_agree] >>
    ASM_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
    TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
    TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
    TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
    TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
    TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
    TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
    TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
    TRY BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def] >>
    irule concretize_rel_jump_to >> metis_tac[]
  )
QED

(* ===== Memory Byte Correspondence ===== *)

(* Helper: EL j of the padded-drop expression equals mem_byte_at *)
(* Generalized: EL j from DROP/pad matches mem_byte_at *)
Triviality el_drop_pad_eq_mem_byte_at_gen:
  !mem off j sz.
    j < sz ==>
    EL j (DROP off mem ++ REPLICATE sz (0w:word8)) =
    mem_byte_at mem (off + j)
Proof
  rpt strip_tac >> simp[mem_byte_at_def] >>
  Cases_on `off + j < LENGTH mem`
  >- (simp[rich_listTheory.EL_APPEND1, LENGTH_DROP] >>
      `j < LENGTH mem - off` by simp[] >>
      simp[rich_listTheory.EL_DROP])
  >>
  simp[rich_listTheory.EL_APPEND2, LENGTH_DROP] >>
  simp[rich_listTheory.EL_REPLICATE]
QED

(* If corresponding bytes match, TAKE/DROP/pad produces equal results *)
Triviality take_drop_pad_bytes_eq:
  !mem1 mem2 off1 off2 sz.
    (!j. j < sz ==> mem_byte_at mem1 (off1 + j) =
                     mem_byte_at mem2 (off2 + j)) ==>
    TAKE sz (DROP off1 mem1 ++ REPLICATE sz (0w:word8)) =
    TAKE sz (DROP off2 mem2 ++ REPLICATE sz 0w)
Proof
  rpt strip_tac >>
  irule listTheory.LIST_EQ >>
  simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP] >>
  rpt strip_tac >>
  simp[EL_TAKE, el_drop_pad_eq_mem_byte_at_gen]
QED

Triviality el_drop_pad_eq_mem_byte_at:
  !mem off j.
    j < 32 ==>
    EL j (DROP off mem ++ REPLICATE 32 (0w:word8)) =
    mem_byte_at mem (off + j)
Proof
  metis_tac[el_drop_pad_eq_mem_byte_at_gen]
QED

(* If corresponding bytes match, mload produces equal results *)
Triviality mload_bytes_eq:
  !mem1 mem2 off1 off2.
    (!j. j < 32 ==> mem_byte_at mem1 (off1 + j) =
                     mem_byte_at mem2 (off2 + j)) ==>
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP off1 mem1 ++ REPLICATE 32 0w)) =
    word_of_bytes T 0w
      (TAKE 32 (DROP off2 mem2 ++ REPLICATE 32 0w))
Proof
  rpt strip_tac >>
  `TAKE 32 (DROP off1 mem1 ++ REPLICATE 32 (0w:word8)) =
   TAKE 32 (DROP off2 mem2 ++ REPLICATE 32 0w)` by (
    irule listTheory.LIST_EQ >>
    simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP] >>
    rpt strip_tac >>
    simp[EL_TAKE, el_drop_pad_eq_mem_byte_at]) >>
  simp[]
QED

(* Corollary: mload produces equal results under byte correspondence *)
Triviality mload_mem_byte_eq:
  !off1 off2 s1 s2.
    (!j. j < 32 ==> mem_byte_at s1.vs_memory (off1 + j) =
                     mem_byte_at s2.vs_memory (off2 + j)) ==>
    mload off1 s1 = mload off2 s2
Proof
  rw[mload_def] >> rpt strip_tac >>
  irule mload_bytes_eq >> metis_tac[ADD_COMM]
QED

(* MLOAD: both sides read 32 bytes from displaced addresses.
   Under all_mem_via_pointer, the address operand is pv.
   The output is non-pv (MLOAD is not pointer-preserving).
   Byte correspondence from alloca_write_before_read + alloca_safe_access
   + concretize_rel clause 3. *)
Triviality concretize_step_mload:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = MLOAD /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  (* Extract inst shape from fn_inst_wf *)
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op. inst.inst_operands = [op]` by
    (Cases_on `inst.inst_operands` >> fs[]) >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[]) >>
  (* Address operand is a pv variable (all_mem_via_pointer) *)
  `?v. op = Var v /\ v IN pointer_derived_vars fn (FDOM amap)` by (
    qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
    simp[all_mem_via_pointer_def, LET_THM] >>
    disch_then (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := op; iao_size := SOME (Lit 32w);
          iao_max_size := SOME (Lit 32w) |>`] mp_tac) >>
    simp[memLocDefsTheory.mem_read_ops_def, is_immutable_op_def]) >>
  gvs[] >>
  (* Unfold step_inst_base for MLOAD *)
  simp[step_inst_base_def, exec_read1_def] >>
  (* eval_operand (Var v) = lookup_var v *)
  simp[eval_operand_def] >>
  (* From CR clause 2: lookup_var v agrees or both NONE *)
  `lookup_var v s1 = NONE /\ lookup_var v s2 = NONE \/
   ?w1 w2 aid orig_off sz addr.
     FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
     alloca_concrete_addr amap fn aid = SOME addr /\
     lookup_var v s1 = SOME w1 /\
     lookup_var v s2 = SOME w2 /\
     orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
     w1 - n2w orig_off = w2 - addr /\
     orig_off + sz < dimword (:256) /\
     w2n addr + sz < dimword (:256)` by
    (fs[concretize_rel_def, LET_THM]) >>
  (* NONE case: Error on both sides *)
  Cases_on `lookup_var v s1`
  >- (gvs[] >> simp[lift_result_def]) >>
  gvs[] >> simp[] >>
  suspend "mload_core"
QED

(* Concrete w2n evaluation — dim256 computed at file top via fcpLib *)
Triviality w2n_32w:
  w2n (32w:bytes32) = 32
Proof
  simp[w2n_n2w, dimword_def, dim256]
QED

Triviality w2n_1w:
  w2n (1w:bytes32) = 1
Proof
  simp[w2n_n2w, dimword_def, dim256]
QED

(* Helper: word displacement equation implies nat displacement equation *)
Triviality word_displ_to_nat:
  !w1 w2 (addr:bytes32) orig_off sz.
    w1 - n2w orig_off = w2 - addr /\
    orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
    orig_off + sz < dimword(:256) /\
    w2n addr + sz < dimword(:256) ==>
    w2n addr <= w2n w2 /\
    w2n w1 - orig_off = w2n w2 - w2n addr
Proof
  rpt gen_tac >> strip_tac >>
  `orig_off < dimword(:256)` by simp[] >>
  `w2n (n2w orig_off : bytes32) = orig_off` by simp[w2n_n2w, LESS_MOD] >>
  `n2w orig_off <=+ w1` by simp[WORD_LS] >>
  `w2n (w1 - n2w orig_off) = w2n w1 - w2n (n2w orig_off : bytes32)` by
    (irule word_sub_w2n >> simp[]) >>
  `w2n (w1 - n2w orig_off) = w2n (w2 - addr)` by
    (AP_TERM_TAC >> simp[]) >>
  (* Show addr <=+ w2 by contradiction - suspend for debugging *)
  suspend "addr_le"
QED

Resume word_displ_to_nat[addr_le]:
  `w2n addr <= w2n w2` by (
    spose_not_then assume_tac >>
    `w2n w2 < w2n addr` by simp[] >>
    (* w2n(w2-addr) = (w2n w2 + dimword - w2n addr) MOD dimword *)
    `w2n (w2 - addr) =
     (w2n w2 + (dimword(:256) - w2n addr)) MOD dimword(:256)` by
      simp[word_sub_def, word_2comp_def, word_add_def, w2n_n2w] >>
    (* Since w2n w2 < w2n addr, the sum < dimword, so MOD is identity *)
    `w2n w2 + (dimword(:256) - w2n addr) < dimword(:256)` by simp[w2n_lt] >>
    `w2n (w2 - addr) = w2n w2 + (dimword(:256) - w2n addr)` by
      gvs[LESS_MOD] >>
    (* But w2n w2 + dimword - w2n addr >= dimword - w2n addr > sz *)
    `w2n (w1 - n2w orig_off) < sz` by gvs[LESS_MOD] >>
    simp[]
  ) >>
  `addr <=+ w2` by simp[WORD_LS] >>
  `w2n (w2 - addr) = w2n w2 - w2n addr` by
    (irule word_sub_w2n >> simp[]) >>
  gvs[LESS_MOD]
QED

Finalise word_displ_to_nat

Resume concretize_step_mload[mload_core]:
  simp[lift_result_def] >>
  (* Step 1: alloca_safe_access => w2n w1 + 32 <= orig_off + sz *)
  qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
  simp[alloca_safe_access_def, LET_THM] >>
  strip_tac >>
  pop_assum (qspecl_then
    [`bb`, `inst`,
     `<| iao_ofst := Var v; iao_size := SOME (Lit 32w);
         iao_max_size := SOME (Lit 32w) |>`,
     `v`, `w1`, `Lit (32w:bytes32)`, `32w:bytes32`,
     `aid`, `orig_off`, `sz`] mp_tac) >>
  simp[memLocDefsTheory.mem_read_ops_def, eval_operand_def, w2n_32w] >>
  strip_tac >>
  (* Step 2: alloca_write_before_read => live + initialized *)
  `alloca_live_at livesets aid (s1.vs_current_bb, 0) /\
   (!i. i < sz ==> is_initialized init aid i)` by (
    qpat_x_assum `alloca_write_before_read _ _ _ _ _` mp_tac >>
    simp[alloca_write_before_read_def, LET_THM] >>
    disch_then (qspecl_then [`v`, `w1`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[lookup_var_def]
  ) >>
  (* Step 3: nat displacement via word_displ_to_nat helper *)
  suspend "step3"
QED

Resume concretize_step_mload[step3]:
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by (
    irule word_displ_to_nat >> conj_tac
    >- (qexists `sz` >> simp[])
    >> simp[]
  ) >>
  (* Step 4: byte correspondence => mload equality *)
  suspend "step4"
QED

Resume concretize_step_mload[step4]:
  `mload (w2n w1) s1 = mload (w2n w2) s2` by (
    irule mload_mem_byte_eq >>
    rpt strip_tac >>
    `w2n w1 - orig_off + j < sz` by simp[] >>
    `is_initialized init aid (w2n w1 - orig_off + j)` by simp[] >>
    `mem_byte_at s1.vs_memory ((w2n w1 - orig_off + j) + orig_off) =
     mem_byte_at s2.vs_memory ((w2n w1 - orig_off + j) + w2n addr)` by (
      fs[concretize_rel_def, LET_THM] >>
      first_x_assum (qspecl_then
        [`aid`, `orig_off`, `sz`, `addr`, `w2n w1 - orig_off + j`]
        mp_tac) >>
      simp[]
    ) >>
    `w2n w1 - orig_off + j + orig_off = w2n w1 + j` by simp[] >>
    `w2n w1 - orig_off + j + w2n addr = w2n w2 + j` by simp[] >>
    gvs[]
  ) >>
  (* Step 5: update_var with equal values preserves concretize_rel *)
  gvs[] >>
  `out NOTIN pointer_derived_vars fn (FDOM amap)` by (
    `~is_pointer_preserving_op inst.inst_opcode` by
      simp[is_pointer_preserving_op_def] >>
    metis_tac[non_alloca_non_pp_output_not_pv, is_alloca_op_def, MEM]
  ) >>
  irule cr_update_var_non_pv >> simp[]
QED

Finalise concretize_step_mload

(* ILOAD now reads ordinary memory, so it follows the same displaced-address
   simulation argument as MLOAD. *)
Triviality concretize_step_iload:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = ILOAD /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op. inst.inst_operands = [op]` by
    (Cases_on `inst.inst_operands` >> fs[]) >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[]) >>
  `?v. op = Var v /\ v IN pointer_derived_vars fn (FDOM amap)` by
    (qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
     simp[all_mem_via_pointer_def, LET_THM] >>
     disch_then (qspecl_then [`bb`, `inst`,
       `<| iao_ofst := op; iao_size := SOME (Lit 32w);
           iao_max_size := SOME (Lit 32w) |>`] mp_tac) >>
     simp[memLocDefsTheory.mem_read_ops_def]) >>
  gvs[] >>
  simp[step_inst_base_def, exec_read1_def, eval_operand_def] >>
  `lookup_var v s1 = NONE /\ lookup_var v s2 = NONE \/
   ?w1 w2 aid orig_off sz addr.
     FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
     alloca_concrete_addr amap fn aid = SOME addr /\
     lookup_var v s1 = SOME w1 /\ lookup_var v s2 = SOME w2 /\
     orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
     w1 - n2w orig_off = w2 - addr /\
     orig_off + sz < dimword (:256) /\
     w2n addr + sz < dimword (:256)` by
    fs[concretize_rel_def, LET_THM] >>
  Cases_on `lookup_var v s1`
  >- (gvs[] >> simp[lift_result_def]) >>
  gvs[] >> simp[] >>
  suspend "iload_core"
(* Previous direct proof, retained for reference. It relied on the obsolete
   immutable-map execution semantics.
  `s1.vs_immutables = s2.vs_immutables` by
    fs[concretize_rel_def, LET_THM] >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  `?op. inst.inst_operands = [op]` by
    (Cases_on `inst.inst_operands` >> gvs[inst_wf_def] >>
     Cases_on `t` >> gvs[]) >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> gvs[inst_wf_def] >>
     Cases_on `t` >> gvs[]) >>
  gvs[] >>
  (* Operand non-pv: pointer_confined + is_immutable_op ILOAD *)
  `!v. MEM (Var v) inst.inst_operands ==>
       v NOTIN pointer_derived_vars fn (FDOM amap)` by (
    rpt strip_tac >> spose_not_then assume_tac >>
    fs[concretize_pointer_confined_def] >>
    `pointer_confined fn (FDOM amap)` by simp[] >>
    fs[pointer_confined_def, LET_THM] >>
    first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
    simp[] >>
    rpt strip_tac >> gvs[is_pointer_preserving_op_def, is_immutable_op_def]
  ) >>
  (* Unfold step_inst_base for ILOAD *)
  fs[step_inst_base_def, exec_read1_def] >>
  (* Operand non-pv → eval_operand agrees *)
  `eval_operand op s1 = eval_operand op s2` by (
    Cases_on `op` >> fs[eval_operand_def, lookup_var_def,
                        concretize_rel_def, LET_THM]
  ) >>
  Cases_on `eval_operand op s1` >> gvs[lift_result_def] >>
  (* SOME: both produce OK, same iload value (vs_immutables already equalized by fs) *)
  `MEM out inst.inst_outputs` by simp[] >>
  `~is_alloca_op inst.inst_opcode` by simp[is_alloca_op_def] >>
  `~is_pointer_preserving_op inst.inst_opcode` by
    simp[is_pointer_preserving_op_def] >>
  `out NOTIN pointer_derived_vars fn (FDOM amap)` by
    metis_tac[non_alloca_non_pp_output_not_pv] >>
  `eval_operand op s2 = SOME x` by gvs[] >>
  gvs[lift_result_def] >>
  irule cr_update_var_non_pv >> simp[]
*)
QED

Resume concretize_step_iload[iload_core]:
  simp[lift_result_def] >>
  qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
  simp[alloca_safe_access_def, LET_THM] >>
  strip_tac >>
  pop_assum (qspecl_then
    [`bb`, `inst`,
     `<| iao_ofst := Var v; iao_size := SOME (Lit 32w);
         iao_max_size := SOME (Lit 32w) |>`,
     `v`, `w1`, `Lit (32w:bytes32)`, `32w:bytes32`,
     `aid`, `orig_off`, `sz`] mp_tac) >>
  simp[memLocDefsTheory.mem_read_ops_def, eval_operand_def, w2n_32w] >>
  strip_tac >>
  `alloca_live_at livesets aid (s1.vs_current_bb, 0) /\
   (!i. i < sz ==> is_initialized init aid i)` by (
    qpat_x_assum `alloca_write_before_read _ _ _ _ _` mp_tac >>
    simp[alloca_write_before_read_def, LET_THM] >>
    disch_then (qspecl_then [`v`, `w1`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[lookup_var_def]
  ) >>
  suspend "iload_step3"
QED

Resume concretize_step_iload[iload_step3]:
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by (
    irule word_displ_to_nat >> conj_tac
    >- (qexists `sz` >> simp[])
    >> simp[]
  ) >>
  suspend "iload_step4"
QED

Resume concretize_step_iload[iload_step4]:
  `mload (w2n w1) s1 = mload (w2n w2) s2` by (
    irule mload_mem_byte_eq >>
    rpt strip_tac >>
    `w2n w1 - orig_off + j < sz` by simp[] >>
    `is_initialized init aid (w2n w1 - orig_off + j)` by simp[] >>
    `mem_byte_at s1.vs_memory ((w2n w1 - orig_off + j) + orig_off) =
     mem_byte_at s2.vs_memory ((w2n w1 - orig_off + j) + w2n addr)` by (
      fs[concretize_rel_def, LET_THM] >>
      first_x_assum (qspecl_then
        [`aid`, `orig_off`, `sz`, `addr`, `w2n w1 - orig_off + j`]
        mp_tac) >>
      simp[]
    ) >>
    `w2n w1 - orig_off + j + orig_off = w2n w1 + j` by simp[] >>
    `w2n w1 - orig_off + j + w2n addr = w2n w2 + j` by simp[] >>
    gvs[]
  ) >>
  gvs[] >>
  `out NOTIN pointer_derived_vars fn (FDOM amap)` by (
    `~is_pointer_preserving_op inst.inst_opcode` by
      simp[is_pointer_preserving_op_def] >>
    metis_tac[non_alloca_non_pp_output_not_pv, is_alloca_op_def, MEM]
  ) >>
  irule cr_update_var_non_pv >> simp[]
QED

Finalise concretize_step_iload

(* OBSOLETE direct ISTORE proof, retained for reference. It predates ISTORE's
   executable-memory behavior and is superseded after the MSTORE proof below.
Triviality concretize_step_istore:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = ISTORE /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `s1.vs_immutables = s2.vs_immutables` by
    fs[concretize_rel_def, LET_THM] >>
  `!v. MEM (Var v) inst.inst_operands ==>
       v NOTIN pointer_derived_vars fn (FDOM amap)` by (
    rpt strip_tac >> spose_not_then assume_tac >>
    fs[concretize_pointer_confined_def] >>
    `pointer_confined fn (FDOM amap)` by simp[] >>
    fs[pointer_confined_def, LET_THM] >>
    first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
    simp[] >>
    rpt strip_tac >> gvs[is_pointer_preserving_op_def, is_immutable_op_def]) >>
  fs[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> gvs[lift_result_def] >>
  Cases_on `t` >> gvs[lift_result_def] >>
  Cases_on `t'` >> gvs[lift_result_def] >>
  rename1 `inst.inst_operands = [op_off; op_val]` >>
  `eval_operand op_off s1 = eval_operand op_off s2` by
    (Cases_on `op_off` >> fs[eval_operand_def, lookup_var_def,
                             concretize_rel_def, LET_THM]) >>
  `eval_operand op_val s1 = eval_operand op_val s2` by
    (Cases_on `op_val` >> fs[eval_operand_def, lookup_var_def,
                             concretize_rel_def, LET_THM]) >>
  Cases_on `eval_operand op_off s1` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_val s1` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_off s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand op_val s2` >> gvs[lift_result_def] >>
  fs[concretize_rel_def, LET_THM, lookup_var_def,
     in_alloca_region_def, venomMemDefsTheory.allocas_non_overlapping_def] >>
  metis_tac[]
QED
*)

(* SHA3: both sides hash the same bytes from displaced addresses.
   Offset operand is pv, size operand is non-pv (pointer_confined).
   Byte correspondence from concretize_rel clause 3 + alloca_safe_access.
   Output is non-pv (SHA3 is not pointer-preserving). *)
Triviality concretize_step_sha3:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = SHA3 /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  (* Extract inst shape from fn_inst_wf *)
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `LENGTH inst.inst_operands = 2 /\ LENGTH inst.inst_outputs = 1` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_ofst op_sz. inst.inst_operands = [op_ofst; op_sz]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[] >> Cases_on `t` >> fs[]) >>
  (* Address operand is a pv variable (all_mem_via_pointer) *)
  `?v. op_ofst = Var v /\ v IN pointer_derived_vars fn (FDOM amap)` by (
    qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
    simp[all_mem_via_pointer_def, LET_THM] >>
    disch_then (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := op_ofst; iao_size := SOME op_sz;
          iao_max_size := SOME op_sz |>`] mp_tac) >>
    simp[memLocDefsTheory.mem_read_ops_def, is_immutable_op_def]) >>
  gvs[] >>
  (* Size operand evaluates equally (non-pv via mem_size_non_pv) *)
  suspend "sha3_sz"
QED

Resume concretize_step_sha3[sha3_sz]:
  (* mem_read_ops for SHA3 with known operands *)
  `mem_read_ops inst = SOME <| iao_ofst := Var v; iao_size := SOME op_sz;
      iao_max_size := SOME op_sz |>` by
    simp[memLocDefsTheory.mem_read_ops_def] >>
  (* Size operand non-pv *)
  `!u. op_sz = Var u ==> u NOTIN pointer_derived_vars fn (FDOM amap)` by (
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `mem_size_non_pv _ _` mp_tac >>
    simp[mem_size_non_pv_def, LET_THM] >>
    qexistsl [`bb`, `inst`,
      `<| iao_ofst := Var v; iao_size := SOME (Var u);
          iao_max_size := SOME (Var u) |>`, `u`] >>
    rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >> simp[]) >>
  (* eval_operand agrees for non-pv op_sz *)
  `eval_operand op_sz s1 = eval_operand op_sz s2` by (
    drule cr_eval_operand_non_pv >>
    disch_then (qspec_then `op_sz` mp_tac) >> simp[]) >>
  (* Unfold step_inst_base for SHA3 *)
  simp[step_inst_base_def, eval_operand_def] >>
  Cases_on `lookup_var v s1`
  >- (drule cr_pv_var_none >> disch_then drule >>
      simp[] >> gvs[] >> simp[lift_result_def]) >>
  simp[] >>
  `lookup_var v s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
  simp[eval_operand_def] >>
  Cases_on `eval_operand op_sz s1` >> gvs[lift_result_def] >>
  `?sz_val. eval_operand op_sz s2 = SOME sz_val` by metis_tac[] >> gvs[] >>
  (* alloca_safe_access => w2n w1 + w2n sz_val <= orig_off + sz *)
  `w2n w1 + w2n sz_val <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then
      [`bb`, `inst`,
       `<| iao_ofst := Var v; iao_size := SOME op_sz;
           iao_max_size := SOME op_sz |>`,
       `v`, `w1`, `op_sz`, `sz_val`,
       `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_read_ops_def, lookup_var_def]) >>
  (* write_before_read => live + initialized *)
  `alloca_live_at livesets aid (s1.vs_current_bb, 0) /\
   (!i. i < sz ==> is_initialized init aid i)` by (
    qpat_x_assum `alloca_write_before_read _ _ _ _ _` mp_tac >>
    simp[alloca_write_before_read_def, LET_THM] >>
    disch_then (qspecl_then [`v`, `w1`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[lookup_var_def]) >>
  (* nat displacement via word_displ_to_nat *)
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by (
    irule word_displ_to_nat >> conj_tac
    >- (qexists `sz` >> simp[])
    >> simp[]) >>
  (* Byte correspondence => TAKE/DROP/pad equality *)
  `TAKE (w2n sz_val) (DROP (w2n w1) s1.vs_memory ++ REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n w2) s2.vs_memory ++ REPLICATE (w2n sz_val) 0w)` by (
    irule take_drop_pad_bytes_eq >>
    rpt strip_tac >>
    `w2n w1 - orig_off + j < sz` by simp[] >>
    `is_initialized init aid (w2n w1 - orig_off + j)` by simp[] >>
    `mem_byte_at s1.vs_memory ((w2n w1 - orig_off + j) + orig_off) =
     mem_byte_at s2.vs_memory ((w2n w1 - orig_off + j) + w2n addr)` by (
      fs[concretize_rel_def, LET_THM] >>
      first_x_assum (qspecl_then
        [`aid`, `orig_off`, `sz`, `addr`, `w2n w1 - orig_off + j`]
        mp_tac) >>
      simp[]) >>
    `w2n w1 - orig_off + j + orig_off = w2n w1 + j` by simp[] >>
    `w2n w1 - orig_off + j + w2n addr = w2n w2 + j` by simp[] >>
    gvs[]) >>
  gvs[] >>
  simp[lift_result_def] >>
  (* Output is non-pv *)
  `out NOTIN pointer_derived_vars fn (FDOM amap)` by (
    `~is_pointer_preserving_op inst.inst_opcode` by
      simp[is_pointer_preserving_op_def] >>
    metis_tac[non_alloca_non_pp_output_not_pv, is_alloca_op_def, MEM]) >>
  irule cr_update_var_non_pv >> simp[]
QED

Finalise concretize_step_sha3

(* RETURN/REVERT: memory-reading terminators.
   Same byte correspondence as SHA3, but produce Halt/Abort results.
   concretize_rel_frame establishes CR on the halt state. *)
Triviality concretize_step_return:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = RETURN /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `LENGTH inst.inst_operands = 2 /\ LENGTH inst.inst_outputs = 0` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_ofst op_sz. inst.inst_operands = [op_ofst; op_sz]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) >>
  `?v. op_ofst = Var v /\ v IN pointer_derived_vars fn (FDOM amap)` by (
    qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
    simp[all_mem_via_pointer_def, LET_THM] >>
    disch_then (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := op_ofst; iao_size := SOME op_sz;
          iao_max_size := SOME op_sz |>`] mp_tac) >>
    simp[memLocDefsTheory.mem_read_ops_def, is_immutable_op_def]) >>
  gvs[] >>
  suspend "ret_bytes"
QED

Resume concretize_step_return[ret_bytes]:
  `mem_read_ops inst = SOME <| iao_ofst := Var v; iao_size := SOME op_sz;
      iao_max_size := SOME op_sz |>` by
    simp[memLocDefsTheory.mem_read_ops_def] >>
  `!u. op_sz = Var u ==> u NOTIN pointer_derived_vars fn (FDOM amap)` by (
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `mem_size_non_pv _ _` mp_tac >>
    simp[mem_size_non_pv_def, LET_THM] >>
    qexistsl [`bb`, `inst`,
      `<| iao_ofst := Var v; iao_size := SOME (Var u);
          iao_max_size := SOME (Var u) |>`, `u`] >>
    rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >> simp[]) >>
  `eval_operand op_sz s1 = eval_operand op_sz s2` by (
    drule cr_eval_operand_non_pv >>
    disch_then (qspec_then `op_sz` mp_tac) >> simp[]) >>
  simp[step_inst_base_def, eval_operand_def] >>
  Cases_on `lookup_var v s1`
  >- (drule cr_pv_var_none >> disch_then drule >>
      simp[] >> gvs[] >> simp[lift_result_def]) >>
  simp[] >>
  `lookup_var v s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
  simp[eval_operand_def] >>
  Cases_on `eval_operand op_sz s1` >> gvs[lift_result_def] >>
  `?sz_val. eval_operand op_sz s2 = SOME sz_val` by metis_tac[] >> gvs[] >>
  `w2n w1 + w2n sz_val <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then
      [`bb`, `inst`,
       `<| iao_ofst := Var v; iao_size := SOME op_sz;
           iao_max_size := SOME op_sz |>`,
       `v`, `w1`, `op_sz`, `sz_val`,
       `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_read_ops_def, lookup_var_def]) >>
  `alloca_live_at livesets aid (s1.vs_current_bb, 0) /\
   (!i. i < sz ==> is_initialized init aid i)` by (
    qpat_x_assum `alloca_write_before_read _ _ _ _ _` mp_tac >>
    simp[alloca_write_before_read_def, LET_THM] >>
    disch_then (qspecl_then [`v`, `w1`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[lookup_var_def]) >>
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by (
    irule word_displ_to_nat >> conj_tac
    >- (qexists `sz` >> simp[])
    >> simp[]) >>
  `TAKE (w2n sz_val) (DROP (w2n w1) s1.vs_memory ++ REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n w2) s2.vs_memory ++ REPLICATE (w2n sz_val) 0w)` by (
    irule take_drop_pad_bytes_eq >>
    rpt strip_tac >>
    `w2n w1 - orig_off + j < sz` by simp[] >>
    `is_initialized init aid (w2n w1 - orig_off + j)` by simp[] >>
    `mem_byte_at s1.vs_memory ((w2n w1 - orig_off + j) + orig_off) =
     mem_byte_at s2.vs_memory ((w2n w1 - orig_off + j) + w2n addr)` by (
      fs[concretize_rel_def, LET_THM] >>
      first_x_assum (qspecl_then
        [`aid`, `orig_off`, `sz`, `addr`, `w2n w1 - orig_off + j`]
        mp_tac) >>
      simp[]) >>
    `w2n w1 - orig_off + j + orig_off = w2n w1 + j` by simp[] >>
    `w2n w1 - orig_off + j + w2n addr = w2n w2 + j` by simp[] >>
    gvs[]) >>
  gvs[] >>
  simp[lift_result_def, concretize_rel_def, LET_THM,
       halt_state_def, set_returndata_def, lookup_var_def,
       allocas_non_overlapping_def, in_alloca_region_def,
       in_concrete_region_def, mem_byte_at_def] >>
  qpat_x_assum `concretize_rel _ _ _ _ s1 s2` mp_tac >>
  simp[concretize_rel_def, LET_THM, lookup_var_def,
       allocas_non_overlapping_def, in_alloca_region_def,
       in_concrete_region_def, mem_byte_at_def] >>
  strip_tac >> rpt conj_tac >> gvs[]
QED

Finalise concretize_step_return

Triviality concretize_step_revert:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = REVERT /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `LENGTH inst.inst_operands = 2 /\ LENGTH inst.inst_outputs = 0` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_ofst op_sz. inst.inst_operands = [op_ofst; op_sz]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) >>
  `?v. op_ofst = Var v /\ v IN pointer_derived_vars fn (FDOM amap)` by (
    qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
    simp[all_mem_via_pointer_def, LET_THM] >>
    disch_then (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := op_ofst; iao_size := SOME op_sz;
          iao_max_size := SOME op_sz |>`] mp_tac) >>
    simp[memLocDefsTheory.mem_read_ops_def, is_immutable_op_def]) >>
  gvs[] >>
  suspend "rev_bytes"
QED

Resume concretize_step_revert[rev_bytes]:
  `mem_read_ops inst = SOME <| iao_ofst := Var v; iao_size := SOME op_sz;
      iao_max_size := SOME op_sz |>` by
    simp[memLocDefsTheory.mem_read_ops_def] >>
  `!u. op_sz = Var u ==> u NOTIN pointer_derived_vars fn (FDOM amap)` by (
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `mem_size_non_pv _ _` mp_tac >>
    simp[mem_size_non_pv_def, LET_THM] >>
    qexistsl [`bb`, `inst`,
      `<| iao_ofst := Var v; iao_size := SOME (Var u);
          iao_max_size := SOME (Var u) |>`, `u`] >>
    rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >> simp[]) >>
  `eval_operand op_sz s1 = eval_operand op_sz s2` by (
    drule cr_eval_operand_non_pv >>
    disch_then (qspec_then `op_sz` mp_tac) >> simp[]) >>
  simp[step_inst_base_def, eval_operand_def] >>
  Cases_on `lookup_var v s1`
  >- (drule cr_pv_var_none >> disch_then drule >>
      simp[] >> gvs[] >> simp[lift_result_def]) >>
  simp[] >>
  `lookup_var v s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
  simp[eval_operand_def] >>
  Cases_on `eval_operand op_sz s1` >> gvs[lift_result_def] >>
  `?sz_val. eval_operand op_sz s2 = SOME sz_val` by metis_tac[] >> gvs[] >>
  `w2n w1 + w2n sz_val <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then
      [`bb`, `inst`,
       `<| iao_ofst := Var v; iao_size := SOME op_sz;
           iao_max_size := SOME op_sz |>`,
       `v`, `w1`, `op_sz`, `sz_val`,
       `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_read_ops_def, lookup_var_def]) >>
  `alloca_live_at livesets aid (s1.vs_current_bb, 0) /\
   (!i. i < sz ==> is_initialized init aid i)` by (
    qpat_x_assum `alloca_write_before_read _ _ _ _ _` mp_tac >>
    simp[alloca_write_before_read_def, LET_THM] >>
    disch_then (qspecl_then [`v`, `w1`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[lookup_var_def]) >>
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by (
    irule word_displ_to_nat >> conj_tac
    >- (qexists `sz` >> simp[])
    >> simp[]) >>
  `TAKE (w2n sz_val) (DROP (w2n w1) s1.vs_memory ++ REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n w2) s2.vs_memory ++ REPLICATE (w2n sz_val) 0w)` by (
    irule take_drop_pad_bytes_eq >>
    rpt strip_tac >>
    `w2n w1 - orig_off + j < sz` by simp[] >>
    `is_initialized init aid (w2n w1 - orig_off + j)` by simp[] >>
    `mem_byte_at s1.vs_memory ((w2n w1 - orig_off + j) + orig_off) =
     mem_byte_at s2.vs_memory ((w2n w1 - orig_off + j) + w2n addr)` by (
      fs[concretize_rel_def, LET_THM] >>
      first_x_assum (qspecl_then
        [`aid`, `orig_off`, `sz`, `addr`, `w2n w1 - orig_off + j`]
        mp_tac) >>
      simp[]) >>
    `w2n w1 - orig_off + j + orig_off = w2n w1 + j` by simp[] >>
    `w2n w1 - orig_off + j + w2n addr = w2n w2 + j` by simp[] >>
    gvs[]) >>
  gvs[] >>
  simp[lift_result_def, concretize_rel_def, LET_THM,
       halt_state_def, set_returndata_def, revert_state_def,
       lookup_var_def, allocas_non_overlapping_def,
       in_alloca_region_def, in_concrete_region_def,
       mem_byte_at_def] >>
  qpat_x_assum `concretize_rel _ _ _ _ s1 s2` mp_tac >>
  simp[concretize_rel_def, LET_THM, lookup_var_def,
       allocas_non_overlapping_def, in_alloca_region_def,
       in_concrete_region_def, mem_byte_at_def] >>
  strip_tac >> rpt conj_tac >> gvs[]
QED

Finalise concretize_step_revert

(* ===== Memory write infrastructure ===== *)

(* Helper: LENGTH of expanded memory in write_memory_with_expansion *)
Triviality wmwe_expanded_length:
  !off sz mem.
    off + sz <= LENGTH (if off + sz > LENGTH mem
      then mem ++ REPLICATE (off + sz - LENGTH mem) (0w:word8) else mem)
Proof
  rpt strip_tac >>
  Cases_on `off + sz > LENGTH mem` >>
  simp[LENGTH_APPEND, rich_listTheory.LENGTH_REPLICATE]
QED

(* Helper: mem_byte_at after write_memory_with_expansion, inside write range *)
Triviality mem_byte_at_wmwe_in:
  !off bytes s i.
    off <= i /\ i < off + LENGTH bytes ==>
    mem_byte_at (write_memory_with_expansion off bytes s).vs_memory i =
    EL (i - off) bytes
Proof
  rpt strip_tac >>
  simp[write_memory_with_expansion_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `TAKE off expanded` >>
  `off + LENGTH bytes <= LENGTH expanded` by
    (simp[Abbr `expanded`] >> irule wmwe_expanded_length) >>
  simp[mem_byte_at_def, LENGTH_APPEND, LENGTH_TAKE_EQ,
       LENGTH_DROP, MIN_DEF] >>
  `off <= LENGTH expanded` by simp[] >>
  simp[] >>
  `~(i < off)` by simp[] >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]
QED

(* Helper: byte at index i in write_memory_with_expansion, for i < off *)
Triviality mem_byte_at_wmwe_below:
  !off bytes s i.
    i < off ==>
    mem_byte_at (write_memory_with_expansion off bytes s).vs_memory i =
    mem_byte_at s.vs_memory i
Proof
  rpt strip_tac >>
  simp[write_memory_with_expansion_def, LET_THM, mem_byte_at_def] >>
  Cases_on `off + LENGTH bytes > LENGTH s.vs_memory` >> simp[]
  >- (
    (* expansion case: expanded = mem ++ REPLICATE _ 0w *)
    simp[LENGTH_APPEND, rich_listTheory.LENGTH_REPLICATE,
         LENGTH_TAKE_EQ, LENGTH_DROP, MIN_DEF] >>
    `i < LENGTH s.vs_memory + (off + LENGTH bytes - LENGTH s.vs_memory)` by simp[] >>
    simp[] >>
    `i < MIN off (LENGTH s.vs_memory + (off + LENGTH bytes - LENGTH s.vs_memory))` by
      simp[MIN_DEF] >>
    simp[rich_listTheory.EL_APPEND1] >>
    simp[EL_TAKE] >>
    Cases_on `i < LENGTH s.vs_memory` >>
    simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2,
      rich_listTheory.EL_REPLICATE, rich_listTheory.LENGTH_REPLICATE])
  >> (* no expansion: off + LENGTH bytes <= LENGTH mem *)
  simp[LENGTH_TAKE_EQ, LENGTH_DROP, MIN_DEF, LENGTH_APPEND] >>
  `i < MIN off (LENGTH s.vs_memory)` by simp[MIN_DEF] >>
  simp[rich_listTheory.EL_APPEND1] >>
  simp[EL_TAKE]
QED

(* Helper for wmwe_above: expansion case *)
Triviality mem_byte_at_wmwe_above_exp:
  !off bytes s i.
    off + LENGTH bytes <= i /\
    off + LENGTH bytes > LENGTH s.vs_memory ==>
    mem_byte_at
      (TAKE off (s.vs_memory ++ REPLICATE (off + LENGTH bytes - LENGTH s.vs_memory) 0w) ++
       bytes ++
       DROP (off + LENGTH bytes)
         (s.vs_memory ++ REPLICATE (off + LENGTH bytes - LENGTH s.vs_memory) 0w)) i =
    mem_byte_at s.vs_memory i
Proof
  rpt strip_tac >> simp[mem_byte_at_def]
QED

(* Helper for wmwe_above: no expansion case *)
Triviality mem_byte_at_wmwe_above_noexp:
  !off bytes s i.
    off + LENGTH bytes <= i /\
    off + LENGTH bytes <= LENGTH s.vs_memory ==>
    mem_byte_at
      (TAKE off s.vs_memory ++ bytes ++ DROP (off + LENGTH bytes) s.vs_memory) i =
    mem_byte_at s.vs_memory i
Proof
  rpt strip_tac >> simp[mem_byte_at_def] >>
  Cases_on `i < LENGTH s.vs_memory` >> simp[
    LENGTH_TAKE_EQ, LENGTH_DROP, LENGTH_APPEND, MIN_DEF,
    rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2] >>
  `i - off - LENGTH bytes + (off + LENGTH bytes) = i` by simp[] >>
  simp[EL_DROP]
QED

(* Helper: byte at index i in write_memory_with_expansion, for i >= off + sz *)
Triviality mem_byte_at_wmwe_above:
  !off bytes s i.
    off + LENGTH bytes <= i ==>
    mem_byte_at (write_memory_with_expansion off bytes s).vs_memory i =
    mem_byte_at s.vs_memory i
Proof
  rpt strip_tac >>
  simp[write_memory_with_expansion_def, LET_THM] >>
  Cases_on `off + LENGTH bytes > LENGTH s.vs_memory` >> simp[]
  >- metis_tac[mem_byte_at_wmwe_above_exp]
  >> metis_tac[mem_byte_at_wmwe_above_noexp, DECIDE ``~(a > b:num) ==> a <= b``]
QED

(* Combined: outside write range, byte preserved *)
Triviality mem_byte_at_wmwe_out:
  !off bytes s i.
    i < off \/ off + LENGTH bytes <= i ==>
    mem_byte_at (write_memory_with_expansion off bytes s).vs_memory i =
    mem_byte_at s.vs_memory i
Proof
  metis_tac[mem_byte_at_wmwe_below, mem_byte_at_wmwe_above]
QED

(* CR preservation when only memory changes.
   Variables, allocas, and all non-memory fields are the same.
   Memory byte correspondence must hold for all relevant regions. *)
Triviality concretize_rel_mem_update:
  !amap fn livesets init s1 s2 m1' m2'.
    concretize_rel amap fn livesets init s1 s2 /\
    (* alloca byte correspondence preserved *)
    (!aid orig_off sz addr i.
       FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
       alloca_concrete_addr amap fn aid = SOME addr /\
       alloca_live_at livesets aid (s1.vs_current_bb, 0) /\
       is_initialized init aid i /\ i < sz ==>
       mem_byte_at m1' (orig_off + i) = mem_byte_at m2' (w2n addr + i)) /\
    (* non-alloca byte correspondence preserved *)
    (!i. ~in_alloca_region s1 i /\ ~in_concrete_region amap fn i ==>
         mem_byte_at m1' i = mem_byte_at m2' i) ==>
    concretize_rel amap fn livesets init
      (s1 with vs_memory := m1') (s2 with vs_memory := m2')
Proof
  rpt strip_tac >>
  simp[concretize_rel_def, LET_THM, lookup_var_def,
       allocas_non_overlapping_def] >>
  qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
  simp[concretize_rel_def, LET_THM, lookup_var_def,
       allocas_non_overlapping_def] >>
  rpt strip_tac >>
  fs[concretize_rel_def, LET_THM, lookup_var_def, allocas_non_overlapping_def,
     in_alloca_region_def, in_concrete_region_def, mem_byte_at_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  res_tac >> fs[]
QED

(* mstore is write_memory_with_expansion with word_to_bytes *)
Triviality mstore_as_wmwe:
  !off val s.
    mstore off val s = write_memory_with_expansion off (word_to_bytes val T) s
Proof
  rpt strip_tac >>
  simp[mstore_def, write_memory_with_expansion_def, LET_THM,
       byteTheory.LENGTH_word_to_bytes, dim256]
QED

(* Helper: MSTORE value operand is non-pv *)
Triviality mstore_value_non_pv:
  !fn amap bb inst v_addr v.
    mem_write_tail_non_pv fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = MSTORE /\
    inst.inst_operands = [Var v_addr; Var v] ==>
    v NOTIN pointer_derived_vars fn (FDOM amap)
Proof
  rpt strip_tac >>
  fs[mem_write_tail_non_pv_def, LET_THM] >>
  first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
  simp[memLocDefsTheory.mem_write_ops_def,
       pointerConfinedDefsTheory.is_immutable_op_def]
QED

(* Helper: ISTORE value operand is non-pv *)
Triviality istore_value_non_pv:
  !fn amap bb inst v_addr v.
    mem_write_tail_non_pv fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = ISTORE /\
    inst.inst_operands = [Var v_addr; Var v] ==>
    v NOTIN pointer_derived_vars fn (FDOM amap)
Proof
  rpt strip_tac >>
  fs[mem_write_tail_non_pv_def, LET_THM] >>
  first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
  simp[memLocDefsTheory.mem_write_ops_def]
QED

Triviality mstore8_as_wmwe:
  !off val s.
    mstore8 off val s = write_memory_with_expansion off [w2w val : word8] s
Proof
  rpt strip_tac >>
  simp[mstore8_def, write_memory_with_expansion_def, LET_THM]
QED

(* Helper: MSTORE8 value operand is non-pv *)
Triviality mstore8_value_non_pv:
  !fn amap bb inst v_addr v.
    mem_write_tail_non_pv fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = MSTORE8 /\
    inst.inst_operands = [Var v_addr; Var v] ==>
    v NOTIN pointer_derived_vars fn (FDOM amap)
Proof
  rpt strip_tac >>
  fs[mem_write_tail_non_pv_def, LET_THM] >>
  first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
  simp[memLocDefsTheory.mem_write_ops_def,
       pointerConfinedDefsTheory.is_immutable_op_def]
QED

(* For memory-writing ops with no memory read and not pointer-preserving,
   non-offset Var operands are non-pv.
   Applies to: CALLDATACOPY, CODECOPY, DLOADBYTES, RETURNDATACOPY. *)
Triviality mem_write_non_offset_non_pv:
  !inst bb fn roots ops v.
    pointer_confined fn roots /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    mem_write_ops inst = SOME ops /\
    ~is_immutable_op inst.inst_opcode /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    mem_read_ops inst = NONE /\
    MEM (Var v) inst.inst_operands /\
    Var v <> ops.iao_ofst ==>
    v NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  fs[pointer_confined_def, LET_THM] >>
  first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
  simp[]
QED

(* When two wmwe calls write the same bytes at displaced offsets,
   byte at position (base1 + i) in wmwe1 equals byte at (base2 + i) in wmwe2,
   provided the displacement is consistent and the index is valid. *)
Triviality wmwe_displaced_byte_eq:
  !off1 off2 bytes s1 s2 base1 base2 sz i.
    (off1 + base2 = off2 + base1) /\
    base1 <= off1 /\ base2 <= off2 /\
    (off1 + LENGTH bytes <= base1 + sz) /\
    (off2 + LENGTH bytes <= base2 + sz) /\
    i < sz /\
    (!j. j < sz /\ (j + base1 < off1 \/ off1 + LENGTH bytes <= j + base1) ==>
         mem_byte_at s1.vs_memory (base1 + j) =
         mem_byte_at s2.vs_memory (base2 + j)) ==>
    mem_byte_at (write_memory_with_expansion off1 bytes s1).vs_memory (base1 + i) =
    mem_byte_at (write_memory_with_expansion off2 bytes s2).vs_memory (base2 + i)
Proof
  rpt strip_tac >>
  `base1 + i < off1 \/ (off1 <= base1 + i /\ base1 + i < off1 + LENGTH bytes) \/ off1 + LENGTH bytes <= base1 + i` by simp[]
  >- (
    `base2 + i < off2` by simp[] >>
    simp[mem_byte_at_wmwe_out] >>
    first_x_assum irule >> simp[])
  >- (
    suspend "in_range")
  >- (
    `off2 + LENGTH bytes <= base2 + i` by simp[] >>
    simp[mem_byte_at_wmwe_out] >>
    first_x_assum irule >> simp[])
QED

Resume wmwe_displaced_byte_eq[in_range]:
  `off2 <= base2 + i` by fs[] >>
  `base2 + i < off2 + LENGTH bytes` by fs[] >>
  simp[mem_byte_at_wmwe_in] >>
  `base1 + i - off1 = base2 + i - off2` by fs[] >>
  simp[]
QED

Finalise wmwe_displaced_byte_eq

(* wmwe only changes vs_memory *)
Triviality wmwe_as_mem_update:
  !off bytes s.
    write_memory_with_expansion off bytes s =
    s with vs_memory := (write_memory_with_expansion off bytes s).vs_memory
Proof
  rw[write_memory_with_expansion_def, LET_THM]
QED

(* General: wmwe writes at displaced offsets preserve alloca byte correspondence.
   Parameterized by byte list `bytes` (length `n`) instead of hardcoded 32/1. *)
Triviality wmwe_alloca_byte_corr:
  !amap fn livesets init s1 s2 w1 w2 bytes n aid orig_off sz addr
   aid' orig_off' sz' addr' i.
    concretize_rel amap fn livesets init s1 s2 /\
    LENGTH bytes = n /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
    (w1 - n2w orig_off = w2 - addr) /\
    (orig_off + sz < dimword (:256)) /\
    (sz + w2n addr < dimword (:256)) /\
    (w2n w1 + n <= orig_off + sz) /\
    FLOOKUP s1.vs_allocas aid' = SOME (orig_off', sz') /\
    alloca_concrete_addr amap fn aid' = SOME addr' /\
    alloca_live_at livesets aid' (s1.vs_current_bb, 0) /\
    (sz' + w2n addr' < dimword (:256)) /\
    (aid <> aid' ==> w2n addr + sz <= w2n addr' \/ w2n addr' + sz' <= w2n addr) /\
    is_initialized init aid' i /\ i < sz' ==>
    mem_byte_at
      (write_memory_with_expansion (w2n w1) bytes s1).vs_memory
      (orig_off' + i) =
    mem_byte_at
      (write_memory_with_expansion (w2n w2) bytes s2).vs_memory
      (w2n addr' + i)
Proof
  rpt strip_tac >>
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by
    (ho_match_mp_tac word_displ_to_nat >> qexists_tac `sz` >> simp[]) >>
  `w2n w2 + n <= w2n addr + sz` by fs[] >>
  Cases_on `aid' = aid` >> gvs[]
  >- (
    (* same alloca — n is now LENGTH bytes after gvs[] *)
    Cases_on `i + orig_off < w2n w1`
    >- (
      `i + w2n addr < w2n w2` by fs[] >>
      simp[mem_byte_at_wmwe_out] >>
      ONCE_REWRITE_TAC[ADD_COMM] >>
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      simp[concretize_rel_def, LET_THM] >> strip_tac >>
      first_x_assum (qspecl_then [`aid`, `orig_off`, `sz`, `addr`, `i`] mp_tac) >>
      simp[]) >>
    Cases_on `w2n w1 + LENGTH bytes <= i + orig_off`
    >- (
      `w2n w2 + LENGTH bytes <= i + w2n addr` by fs[] >>
      simp[mem_byte_at_wmwe_out] >>
      ONCE_REWRITE_TAC[ADD_COMM] >>
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      simp[concretize_rel_def, LET_THM] >> strip_tac >>
      first_x_assum (qspecl_then [`aid`, `orig_off`, `sz`, `addr`, `i`] mp_tac) >>
      simp[]) >>
    (* In range: both sides get same byte *)
    `w2n w1 <= i + orig_off /\ i + orig_off < w2n w1 + LENGTH bytes` by fs[] >>
    `w2n w2 <= i + w2n addr` by fs[] >>
    `i + w2n addr < w2n w2 + LENGTH bytes` by fs[] >>
    simp[mem_byte_at_wmwe_in] >>
    `i + orig_off - w2n w1 = i + w2n addr - w2n w2` by fs[] >>
    simp[])
  >- (
    (* different alloca case 1 *)
    `allocas_non_overlapping s1` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      simp[concretize_rel_def, LET_THM] >> strip_tac >> simp[]) >>
    `orig_off + sz <= orig_off' \/ orig_off' + sz' <= orig_off` by (
      qpat_x_assum `allocas_non_overlapping _` mp_tac >>
      simp[allocas_non_overlapping_def] >>
      disch_then (qspecl_then [`aid`, `aid'`, `orig_off`, `sz`, `orig_off'`, `sz'`] mp_tac) >>
      simp[]) >>
    `mem_byte_at (write_memory_with_expansion (w2n w1) bytes s1).vs_memory
       (orig_off' + i) = mem_byte_at s1.vs_memory (orig_off' + i)` by
      (irule mem_byte_at_wmwe_out >> fs[]) >>
    `mem_byte_at (write_memory_with_expansion (w2n w2) bytes s2).vs_memory
       (w2n addr' + i) = mem_byte_at s2.vs_memory (w2n addr' + i)` by
      (irule mem_byte_at_wmwe_out >> fs[]) >>
    gvs[] >>
    ONCE_REWRITE_TAC[ADD_COMM] >>
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM] >> strip_tac >>
    first_x_assum (qspecl_then [`aid'`, `orig_off'`, `sz'`, `addr'`, `i`] mp_tac) >>
    simp[])
  >- (
    (* different alloca case 2 *)
    `allocas_non_overlapping s1` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      simp[concretize_rel_def, LET_THM] >> strip_tac >> simp[]) >>
    `orig_off + sz <= orig_off' \/ orig_off' + sz' <= orig_off` by (
      qpat_x_assum `allocas_non_overlapping _` mp_tac >>
      simp[allocas_non_overlapping_def] >>
      disch_then (qspecl_then [`aid`, `aid'`, `orig_off`, `sz`, `orig_off'`, `sz'`] mp_tac) >>
      simp[]) >>
    `mem_byte_at (write_memory_with_expansion (w2n w1) bytes s1).vs_memory
       (orig_off' + i) = mem_byte_at s1.vs_memory (orig_off' + i)` by
      (irule mem_byte_at_wmwe_out >> fs[]) >>
    `mem_byte_at (write_memory_with_expansion (w2n w2) bytes s2).vs_memory
       (w2n addr' + i) = mem_byte_at s2.vs_memory (w2n addr' + i)` by
      (irule mem_byte_at_wmwe_out >> fs[]) >>
    gvs[] >>
    ONCE_REWRITE_TAC[ADD_COMM] >>
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM] >> strip_tac >>
    first_x_assum (qspecl_then [`aid'`, `orig_off'`, `sz'`, `addr'`, `i`] mp_tac) >>
    simp[])
QED

(* From alloca_concrete_addr, extract FLOOKUP amap v and fn_alloca_id_of_var *)
Triviality alloca_concrete_addr_decompose:
  !amap fn aid addr.
    alloca_concrete_addr amap fn aid = SOME addr /\
    ssa_form fn ==>
    ?out. FLOOKUP amap out = SOME addr /\
          fn_alloca_id_of_var fn out = SOME aid
Proof
  rpt strip_tac >>
  gvs[alloca_concrete_addr_def, AllCaseEqs()] >>
  rename1 `FIND _ (fn_insts fn) = SOME inst` >>
  rename1 `inst.inst_outputs = [out]` >>
  qexists_tac `out` >> simp[] >>
  `MEM inst (fn_insts fn)` by metis_tac[FIND_MEM] >>
  imp_res_tac FIND_P >> gvs[] >>
  simp[fn_alloca_id_of_var_def] >>
  `FIND (\i. is_alloca_op i.inst_opcode /\ i.inst_outputs = [out])
        (fn_insts fn) = SOME inst` by
    (irule find_mem_alloca >> gvs[ssa_form_def]) >>
  simp[]
QED

(* General: wmwe writes at displaced offsets preserve non-alloca byte equality.
   Byte i is outside all alloca regions on s1 and all concrete regions on s2,
   so wmwe doesn't affect it iff the write region is within the alloca/concrete region. *)
Triviality wmwe_nonalloca_byte_corr:
  !amap fn livesets init s1 s2 w1 w2 bytes n aid orig_off sz addr i.
    concretize_rel amap fn livesets init s1 s2 /\
    ssa_form fn /\
    LENGTH bytes = n /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
    (w1 - n2w orig_off = w2 - addr) /\
    (orig_off + sz < dimword (:256)) /\
    (w2n addr + sz < dimword (:256)) /\
    (w2n w1 + n <= orig_off + sz) /\
    alloca_sizes_match fn s1 /\
    ~in_alloca_region s1 i /\ ~in_concrete_region amap fn i ==>
    mem_byte_at (write_memory_with_expansion (w2n w1) bytes s1).vs_memory i =
    mem_byte_at (write_memory_with_expansion (w2n w2) bytes s2).vs_memory i
Proof
  rpt strip_tac >>
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by
    (ho_match_mp_tac word_displ_to_nat >> qexists_tac `sz` >> simp[]) >>
  (* s1 side: i not in alloca region => i outside write range *)
  `~(orig_off <= i /\ i < orig_off + sz)` by (
    qpat_x_assum `~in_alloca_region s1 i` mp_tac >>
    simp[in_alloca_region_def] >> metis_tac[]) >>
  `mem_byte_at (write_memory_with_expansion (w2n w1) bytes s1).vs_memory i =
   mem_byte_at s1.vs_memory i` by
    (irule mem_byte_at_wmwe_out >> fs[]) >>
  `w2n w2 + LENGTH bytes <= w2n addr + sz` by fs[] >>
  (* s2 side: i not in concrete region => i outside write range *)
  suspend "s2_side"
QED

Resume wmwe_nonalloca_byte_corr[s2_side]:
  `sz = get_alloca_size fn (Allocation aid)` by (
    qpat_x_assum `alloca_sizes_match _ _` mp_tac >>
    simp[alloca_sizes_match_def]) >>
  `~(w2n addr <= i /\ i < w2n addr + sz)` by (
    spose_not_then assume_tac >>
    qpat_x_assum `~in_concrete_region _ _ _` mp_tac >>
    simp[in_concrete_region_def] >>
    drule_all alloca_concrete_addr_decompose >>
    strip_tac >> gvs[] >>
    qexistsl [`out`, `addr`, `aid`] >> simp[]) >>
  `mem_byte_at (write_memory_with_expansion (w2n w2) bytes s2).vs_memory i =
   mem_byte_at s2.vs_memory i` by
    (irule mem_byte_at_wmwe_out >> fs[]) >>
  gvs[] >>
  qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
  simp[concretize_rel_def, LET_THM]
QED

Finalise wmwe_nonalloca_byte_corr

(* Specialized for MSTORE (32 bytes) *)
Triviality mstore_alloca_byte_corr:
  !amap fn livesets init s1 s2 w1 w2 (val:bytes32) aid orig_off sz addr
   aid' orig_off' sz' addr' i.
    concretize_rel amap fn livesets init s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
    (w1 - n2w orig_off = w2 - addr) /\
    (orig_off + sz < dimword (:256)) /\
    (sz + w2n addr < dimword (:256)) /\
    (w2n w1 + 32 <= orig_off + sz) /\
    FLOOKUP s1.vs_allocas aid' = SOME (orig_off', sz') /\
    alloca_concrete_addr amap fn aid' = SOME addr' /\
    alloca_live_at livesets aid' (s1.vs_current_bb, 0) /\
    (sz' + w2n addr' < dimword (:256)) /\
    (aid <> aid' ==> w2n addr + sz <= w2n addr' \/ w2n addr' + sz' <= w2n addr) /\
    is_initialized init aid' i /\ i < sz' ==>
    mem_byte_at
      (write_memory_with_expansion (w2n w1) (word_to_bytes val T) s1).vs_memory
      (orig_off' + i) =
    mem_byte_at
      (write_memory_with_expansion (w2n w2) (word_to_bytes val T) s2).vs_memory
      (w2n addr' + i)
Proof
  rpt strip_tac >>
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by
    (ho_match_mp_tac word_displ_to_nat >> qexists_tac `sz` >> simp[]) >>
  `w2n w2 + 32 <= w2n addr + sz` by fs[] >>
  Cases_on `aid' = aid` >> gvs[]
  >- (
    (* same alloca: case split on whether i is in write range *)
    suspend "same_alloca")
  >- (
    (* different alloca case 1: concrete target below write *)
    suspend "diff_alloca_lo")
  >- (
    (* different alloca case 2: concrete target above write *)
    suspend "diff_alloca_hi")
QED

Resume mstore_alloca_byte_corr[same_alloca]:
  (* Case split: is i in the write range [w2n w1, w2n w1 + 32) ? *)
  Cases_on `i + orig_off < w2n w1`
  >- (
    (* Below write range: wmwe_out on both sides + old CR *)
    `i + w2n addr < w2n w2` by fs[] >>
    simp[mem_byte_at_wmwe_out, byteTheory.LENGTH_word_to_bytes, dim256] >>
    ONCE_REWRITE_TAC[ADD_COMM] >>
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM] >> strip_tac >>
    first_x_assum (qspecl_then [`aid`, `orig_off`, `sz`, `addr`, `i`] mp_tac) >>
    simp[]) >>
  Cases_on `w2n w1 + 32 <= i + orig_off`
  >- (
    (* Above write range: wmwe_out on both sides + old CR *)
    `w2n w2 + 32 <= i + w2n addr` by fs[] >>
    simp[mem_byte_at_wmwe_out, byteTheory.LENGTH_word_to_bytes, dim256] >>
    ONCE_REWRITE_TAC[ADD_COMM] >>
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM] >> strip_tac >>
    first_x_assum (qspecl_then [`aid`, `orig_off`, `sz`, `addr`, `i`] mp_tac) >>
    simp[]) >>
  (* In range: both sides get same byte from word_to_bytes *)
  `w2n w1 <= i + orig_off /\ i + orig_off < w2n w1 + 32` by fs[] >>
  `w2n w2 <= i + w2n addr` by fs[] >>
  `i + w2n addr < w2n w2 + 32` by fs[] >>
  `LENGTH (word_to_bytes val T) = 32` by
    simp[byteTheory.LENGTH_word_to_bytes, dim256] >>
  simp[mem_byte_at_wmwe_in] >>
  `i + orig_off - w2n w1 = i + w2n addr - w2n w2` by fs[] >>
  simp[]
QED

Resume mstore_alloca_byte_corr[diff_alloca_lo]:
  rpt strip_tac >>
  (* abstract non-overlapping *)
  `allocas_non_overlapping s1` by (
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM] >> strip_tac >> simp[]) >>
  `orig_off + sz <= orig_off' \/ orig_off' + sz' <= orig_off` by (
    qpat_x_assum `allocas_non_overlapping _` mp_tac >>
    simp[allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid'`, `orig_off`, `sz`, `orig_off'`, `sz'`] mp_tac) >>
    simp[]) >>
  `LENGTH (word_to_bytes val T) = 32` by
    simp[byteTheory.LENGTH_word_to_bytes, dim256] >>
  (* s1: target outside write range (abstract non-overlapping + write within alloca) *)
  `i + orig_off' < w2n w1 \/ w2n w1 + LENGTH (word_to_bytes val T) <= i + orig_off'` by fs[] >>
  (* s2: target outside write range (concrete target below write) *)
  `i + w2n addr' < w2n w2 \/ w2n w2 + LENGTH (word_to_bytes val T) <= i + w2n addr'` by fs[] >>
  (* Apply wmwe_out to both sides *)
  imp_res_tac mem_byte_at_wmwe_out >>
  gvs[] >>
  (* Old bytes correspond by CR *)
  ONCE_REWRITE_TAC[ADD_COMM] >>
  qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
  simp[concretize_rel_def, LET_THM] >> strip_tac >>
  first_x_assum (qspecl_then [`aid'`, `orig_off'`, `sz'`, `addr'`, `i`] mp_tac) >>
  simp[]
QED

(* Same proof structure for both disjuncts *)
Resume mstore_alloca_byte_corr[diff_alloca_hi]:
  rpt strip_tac >>
  `allocas_non_overlapping s1` by (
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM] >> strip_tac >> simp[]) >>
  `orig_off + sz <= orig_off' \/ orig_off' + sz' <= orig_off` by (
    qpat_x_assum `allocas_non_overlapping _` mp_tac >>
    simp[allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid'`, `orig_off`, `sz`, `orig_off'`, `sz'`] mp_tac) >>
    simp[]) >>
  `LENGTH (word_to_bytes val T) = 32` by
    simp[byteTheory.LENGTH_word_to_bytes, dim256] >>
  `i + orig_off' < w2n w1 \/ w2n w1 + LENGTH (word_to_bytes val T) <= i + orig_off'` by fs[] >>
  `i + w2n addr' < w2n w2 \/ w2n w2 + LENGTH (word_to_bytes val T) <= i + w2n addr'` by fs[] >>
  imp_res_tac mem_byte_at_wmwe_out >>
  gvs[] >>
  ONCE_REWRITE_TAC[ADD_COMM] >>
  qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
  simp[concretize_rel_def, LET_THM] >> strip_tac >>
  first_x_assum (qspecl_then [`aid'`, `orig_off'`, `sz'`, `addr'`, `i`] mp_tac) >>
  simp[]
QED

Finalise mstore_alloca_byte_corr

(* MSTORE8: same structure as mstore_alloca_byte_corr but for 1 byte [w2w val]. *)
Triviality mstore8_alloca_byte_corr:
  !amap fn livesets init s1 s2 w1 w2 (val:bytes32) aid orig_off sz addr
   aid' orig_off' sz' addr' i.
    concretize_rel amap fn livesets init s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    alloca_concrete_addr amap fn aid = SOME addr /\
    orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
    (w1 - n2w orig_off = w2 - addr) /\
    (orig_off + sz < dimword (:256)) /\
    (sz + w2n addr < dimword (:256)) /\
    (w2n w1 + 1 <= orig_off + sz) /\
    FLOOKUP s1.vs_allocas aid' = SOME (orig_off', sz') /\
    alloca_concrete_addr amap fn aid' = SOME addr' /\
    alloca_live_at livesets aid' (s1.vs_current_bb, 0) /\
    (sz' + w2n addr' < dimword (:256)) /\
    (aid <> aid' ==> w2n addr + sz <= w2n addr' \/ w2n addr' + sz' <= w2n addr) /\
    is_initialized init aid' i /\ i < sz' ==>
    mem_byte_at
      (write_memory_with_expansion (w2n w1) [w2w val : word8] s1).vs_memory
      (orig_off' + i) =
    mem_byte_at
      (write_memory_with_expansion (w2n w2) [w2w val : word8] s2).vs_memory
      (w2n addr' + i)
Proof
  rpt strip_tac >>
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by
    (ho_match_mp_tac word_displ_to_nat >> qexists_tac `sz` >> simp[]) >>
  `w2n w2 + 1 <= w2n addr + sz` by fs[] >>
  Cases_on `aid' = aid` >> gvs[]
  >- (
    (* same alloca *)
    Cases_on `i + orig_off < w2n w1`
    >- (
      `i + w2n addr < w2n w2` by fs[] >>
      simp[mem_byte_at_wmwe_out] >>
      ONCE_REWRITE_TAC[ADD_COMM] >>
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      simp[concretize_rel_def, LET_THM] >> strip_tac >>
      first_x_assum (qspecl_then [`aid`, `orig_off`, `sz`, `addr`, `i`] mp_tac) >>
      simp[]) >>
    Cases_on `w2n w1 + 1 <= i + orig_off`
    >- (
      `w2n w2 + 1 <= i + w2n addr` by fs[] >>
      simp[mem_byte_at_wmwe_out] >>
      ONCE_REWRITE_TAC[ADD_COMM] >>
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      simp[concretize_rel_def, LET_THM] >> strip_tac >>
      first_x_assum (qspecl_then [`aid`, `orig_off`, `sz`, `addr`, `i`] mp_tac) >>
      simp[]) >>
    (* In range: exactly byte at w2n w1 = i + orig_off *)
    `i + orig_off = w2n w1` by fs[] >>
    `i + w2n addr = w2n w2` by fs[] >>
    simp[mem_byte_at_wmwe_in])
  >- (
    (* different alloca case 1: concrete target below write *)
    `allocas_non_overlapping s1` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      simp[concretize_rel_def, LET_THM] >> strip_tac >> simp[]) >>
    `orig_off + sz <= orig_off' \/ orig_off' + sz' <= orig_off` by (
      qpat_x_assum `allocas_non_overlapping _` mp_tac >>
      simp[allocas_non_overlapping_def] >>
      disch_then (qspecl_then [`aid`, `aid'`, `orig_off`, `sz`, `orig_off'`, `sz'`] mp_tac) >>
      simp[]) >>
    `mem_byte_at (write_memory_with_expansion (w2n w1) [w2w val] s1).vs_memory
       (orig_off' + i) = mem_byte_at s1.vs_memory (orig_off' + i)` by
      (irule mem_byte_at_wmwe_out >> fs[]) >>
    `mem_byte_at (write_memory_with_expansion (w2n w2) [w2w val] s2).vs_memory
       (w2n addr' + i) = mem_byte_at s2.vs_memory (w2n addr' + i)` by
      (irule mem_byte_at_wmwe_out >> fs[]) >>
    gvs[] >>
    ONCE_REWRITE_TAC[ADD_COMM] >>
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM] >> strip_tac >>
    first_x_assum (qspecl_then [`aid'`, `orig_off'`, `sz'`, `addr'`, `i`] mp_tac) >>
    simp[])
  >- (
    (* different alloca case 2: concrete target above write *)
    `allocas_non_overlapping s1` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      simp[concretize_rel_def, LET_THM] >> strip_tac >> simp[]) >>
    `orig_off + sz <= orig_off' \/ orig_off' + sz' <= orig_off` by (
      qpat_x_assum `allocas_non_overlapping _` mp_tac >>
      simp[allocas_non_overlapping_def] >>
      disch_then (qspecl_then [`aid`, `aid'`, `orig_off`, `sz`, `orig_off'`, `sz'`] mp_tac) >>
      simp[]) >>
    `mem_byte_at (write_memory_with_expansion (w2n w1) [w2w val] s1).vs_memory
       (orig_off' + i) = mem_byte_at s1.vs_memory (orig_off' + i)` by
      (irule mem_byte_at_wmwe_out >> fs[]) >>
    `mem_byte_at (write_memory_with_expansion (w2n w2) [w2w val] s2).vs_memory
       (w2n addr' + i) = mem_byte_at s2.vs_memory (w2n addr' + i)` by
      (irule mem_byte_at_wmwe_out >> fs[]) >>
    gvs[] >>
    ONCE_REWRITE_TAC[ADD_COMM] >>
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM] >> strip_tac >>
    first_x_assum (qspecl_then [`aid'`, `orig_off'`, `sz'`, `addr'`, `i`] mp_tac) >>
    simp[])
QED

(* MSTORE: both sides write same 32 bytes at displaced offsets.
   Address is pv (displaced), value is non-pv (same on both sides).
   CR preserved with init' = init via concretize_rel_mem_update. *)
Triviality concretize_step_mstore:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = MSTORE /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_safe_access fn (FDOM amap) s1 /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  (* Extract inst shape *)
  `inst_wf inst` by (fs[fn_inst_wf_def] >> res_tac >> fs[]) >>
  `LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_addr op_val. inst.inst_operands = [op_addr; op_val]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) >>
  gvs[] >>
  (* Address operand is pv *)
  `?v_addr. op_addr = Var v_addr /\
            v_addr IN pointer_derived_vars fn (FDOM amap)` by
    (qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
     simp[all_mem_via_pointer_def, LET_THM] >>
     disch_then (qspecl_then [`bb`, `inst`,
       `<| iao_ofst := op_addr;
          iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w) |>`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  gvs[] >>
  (* Value operand is non-pv via mem_write_tail_non_pv *)
  `!v. op_val = Var v ==>
       v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >> drule_all mstore_value_non_pv >> simp[]) >>
  (* Value operand evaluates same on both sides *)
  `eval_operand op_val s1 = eval_operand op_val s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  (* Get CR displacement for address variable *)
  (* Case split: is v_addr assigned? *)
  Cases_on `lookup_var v_addr s1` >- (
    (* NONE case: both sides error on eval_operand *)
    `lookup_var v_addr s2 = NONE` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC[concretize_rel_def] >> simp[LET_THM] >>
      strip_tac >> first_x_assum (qspec_then `v_addr` mp_tac) >> simp[]) >>
    simp[step_inst_base_def, exec_write2_def, eval_operand_def,
         lookup_var_def, lift_result_def]) >>
  rename1 `lookup_var v_addr s1 = SOME w1` >>
  `lookup_var v_addr s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >>
  gvs[] >>
  (* Evaluate step_inst_base for MSTORE *)
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[exec_write2_def, eval_operand_def, lookup_var_def] >>
  Cases_on `eval_operand op_val s1` >>
  gvs[lift_result_def] >>
  `?val. eval_operand op_val s2 = SOME val` by metis_tac[] >>
  gvs[lift_result_def] >>
  simp[mstore_as_wmwe] >>
  ONCE_REWRITE_TAC[wmwe_as_mem_update] >>
  irule concretize_rel_mem_update >> rpt conj_tac
  >- (
    (* alloca byte correspondence *)
    rpt gen_tac >> strip_tac >>
    rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (off2, sz2)` >>
    rename1 `alloca_concrete_addr amap fn aid2 = SOME addr2` >>
    rename1 `alloca_live_at livesets aid2 _` >>
    rename1 `is_initialized init aid2 j` >>
    rename1 `j < sz2` >>
    suspend "alloca_byte")
  >- (
    (* non-alloca byte correspondence *)
    rpt strip_tac >>
    suspend "nonalloca_byte")
  >- (
    (* CR still holds *)
    first_x_assum ACCEPT_TAC)
QED

Resume concretize_step_mstore[alloca_byte]:
  (* Derive w2n w1 + 32 <= orig_off + sz from alloca_safe_access *)
  `w2n w1 + 32 <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_addr;
          iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w) |>`,
      `v_addr`, `w1`, `Lit 32w`, `32w`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_32w]) >>
  (* Derive sz2 + w2n addr2 < dimword from alloca_overflow_safe *)
  `sz2 + w2n addr2 < dimword (:256)` by (
    qpat_x_assum `alloca_overflow_safe _ _ _` mp_tac >>
    simp[alloca_overflow_safe_def] >> strip_tac >>
    first_x_assum (qspecl_then [`aid2`, `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  (* Derive concrete non-overlapping *)
  `aid <> aid2 ==> w2n addr + sz <= w2n addr2 \/ w2n addr2 + sz2 <= w2n addr` by (
    strip_tac >>
    qpat_x_assum `concrete_allocas_non_overlapping _ _ _` mp_tac >>
    simp[concrete_allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid2`, `orig_off`, `sz`, `addr`,
                             `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  (* Apply mstore_alloca_byte_corr *)
  drule_all mstore_alloca_byte_corr >>
  disch_then (qspec_then `val` mp_tac) >> simp[]
QED

Resume concretize_step_mstore[nonalloca_byte]:
  (* Derive w2n w1 + 32 <= orig_off + sz from alloca_safe_access *)
  `w2n w1 + 32 <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_addr;
          iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w) |>`,
      `v_addr`, `w1`, `Lit 32w`, `32w`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_32w]) >>
  (* Derive w2n addr <= w2n w2 and displacement in nats *)
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by (
    ho_match_mp_tac word_displ_to_nat >> qexists_tac `sz` >> simp[]) >>
  (* s1 side: i not in alloca region => i outside [w2n w1, w2n w1+32) *)
  `~(orig_off <= i /\ i < orig_off + sz)` by (
    qpat_x_assum `~in_alloca_region s1 i` mp_tac >>
    simp[in_alloca_region_def] >> metis_tac[]) >>
  `mem_byte_at (write_memory_with_expansion (w2n w1) (word_to_bytes val T) s1).vs_memory i =
   mem_byte_at s1.vs_memory i` by (
    irule mem_byte_at_wmwe_out >>
    simp[byteTheory.LENGTH_word_to_bytes, dim256] >> fs[]) >>
  (* s2 side: i not in concrete region => i outside [w2n w2, w2n w2+32) *)
  `mem_byte_at (write_memory_with_expansion (w2n w2) (word_to_bytes val T) s2).vs_memory i =
   mem_byte_at s2.vs_memory i` by (
    irule mem_byte_at_wmwe_out >>
    simp[byteTheory.LENGTH_word_to_bytes, dim256] >>
    `w2n w2 + 32 <= w2n addr + sz` by fs[] >>
    `~(w2n addr <= i /\ i < w2n addr + sz)` by (
      spose_not_then assume_tac >>
      qpat_x_assum `~in_concrete_region _ _ _` mp_tac >>
      simp[in_concrete_region_def] >>
      drule_all alloca_concrete_addr_decompose >>
      strip_tac >>
      qexistsl [`out`, `addr`, `aid`] >> simp[] >>
      `sz = get_alloca_size fn (Allocation aid)` by (
        qpat_x_assum `alloca_sizes_match _ _` mp_tac >>
        simp[alloca_sizes_match_def]) >>
      fs[]) >>
    fs[]) >>
  (* Both sides reduce to old memory; CR clause 4 gives equality *)
  gvs[] >>
  qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
  simp[concretize_rel_def, LET_THM]
QED

Finalise concretize_step_mstore

(* Immutable bookkeeping is intentionally absent from concretize_rel. *)
Triviality concretize_rel_update_immutables:
  !amap fn livesets init imms1 imms2 s1 s2.
    concretize_rel amap fn livesets init
      (s1 with vs_immutables := imms1) (s2 with vs_immutables := imms2) <=>
    concretize_rel amap fn livesets init s1 s2
Proof
  simp[concretize_rel_def, LET_THM, lookup_var_def,
       allocas_non_overlapping_def, in_alloca_region_def,
       in_concrete_region_def, mem_byte_at_def]
QED

(* ISTORE's executable effect is exactly the corresponding MSTORE effect. *)
Triviality concretize_rel_istore:
  !amap fn livesets init off1 off2 val1 val2 s1 s2.
    concretize_rel amap fn livesets init
      (istore off1 val1 s1) (istore off2 val2 s2) <=>
    concretize_rel amap fn livesets init
      (mstore off1 val1 s1) (mstore off2 val2 s2)
Proof
  simp[istore_def, concretize_rel_update_immutables]
QED

(* ISTORE has MSTORE's 32-byte executable-memory effect, plus unobserved
   immutable-map bookkeeping. *)
Triviality concretize_step_istore:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = ISTORE /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_safe_access fn (FDOM amap) s1 /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> res_tac >> fs[]) >>
  `LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_addr op_val. inst.inst_operands = [op_addr; op_val]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) >>
  gvs[] >>
  `?v_addr. op_addr = Var v_addr /\
            v_addr IN pointer_derived_vars fn (FDOM amap)` by
    (qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
     simp[all_mem_via_pointer_def, LET_THM] >>
     disch_then (qspecl_then [`bb`, `inst`,
       `<| iao_ofst := op_addr;
          iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w) |>`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def]) >>
  gvs[] >>
  `!v. op_val = Var v ==>
       v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >> drule_all istore_value_non_pv >> simp[]) >>
  `eval_operand op_val s1 = eval_operand op_val s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  Cases_on `lookup_var v_addr s1` >- (
    `lookup_var v_addr s2 = NONE` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC[concretize_rel_def] >> simp[LET_THM] >>
      strip_tac >> first_x_assum (qspec_then `v_addr` mp_tac) >> simp[]) >>
    simp[step_inst_base_def, exec_write2_def, eval_operand_def,
         lookup_var_def, lift_result_def]) >>
  rename1 `lookup_var v_addr s1 = SOME w1` >>
  `lookup_var v_addr s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >>
  gvs[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[exec_write2_def, eval_operand_def, lookup_var_def] >>
  Cases_on `eval_operand op_val s1` >>
  gvs[lift_result_def] >>
  `?val. eval_operand op_val s2 = SOME val` by metis_tac[] >>
  gvs[lift_result_def] >>
  ONCE_REWRITE_TAC[concretize_rel_istore] >>
  simp[mstore_as_wmwe] >>
  ONCE_REWRITE_TAC[wmwe_as_mem_update] >>
  irule concretize_rel_mem_update >> rpt conj_tac
  >- (
    rpt gen_tac >> strip_tac >>
    rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (off2, sz2)` >>
    rename1 `alloca_concrete_addr amap fn aid2 = SOME addr2` >>
    rename1 `alloca_live_at livesets aid2 _` >>
    rename1 `is_initialized init aid2 j` >>
    rename1 `j < sz2` >>
    suspend "istore_alloca_byte")
  >- (rpt strip_tac >> suspend "istore_nonalloca_byte")
  >- first_x_assum ACCEPT_TAC
QED

Resume concretize_step_istore[istore_alloca_byte]:
  `w2n w1 + 32 <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_addr;
          iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w) |>`,
      `v_addr`, `w1`, `Lit 32w`, `32w`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_32w]) >>
  `sz2 + w2n addr2 < dimword (:256)` by (
    qpat_x_assum `alloca_overflow_safe _ _ _` mp_tac >>
    simp[alloca_overflow_safe_def] >> strip_tac >>
    first_x_assum (qspecl_then [`aid2`, `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  `aid <> aid2 ==> w2n addr + sz <= w2n addr2 \/
                   w2n addr2 + sz2 <= w2n addr` by (
    strip_tac >>
    qpat_x_assum `concrete_allocas_non_overlapping _ _ _` mp_tac >>
    simp[concrete_allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid2`, `orig_off`, `sz`, `addr`,
                             `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  drule_all mstore_alloca_byte_corr >>
  disch_then (qspec_then `val` mp_tac) >> simp[]
QED

Resume concretize_step_istore[istore_nonalloca_byte]:
  `w2n w1 + 32 <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_addr;
          iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w) |>`,
      `v_addr`, `w1`, `Lit 32w`, `32w`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_32w]) >>
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by
    (ho_match_mp_tac word_displ_to_nat >> qexists_tac `sz` >> simp[]) >>
  `~(orig_off <= i /\ i < orig_off + sz)` by (
    qpat_x_assum `~in_alloca_region s1 i` mp_tac >>
    simp[in_alloca_region_def] >> metis_tac[]) >>
  `mem_byte_at
     (write_memory_with_expansion (w2n w1) (word_to_bytes val T) s1).vs_memory i =
   mem_byte_at s1.vs_memory i` by (
    irule mem_byte_at_wmwe_out >>
    simp[byteTheory.LENGTH_word_to_bytes, dim256] >> fs[]) >>
  `mem_byte_at
     (write_memory_with_expansion (w2n w2) (word_to_bytes val T) s2).vs_memory i =
   mem_byte_at s2.vs_memory i` by (
    irule mem_byte_at_wmwe_out >>
    simp[byteTheory.LENGTH_word_to_bytes, dim256] >>
    `w2n w2 + 32 <= w2n addr + sz` by fs[] >>
    `~(w2n addr <= i /\ i < w2n addr + sz)` by (
      spose_not_then assume_tac >>
      qpat_x_assum `~in_concrete_region _ _ _` mp_tac >>
      simp[in_concrete_region_def] >>
      drule_all alloca_concrete_addr_decompose >>
      strip_tac >>
      qexistsl [`out`, `addr`, `aid`] >> simp[] >>
      `sz = get_alloca_size fn (Allocation aid)` by (
        qpat_x_assum `alloca_sizes_match _ _` mp_tac >>
        simp[alloca_sizes_match_def]) >>
      fs[]) >>
    fs[]) >>
  gvs[] >>
  qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
  simp[concretize_rel_def, LET_THM]
QED

Finalise concretize_step_istore

(* MSTORE8: same as MSTORE but writes 1 byte [w2w val] instead of 32 bytes. *)
Triviality concretize_step_mstore8:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = MSTORE8 /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_safe_access fn (FDOM amap) s1 /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  (* Extract inst shape *)
  `inst_wf inst` by (fs[fn_inst_wf_def] >> res_tac >> fs[]) >>
  `LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_addr op_val. inst.inst_operands = [op_addr; op_val]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) >>
  gvs[] >>
  (* Address operand is pv *)
  `?v_addr. op_addr = Var v_addr /\
            v_addr IN pointer_derived_vars fn (FDOM amap)` by
    (qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
     simp[all_mem_via_pointer_def, LET_THM] >>
     disch_then (qspecl_then [`bb`, `inst`,
       `<| iao_ofst := op_addr;
          iao_size := SOME (Lit 1w); iao_max_size := SOME (Lit 1w) |>`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  gvs[] >>
  (* Value operand is non-pv *)
  `!v. op_val = Var v ==>
       v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >> drule_all mstore8_value_non_pv >> simp[]) >>
  (* Value operand evaluates same on both sides *)
  `eval_operand op_val s1 = eval_operand op_val s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  (* Get CR displacement for address variable *)
  Cases_on `lookup_var v_addr s1` >- (
    (* NONE case: both sides error on eval_operand *)
    `lookup_var v_addr s2 = NONE` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC[concretize_rel_def] >> simp[LET_THM] >>
      strip_tac >> first_x_assum (qspec_then `v_addr` mp_tac) >> simp[]) >>
    simp[step_inst_base_def, exec_write2_def, eval_operand_def,
         lookup_var_def, lift_result_def]) >>
  rename1 `lookup_var v_addr s1 = SOME w1` >>
  `lookup_var v_addr s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >>
  gvs[] >>
  (* Evaluate step_inst_base for MSTORE8 *)
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[exec_write2_def, eval_operand_def, lookup_var_def] >>
  Cases_on `eval_operand op_val s1` >>
  gvs[lift_result_def] >>
  `?val. eval_operand op_val s2 = SOME val` by metis_tac[] >>
  gvs[lift_result_def] >>
  simp[mstore8_as_wmwe] >>
  ONCE_REWRITE_TAC[wmwe_as_mem_update] >>
  irule concretize_rel_mem_update >> rpt conj_tac
  >- (
    (* alloca byte correspondence *)
    rpt gen_tac >> strip_tac >>
    rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (off2, sz2)` >>
    rename1 `alloca_concrete_addr amap fn aid2 = SOME addr2` >>
    rename1 `alloca_live_at livesets aid2 _` >>
    rename1 `is_initialized init aid2 j` >>
    rename1 `j < sz2` >>
    suspend "alloca_byte")
  >- (
    (* non-alloca byte correspondence *)
    rpt strip_tac >>
    suspend "nonalloca_byte")
  >- (
    (* CR still holds *)
    first_x_assum ACCEPT_TAC)
QED

Resume concretize_step_mstore8[alloca_byte]:
  (* Derive w2n w1 + 1 <= orig_off + sz from alloca_safe_access *)
  `w2n w1 + 1 <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_addr;
          iao_size := SOME (Lit 1w); iao_max_size := SOME (Lit 1w) |>`,
      `v_addr`, `w1`, `Lit 1w`, `1w`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_1w]) >>
  (* Derive sz2 + w2n addr2 < dimword from alloca_overflow_safe *)
  `sz2 + w2n addr2 < dimword (:256)` by (
    qpat_x_assum `alloca_overflow_safe _ _ _` mp_tac >>
    simp[alloca_overflow_safe_def] >> strip_tac >>
    first_x_assum (qspecl_then [`aid2`, `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  (* Derive concrete non-overlapping *)
  `aid <> aid2 ==> w2n addr + sz <= w2n addr2 \/ w2n addr2 + sz2 <= w2n addr` by (
    strip_tac >>
    qpat_x_assum `concrete_allocas_non_overlapping _ _ _` mp_tac >>
    simp[concrete_allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid2`, `orig_off`, `sz`, `addr`,
                             `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  (* Apply mstore8_alloca_byte_corr *)
  drule_all mstore8_alloca_byte_corr >>
  disch_then (qspec_then `val` mp_tac) >> simp[]
QED

Resume concretize_step_mstore8[nonalloca_byte]:
  (* Derive w2n w1 + 1 <= orig_off + sz from alloca_safe_access *)
  `w2n w1 + 1 <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_addr;
          iao_size := SOME (Lit 1w); iao_max_size := SOME (Lit 1w) |>`,
      `v_addr`, `w1`, `Lit 1w`, `1w`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def, eval_operand_def, w2n_1w]) >>
  (* Derive w2n addr <= w2n w2 and displacement in nats *)
  `w2n addr <= w2n w2 /\ w2n w1 - orig_off = w2n w2 - w2n addr` by (
    ho_match_mp_tac word_displ_to_nat >> qexists_tac `sz` >> simp[]) >>
  (* s1 side: i not in alloca region => i outside [w2n w1, w2n w1+1) *)
  `~(orig_off <= i /\ i < orig_off + sz)` by (
    qpat_x_assum `~in_alloca_region s1 i` mp_tac >>
    simp[in_alloca_region_def] >> metis_tac[]) >>
  `mem_byte_at (write_memory_with_expansion (w2n w1) [w2w val : word8] s1).vs_memory i =
   mem_byte_at s1.vs_memory i` by (
    irule mem_byte_at_wmwe_out >> simp[] >> fs[]) >>
  (* s2 side: i not in concrete region => i outside [w2n w2, w2n w2+1) *)
  `mem_byte_at (write_memory_with_expansion (w2n w2) [w2w val : word8] s2).vs_memory i =
   mem_byte_at s2.vs_memory i` by (
    irule mem_byte_at_wmwe_out >> simp[] >>
    `w2n w2 + 1 <= w2n addr + sz` by fs[] >>
    `~(w2n addr <= i /\ i < w2n addr + sz)` by (
      spose_not_then assume_tac >>
      qpat_x_assum `~in_concrete_region _ _ _` mp_tac >>
      simp[in_concrete_region_def] >>
      drule_all alloca_concrete_addr_decompose >>
      strip_tac >>
      qexistsl [`out`, `addr`, `aid`] >> simp[] >>
      `sz = get_alloca_size fn (Allocation aid)` by (
        qpat_x_assum `alloca_sizes_match _ _` mp_tac >>
        simp[alloca_sizes_match_def]) >>
      fs[]) >>
    fs[]) >>
  (* Both sides reduce to old memory; CR clause 4 gives equality *)
  gvs[] >>
  qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
  simp[concretize_rel_def, LET_THM]
QED

Finalise concretize_step_mstore8

(* CALLDATACOPY: writes TAKE (w2n sz) (DROP (w2n src) calldata ++ REPLICATE ...) to memory.
   Address (dst) is pv (displaced), src and sz are non-pv (same on both sides).
   Source data (calldata) is identical on both sides via CR. *)
Triviality concretize_step_calldatacopy:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = CALLDATACOPY /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_safe_access fn (FDOM amap) s1 /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> res_tac >> fs[]) >>
  `LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_dst op_src op_sz. inst.inst_operands = [op_dst; op_src; op_sz]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[] >>
  (* dst is pv *)
  `?v_dst. op_dst = Var v_dst /\
           v_dst IN pointer_derived_vars fn (FDOM amap)` by
    (qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
     simp[all_mem_via_pointer_def, LET_THM] >>
     disch_then (qspecl_then [`bb`, `inst`,
       `<| iao_ofst := op_dst;
          iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  gvs[] >>
  (* src and sz are non-pv via mem_write_tail_non_pv (position-based) *)
  `!v. op_src = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >>
     fs[mem_write_tail_non_pv_def, LET_THM] >>
     first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  `!v. op_sz = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >>
     fs[mem_write_tail_non_pv_def, LET_THM] >>
     first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  (* Non-pv operands evaluate the same *)
  `eval_operand op_src s1 = eval_operand op_src s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  `eval_operand op_sz s1 = eval_operand op_sz s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  (* Handle dst NONE case *)
  Cases_on `lookup_var v_dst s1` >- (
    `lookup_var v_dst s2 = NONE` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC[concretize_rel_def] >> simp[LET_THM] >>
      strip_tac >> first_x_assum (qspec_then `v_dst` mp_tac) >> simp[]) >>
    simp[step_inst_base_def, eval_operand_def,
         lookup_var_def, lift_result_def]) >>
  rename1 `lookup_var v_dst s1 = SOME w1` >>
  `lookup_var v_dst s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >>
  gvs[] >>
  (* Unfold step_inst_base for CALLDATACOPY *)
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def] >>
  (* Substitute s2 evals with s1 evals to unify both sides *)
  qpat_x_assum `eval_operand op_src s1 = eval_operand op_src s2`
    (fn th => REWRITE_TAC[SYM th]) >>
  qpat_x_assum `eval_operand op_sz s1 = eval_operand op_sz s2`
    (fn th => REWRITE_TAC[SYM th]) >>
  Cases_on `eval_operand op_src s1` >>
  gvs[lift_result_def] >>
  Cases_on `eval_operand op_sz s1` >>
  gvs[lift_result_def] >>
  (* Source data is identical *)
  `s1.vs_call_ctx = s2.vs_call_ctx` by (
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM]) >>
  simp[] >>
  ONCE_REWRITE_TAC[wmwe_as_mem_update] >>
  irule concretize_rel_mem_update >> rpt conj_tac
  >- (
    (* alloca byte correspondence *)
    rpt gen_tac >> strip_tac >>
    rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (off2, sz2)` >>
    rename1 `alloca_concrete_addr amap fn aid2 = SOME addr2` >>
    rename1 `alloca_live_at livesets aid2 _` >>
    rename1 `is_initialized init aid2 j` >>
    rename1 `j < sz2` >>
    suspend "alloca_byte")
  >- (
    (* non-alloca byte correspondence *)
    rpt strip_tac >>
    suspend "nonalloca_byte")
  >- (
    first_x_assum ACCEPT_TAC)
QED

Resume concretize_step_calldatacopy[alloca_byte]:
  irule wmwe_alloca_byte_corr >>
  (* alloca_safe_access gives w2n w1 + w2n sz_val <= orig_off + sz *)
  `w2n w1 + w2n x' <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_dst;
         iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`,
      `v_dst`, `w1`, `op_sz`, `x'`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def]) >>
  (* alloca_overflow_safe *)
  `sz2 + w2n addr2 < dimword (:256)` by (
    qpat_x_assum `alloca_overflow_safe _ _ _` mp_tac >>
    simp[alloca_overflow_safe_def] >> strip_tac >>
    first_x_assum (qspecl_then [`aid2`, `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  (* concrete non-overlapping *)
  `aid <> aid2 ==> w2n addr + sz <= w2n addr2 \/ w2n addr2 + sz2 <= w2n addr` by (
    strip_tac >>
    qpat_x_assum `concrete_allocas_non_overlapping _ _ _` mp_tac >>
    simp[concrete_allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid2`, `orig_off`, `sz`, `addr`,
                             `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  simp[LENGTH_TAKE_EQ] >>
  qexistsl [`addr`, `aid`, `aid2`, `amap`, `fn`, `init`, `livesets`,
            `orig_off`, `sz`, `sz2`] >> simp[]
QED

Resume concretize_step_calldatacopy[nonalloca_byte]:
  irule wmwe_nonalloca_byte_corr >>
  `w2n w1 + w2n x' <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_dst;
         iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`,
      `v_dst`, `w1`, `op_sz`, `x'`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def]) >>
  simp[LENGTH_TAKE_EQ] >>
  qexistsl [`addr`, `aid`, `amap`, `fn`, `init`, `livesets`,
            `orig_off`, `sz`] >> simp[]
QED

Finalise concretize_step_calldatacopy

(* CODECOPY: identical pattern to CALLDATACOPY with vs_code as source. *)
Triviality concretize_step_codecopy:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = CODECOPY /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_safe_access fn (FDOM amap) s1 /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> res_tac >> fs[]) >>
  `LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_dst op_src op_sz. inst.inst_operands = [op_dst; op_src; op_sz]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[] >>
  `?v_dst. op_dst = Var v_dst /\
           v_dst IN pointer_derived_vars fn (FDOM amap)` by
    (qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
     simp[all_mem_via_pointer_def, LET_THM] >>
     disch_then (qspecl_then [`bb`, `inst`,
       `<| iao_ofst := op_dst;
          iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  gvs[] >>
  `!v. op_src = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >>
     fs[mem_write_tail_non_pv_def, LET_THM] >>
     first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  `!v. op_sz = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >>
     fs[mem_write_tail_non_pv_def, LET_THM] >>
     first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  `eval_operand op_src s1 = eval_operand op_src s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  `eval_operand op_sz s1 = eval_operand op_sz s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  Cases_on `lookup_var v_dst s1` >- (
    `lookup_var v_dst s2 = NONE` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC[concretize_rel_def] >> simp[LET_THM] >>
      strip_tac >> first_x_assum (qspec_then `v_dst` mp_tac) >> simp[]) >>
    simp[step_inst_base_def, eval_operand_def,
         lookup_var_def, lift_result_def]) >>
  rename1 `lookup_var v_dst s1 = SOME w1` >>
  `lookup_var v_dst s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >>
  gvs[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `eval_operand op_src s1 = eval_operand op_src s2`
    (fn th => REWRITE_TAC[SYM th]) >>
  qpat_x_assum `eval_operand op_sz s1 = eval_operand op_sz s2`
    (fn th => REWRITE_TAC[SYM th]) >>
  Cases_on `eval_operand op_src s1` >>
  gvs[lift_result_def] >>
  Cases_on `eval_operand op_sz s1` >>
  gvs[lift_result_def] >>
  `s1.vs_code = s2.vs_code` by (
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM]) >>
  simp[] >>
  ONCE_REWRITE_TAC[wmwe_as_mem_update] >>
  irule concretize_rel_mem_update >> rpt conj_tac
  >- (
    rpt gen_tac >> strip_tac >>
    rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (off2, sz2)` >>
    rename1 `alloca_concrete_addr amap fn aid2 = SOME addr2` >>
    rename1 `alloca_live_at livesets aid2 _` >>
    rename1 `is_initialized init aid2 j` >>
    rename1 `j < sz2` >>
    suspend "alloca_byte")
  >- (
    rpt strip_tac >>
    suspend "nonalloca_byte")
  >- (
    first_x_assum ACCEPT_TAC)
QED

Resume concretize_step_codecopy[alloca_byte]:
  irule wmwe_alloca_byte_corr >>
  `w2n w1 + w2n x' <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_dst;
         iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`,
      `v_dst`, `w1`, `op_sz`, `x'`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def]) >>
  `sz2 + w2n addr2 < dimword (:256)` by (
    qpat_x_assum `alloca_overflow_safe _ _ _` mp_tac >>
    simp[alloca_overflow_safe_def] >> strip_tac >>
    first_x_assum (qspecl_then [`aid2`, `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  `aid <> aid2 ==> w2n addr + sz <= w2n addr2 \/ w2n addr2 + sz2 <= w2n addr` by (
    strip_tac >>
    qpat_x_assum `concrete_allocas_non_overlapping _ _ _` mp_tac >>
    simp[concrete_allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid2`, `orig_off`, `sz`, `addr`,
                             `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  simp[LENGTH_TAKE_EQ] >>
  qexistsl [`addr`, `aid`, `aid2`, `amap`, `fn`, `init`, `livesets`,
            `orig_off`, `sz`, `sz2`] >> simp[]
QED

Resume concretize_step_codecopy[nonalloca_byte]:
  irule wmwe_nonalloca_byte_corr >>
  `w2n w1 + w2n x' <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_dst;
         iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`,
      `v_dst`, `w1`, `op_sz`, `x'`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def]) >>
  simp[LENGTH_TAKE_EQ] >>
  qexistsl [`addr`, `aid`, `amap`, `fn`, `init`, `livesets`,
            `orig_off`, `sz`] >> simp[]
QED

Finalise concretize_step_codecopy

(* DLOADBYTES: identical pattern to CALLDATACOPY with vs_data_section as source. *)
Triviality concretize_step_dloadbytes:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = DLOADBYTES /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_safe_access fn (FDOM amap) s1 /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> res_tac >> fs[]) >>
  `LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_dst op_src op_sz. inst.inst_operands = [op_dst; op_src; op_sz]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[] >>
  `?v_dst. op_dst = Var v_dst /\
           v_dst IN pointer_derived_vars fn (FDOM amap)` by
    (qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
     simp[all_mem_via_pointer_def, LET_THM] >>
     disch_then (qspecl_then [`bb`, `inst`,
       `<| iao_ofst := op_dst;
          iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  gvs[] >>
  `!v. op_src = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >>
     fs[mem_write_tail_non_pv_def, LET_THM] >>
     first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  `!v. op_sz = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >>
     fs[mem_write_tail_non_pv_def, LET_THM] >>
     first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  `eval_operand op_src s1 = eval_operand op_src s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  `eval_operand op_sz s1 = eval_operand op_sz s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  Cases_on `lookup_var v_dst s1` >- (
    `lookup_var v_dst s2 = NONE` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC[concretize_rel_def] >> simp[LET_THM] >>
      strip_tac >> first_x_assum (qspec_then `v_dst` mp_tac) >> simp[]) >>
    simp[step_inst_base_def, eval_operand_def,
         lookup_var_def, lift_result_def]) >>
  rename1 `lookup_var v_dst s1 = SOME w1` >>
  `lookup_var v_dst s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >>
  gvs[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `eval_operand op_src s1 = eval_operand op_src s2`
    (fn th => REWRITE_TAC[SYM th]) >>
  qpat_x_assum `eval_operand op_sz s1 = eval_operand op_sz s2`
    (fn th => REWRITE_TAC[SYM th]) >>
  Cases_on `eval_operand op_src s1` >>
  gvs[lift_result_def] >>
  Cases_on `eval_operand op_sz s1` >>
  gvs[lift_result_def] >>
  `s1.vs_data_section = s2.vs_data_section` by (
    qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
    simp[concretize_rel_def, LET_THM]) >>
  simp[] >>
  ONCE_REWRITE_TAC[wmwe_as_mem_update] >>
  irule concretize_rel_mem_update >> rpt conj_tac
  >- (
    rpt gen_tac >> strip_tac >>
    rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (off2, sz2)` >>
    rename1 `alloca_concrete_addr amap fn aid2 = SOME addr2` >>
    rename1 `alloca_live_at livesets aid2 _` >>
    rename1 `is_initialized init aid2 j` >>
    rename1 `j < sz2` >>
    suspend "alloca_byte")
  >- (
    rpt strip_tac >>
    suspend "nonalloca_byte")
  >- (
    first_x_assum ACCEPT_TAC)
QED

Resume concretize_step_dloadbytes[alloca_byte]:
  irule wmwe_alloca_byte_corr >>
  `w2n w1 + w2n x' <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_dst;
         iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`,
      `v_dst`, `w1`, `op_sz`, `x'`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def]) >>
  `sz2 + w2n addr2 < dimword (:256)` by (
    qpat_x_assum `alloca_overflow_safe _ _ _` mp_tac >>
    simp[alloca_overflow_safe_def] >> strip_tac >>
    first_x_assum (qspecl_then [`aid2`, `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  `aid <> aid2 ==> w2n addr + sz <= w2n addr2 \/ w2n addr2 + sz2 <= w2n addr` by (
    strip_tac >>
    qpat_x_assum `concrete_allocas_non_overlapping _ _ _` mp_tac >>
    simp[concrete_allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid2`, `orig_off`, `sz`, `addr`,
                             `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  simp[LENGTH_TAKE_EQ] >>
  qexistsl [`addr`, `aid`, `aid2`, `amap`, `fn`, `init`, `livesets`,
            `orig_off`, `sz`, `sz2`] >> simp[]
QED

Resume concretize_step_dloadbytes[nonalloca_byte]:
  irule wmwe_nonalloca_byte_corr >>
  `w2n w1 + w2n x' <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_dst;
         iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`,
      `v_dst`, `w1`, `op_sz`, `x'`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def]) >>
  simp[LENGTH_TAKE_EQ] >>
  qexistsl [`addr`, `aid`, `amap`, `fn`, `init`, `livesets`,
            `orig_off`, `sz`] >> simp[]
QED

Finalise concretize_step_dloadbytes

(* RETURNDATACOPY: like CALLDATACOPY but with OOB check → Abort.
   When OOB: both sides abort (same condition, same returndata).
   When in-bounds: same pattern as CALLDATACOPY with vs_returndata. *)
Triviality concretize_step_returndatacopy:
  !inst bb amap fn livesets init s1 s2.
    inst.inst_opcode = RETURNDATACOPY /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_safe_access fn (FDOM amap) s1 /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> res_tac >> fs[]) >>
  `LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  `?op_dst op_src op_sz. inst.inst_operands = [op_dst; op_src; op_sz]` by
    (Cases_on `inst.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[] >>
  (* dst is pv *)
  `?v_dst. op_dst = Var v_dst /\
           v_dst IN pointer_derived_vars fn (FDOM amap)` by
    (qpat_x_assum `all_mem_via_pointer _ _` mp_tac >>
     simp[all_mem_via_pointer_def, LET_THM] >>
     disch_then (qspecl_then [`bb`, `inst`,
       `<| iao_ofst := op_dst;
          iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  gvs[] >>
  (* src and sz are non-pv via mem_write_tail_non_pv *)
  `!v. op_src = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >>
     fs[mem_write_tail_non_pv_def, LET_THM] >>
     first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  `!v. op_sz = Var v ==> v NOTIN pointer_derived_vars fn (FDOM amap)` by
    (rpt strip_tac >> gvs[] >>
     fs[mem_write_tail_non_pv_def, LET_THM] >>
     first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
     simp[memLocDefsTheory.mem_write_ops_def,
          pointerConfinedDefsTheory.is_immutable_op_def]) >>
  (* Non-pv operands evaluate the same *)
  `eval_operand op_src s1 = eval_operand op_src s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  `eval_operand op_sz s1 = eval_operand op_sz s2` by
    (drule cr_eval_operand_non_pv >> disch_then irule >> simp[]) >>
  (* Handle dst NONE case *)
  Cases_on `lookup_var v_dst s1` >- (
    `lookup_var v_dst s2 = NONE` by (
      qpat_x_assum `concretize_rel _ _ _ _ _ _` mp_tac >>
      ONCE_REWRITE_TAC[concretize_rel_def] >> simp[LET_THM] >>
      strip_tac >> first_x_assum (qspec_then `v_dst` mp_tac) >> simp[]) >>
    ONCE_REWRITE_TAC[step_inst_base_def] >>
    qpat_x_assum `inst.inst_opcode = RETURNDATACOPY`
      (fn th => assume_tac th >> PURE_REWRITE_TAC[th]) >>
    simp[eval_operand_def, lookup_var_def, lift_result_def]) >>
  rename1 `lookup_var v_dst s1 = SOME w1` >>
  `lookup_var v_dst s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >>
  gvs[] >>
  (* Unfold step_inst_base for RETURNDATACOPY *)
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = RETURNDATACOPY`
    (fn th => assume_tac th >> PURE_REWRITE_TAC[th]) >>
  simp[eval_operand_def, lookup_var_def] >>
  (* Substitute s2 evals with s1 evals *)
  qpat_x_assum `eval_operand op_src s1 = eval_operand op_src s2`
    (fn th => REWRITE_TAC[SYM th]) >>
  qpat_x_assum `eval_operand op_sz s1 = eval_operand op_sz s2`
    (fn th => REWRITE_TAC[SYM th]) >>
  Cases_on `eval_operand op_src s1` >>
  gvs[lift_result_def] >>
  Cases_on `eval_operand op_sz s1` >>
  gvs[lift_result_def] >>
  (* Source data (returndata) is identical *)
  `s1.vs_returndata = s2.vs_returndata` by
    fs[concretize_rel_def, LET_THM] >>
  simp[] >>
  (* OOB case: both sides Abort with same args *)
  Cases_on `w2n x + w2n x' > LENGTH s1.vs_returndata` >- (
    suspend "oob_case") >>
  simp[] >>
  suspend "wmwe_cont"
QED

Resume concretize_step_returndatacopy[oob_case]:
  gvs[lift_result_def] >>
  irule concretize_rel_frame >>
  simp[halt_state_def, set_returndata_def] >>
  fs[concretize_rel_def, LET_THM] >>
  qexists_tac `s1` >> qexists_tac `s2` >> gvs[] >>
  rpt strip_tac >> res_tac
QED

Resume concretize_step_returndatacopy[wmwe_cont]:
  gvs[lift_result_def] >>
  ONCE_REWRITE_TAC[wmwe_as_mem_update] >>
  irule concretize_rel_mem_update >> rpt conj_tac
  >- (
    rpt gen_tac >> strip_tac >>
    rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (off2, sz2)` >>
    rename1 `alloca_concrete_addr amap fn aid2 = SOME addr2` >>
    rename1 `alloca_live_at livesets aid2 _` >>
    rename1 `is_initialized init aid2 j` >>
    rename1 `j < sz2` >>
    suspend "alloca_byte")
  >- (
    rpt strip_tac >>
    suspend "nonalloca_byte")
  >- (
    first_x_assum ACCEPT_TAC)
QED

Resume concretize_step_returndatacopy[alloca_byte]:
  irule wmwe_alloca_byte_corr >>
  `w2n w1 + w2n x' <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_dst;
         iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`,
      `v_dst`, `w1`, `op_sz`, `x'`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def]) >>
  `sz2 + w2n addr2 < dimword (:256)` by (
    qpat_x_assum `alloca_overflow_safe _ _ _` mp_tac >>
    simp[alloca_overflow_safe_def] >> strip_tac >>
    first_x_assum (qspecl_then [`aid2`, `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  `aid <> aid2 ==> w2n addr + sz <= w2n addr2 \/ w2n addr2 + sz2 <= w2n addr` by (
    strip_tac >>
    qpat_x_assum `concrete_allocas_non_overlapping _ _ _` mp_tac >>
    simp[concrete_allocas_non_overlapping_def] >>
    disch_then (qspecl_then [`aid`, `aid2`, `orig_off`, `sz`, `addr`,
                             `off2`, `sz2`, `addr2`] mp_tac) >>
    simp[]) >>
  simp[LENGTH_TAKE_EQ] >>
  qexistsl [`addr`, `aid`, `aid2`, `amap`, `fn`, `init`, `livesets`,
            `orig_off`, `sz`, `sz2`] >> simp[]
QED

Resume concretize_step_returndatacopy[nonalloca_byte]:
  irule wmwe_nonalloca_byte_corr >>
  `w2n w1 + w2n x' <= orig_off + sz` by (
    qpat_x_assum `alloca_safe_access _ _ _` mp_tac >>
    simp[alloca_safe_access_def, LET_THM] >>
    strip_tac >>
    pop_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := Var v_dst;
         iao_size := SOME op_sz; iao_max_size := SOME op_sz |>`,
      `v_dst`, `w1`, `op_sz`, `x'`, `aid`, `orig_off`, `sz`] mp_tac) >>
    simp[memLocDefsTheory.mem_write_ops_def]) >>
  simp[LENGTH_TAKE_EQ] >>
  qexistsl [`addr`, `aid`, `amap`, `fn`, `init`, `livesets`,
            `orig_off`, `sz`] >> simp[]
QED

Finalise concretize_step_returndatacopy

(* Per-instruction simulation for non-alloca, non-INVOKE, non-NOP, non-MEMTOP
   opcodes. Under concretize_rel, step_inst_base on the original instruction
   and (identical) concretized instruction are related — pure ops agree on
   results, pointer-preserving ops maintain displacement, memory ops use
   byte correspondence, terminators jump to the same target. MEMTOP excluded
   because vs_memory LENGTH may differ between sides after displaced writes. *)

(* Exhaustive audit for the memory-effect arm of the identity dispatcher. *)
Triviality concretize_memory_effect_survivors:
  !op.
    ~is_alloca_op op /\ op <> INVOKE /\ op <> NOP /\ op <> MEMTOP /\
    op <> LOG /\ op <> MCOPY /\ op <> EXTCODECOPY /\
    ~is_pointer_preserving_op op /\ ~is_effect_free_op op /\
    ~is_ext_call_op op /\ op <> RETURN /\ op <> REVERT /\ op <> DALLOCA /\
    (Eff_MEMORY IN read_effects op \/ Eff_MEMORY IN write_effects op) ==>
    op = MSTORE \/ op = MSTORE8 \/ op = CALLDATACOPY \/ op = CODECOPY \/
    op = DLOADBYTES \/ op = RETURNDATACOPY \/ op = ISTORE \/ op = DRET
Proof
  Cases >>
  simp[is_alloca_op_def, is_pointer_preserving_op_def, is_effect_free_op_def,
       is_ext_call_op_def, venomEffectsTheory.read_effects_def,
       venomEffectsTheory.write_effects_def, venomEffectsTheory.all_effects_def,
       venomEffectsTheory.empty_effects_def]
QED

(* The generic memory-location tables do not expose DRET's dynamic pairs.
   Consequently the existing per-access safety hypotheses cannot supply the
   source-byte premise needed by take_drop_pad_bytes_eq. *)
Triviality dert_memloc_tables_blind:
  !inst. inst.inst_opcode = DRET ==>
    mem_read_ops inst = NONE /\ mem_write_ops inst = NONE
Proof
  simp[memLocDefsTheory.mem_read_ops_def, memLocDefsTheory.mem_write_ops_def]
QED
Theorem concretize_step_inst_base_identity:
  !inst bb amap fn livesets init s1 s2.
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> NOP /\
    inst.inst_opcode <> MEMTOP /\
    inst.inst_opcode <> DRET /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> MCOPY /\
    inst.inst_opcode <> EXTCODECOPY /\
    ~is_ext_call_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    alloca_overflow_safe fn amap s1 /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (step_inst_base inst s1)
        (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  Cases_on `is_pointer_preserving_op inst.inst_opcode`
  >- (qexists `init` >>
      irule concretize_step_pointer_preserving >>
      simp[] >> metis_tac[]) >>
  Cases_on `is_effect_free_op inst.inst_opcode`
  >- (
    (* ILOAD: reads vs_immutables not vs_memory, handle before memory check *)
    Cases_on `inst.inst_opcode = ILOAD`
    >- (qexists `init` >> irule concretize_step_iload >> metis_tac[]) >>
    Cases_on `inst.inst_opcode = MLOAD`
    >- (qexists `init` >> irule concretize_step_mload >> metis_tac[]) >>
    Cases_on `Eff_MEMORY IN read_effects inst.inst_opcode`
    >- (`inst.inst_opcode = SHA3` by
        (Cases_on `inst.inst_opcode` >>
         gvs[venomEffectsTheory.read_effects_def,
             venomEffectsTheory.all_effects_def,
             venomEffectsTheory.empty_effects_def,
             is_effect_free_op_def]) >>
       qexists `init` >> irule concretize_step_sha3 >> metis_tac[]) >>
    (* Eff_MSIZE no longer exists (MSIZE→MEMTOP, upstream #4909);
       Eff_MSIZE NOTIN read_effects is vacuously true *)
    fs[] >>
    qexists `init` >>
    irule concretize_step_pure_non_pv >>
    metis_tac[non_alloca_non_pp_output_not_pv]
  ) >>
  (* Non-effect-free ops *)
  Cases_on `inst.inst_opcode = RETURN`
  >- (qexists `init` >> irule concretize_step_return >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (qexists `init` >> irule concretize_step_dalloca >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = REVERT`
  >- (qexists `init` >> irule concretize_step_revert >> metis_tac[]) >>
  Cases_on `is_ext_call_op inst.inst_opcode`
  >- gvs[] >>
  Cases_on `Eff_MEMORY IN read_effects inst.inst_opcode \/
            Eff_MEMORY IN write_effects inst.inst_opcode`
  >- (
    Cases_on `inst.inst_opcode = MSTORE`
    >- (qexists `init` >> irule concretize_step_mstore >> metis_tac[]) >>
    Cases_on `inst.inst_opcode = MSTORE8`
    >- (qexists `init` >> irule concretize_step_mstore8 >> metis_tac[]) >>
    Cases_on `inst.inst_opcode = CALLDATACOPY`
    >- (qexists `init` >> irule concretize_step_calldatacopy >> metis_tac[]) >>
    Cases_on `inst.inst_opcode = CODECOPY`
    >- (qexists `init` >> irule concretize_step_codecopy >> metis_tac[]) >>
    Cases_on `inst.inst_opcode = DLOADBYTES`
    >- (qexists `init` >> irule concretize_step_dloadbytes >> metis_tac[]) >>
    Cases_on `inst.inst_opcode = RETURNDATACOPY`
    >- (qexists `init` >> irule concretize_step_returndatacopy >> metis_tac[]) >>
    Cases_on `inst.inst_opcode = ISTORE`
    >- (qexists `init` >> irule concretize_step_istore >> metis_tac[]) >>
    Cases_on `inst.inst_opcode = LOG` >- gvs[] >>
    Cases_on `inst.inst_opcode` >>
    gvs[is_effect_free_op_def, is_pointer_preserving_op_def,
        is_alloca_op_def, is_ext_call_op_def,
        venomEffectsTheory.read_effects_def,
        venomEffectsTheory.write_effects_def,
        venomEffectsTheory.all_effects_def,
        venomEffectsTheory.empty_effects_def]) >>
  Cases_on `is_ext_call_op inst.inst_opcode`
  >- gvs[] >>
  fs[] >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
            inst.inst_opcode = DJMP`
  >- (
    qexists `FEMPTY` >>
    irule concretize_step_branch_terminator >>
    simp[] >> metis_tac[]
  ) >>
  fs[] >>
  qexists `init` >>
  irule concretize_step_non_mem_identity >>
  metis_tac[]
QED

(* ALLOCA on side 1 vs ASSIGN on side 2 preserves concretize_rel.
   Side 1 bump-allocates at vs_alloca_next; side 2 assigns the concrete
   address from amap. The displacement invariant (w1 - base = w2 - addr)
   is established for fresh allocas and maintained for reuse. *)
Theorem concretize_step_alloca_assign:
  !inst bb amap fn livesets init s1 s2 out addr alloc_size.
    inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit alloc_size] /\
    inst.inst_outputs = [out] /\
    FLOOKUP amap out = SOME addr /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ssa_form fn /\
    fn_inst_ids_distinct fn /\
    alloca_inv s1 /\
    0 < w2n alloc_size /\
    s1.vs_alloca_next < dimword (:256) /\
    (FLOOKUP s1.vs_allocas inst.inst_id = NONE ==>
     s1.vs_alloca_next + w2n alloc_size < dimword (:256)) /\
    w2n addr + w2n alloc_size < dimword (:256) /\
    (!aid off sz addr'.
       FLOOKUP s1.vs_allocas aid = SOME (off, sz) /\
       alloca_concrete_addr amap fn aid = SOME addr' ==>
       0 < sz /\ w2n addr' + sz < dimword (:256)) /\
    concretize_pointer_confined fn amap /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (step_inst_base inst s1)
        (step_inst_base (mk_assign_inst inst (Lit addr)) s2)
Proof
  rpt strip_tac >>
  `step_inst_base inst s1 = exec_alloca inst s1 alloc_size` by
    simp[step_inst_base_def] >>
  `step_inst_base (mk_assign_inst inst (Lit addr)) s2 =
     OK (update_var out addr s2)` by
    simp[step_inst_base_def, mk_assign_inst_def, eval_operand_def] >>
  rewrite_tac[] >>
  (* Case split on FLOOKUP vs_allocas inst.inst_id *)
  Cases_on `FLOOKUP s1.vs_allocas inst.inst_id`
  >- (
    (* Fresh alloca: NONE case *)
    simp[exec_alloca_def, update_var_def, lift_result_def, LET_THM] >>
    qexists `init \\ inst.inst_id` >>
    suspend "fresh"
  )
  >>
  (* Reuse alloca: SOME case *)
  rename1 `FLOOKUP s1.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  simp[exec_alloca_def, update_var_def, lift_result_def] >>
  qexists `init` >>
  suspend "reuse"
QED

Resume concretize_step_alloca_assign[fresh]:
  match_mp_tac step_alloca_fresh_goal >>
  qexists `bb` >> simp[] >> metis_tac[ADD_COMM]
QED

Resume concretize_step_alloca_assign[reuse]:
  simp[GSYM update_var_def] >>
  match_mp_tac step_alloca_reuse_goal >>
  qexistsl [`inst`, `bb`, `alloc_size`, `entry1`] >>
  simp[] >> metis_tac[ADD_COMM]
QED

Finalise concretize_step_alloca_assign

(* eval_operand doesn't depend on vs_inst_idx *)
Triviality eval_operand_inst_idx:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases_on `op` >> rw[eval_operand_def, lookup_var_def]
QED

(* concretize_rel preserved by any vs_inst_idx update on both sides *)
Triviality concretize_rel_update_inst_idx:
  !amap fn livesets init s1 s2 n m.
    concretize_rel amap fn livesets init s1 s2 ==>
    concretize_rel amap fn livesets init
      (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := m)
Proof
  rpt strip_tac >>
  fs[concretize_rel_def, LET_THM, lookup_var_def,
     allocas_non_overlapping_def, in_alloca_region_def] >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> fs[]
QED

(* ---------- Structural helpers for block simulation ---------- *)

(* get_instruction commutes with block_map_transform *)
Triviality get_instruction_bmt:
  !f bb i.
    get_instruction (block_map_transform f bb) i =
    OPTION_MAP f (get_instruction bb i)
Proof
  rw[get_instruction_def, block_map_transform_def] >>
  simp[EL_MAP]
QED

(* concretize_inst on non-alloca preserves opcode *)
Triviality concretize_inst_non_alloca_opcode:
  !amap inst.
    ~is_alloca_op inst.inst_opcode ==>
    (concretize_inst amap inst).inst_opcode = inst.inst_opcode
Proof
  rw[concretize_inst_def]
QED

(* concretize_inst on alloca with output in amap: opcode is ASSIGN *)
Triviality concretize_inst_alloca_assign:
  !amap inst out addr.
    is_alloca_op inst.inst_opcode /\
    inst.inst_outputs = [out] /\
    FLOOKUP amap out = SOME addr ==>
    concretize_inst amap inst = mk_assign_inst inst (Lit addr)
Proof
  rw[concretize_inst_def]
QED

(* concretize_inst never produces NOP under all_allocas_mapped + fn_inst_wf +
   non-NOP input. Alloca → ASSIGN (mapped) or identity (non-singleton outputs,
   but fn_inst_wf ensures singleton). Non-alloca → identity. *)
Triviality concretize_inst_not_nop:
  !amap fn inst bb.
    all_allocas_mapped fn amap /\ fn_inst_wf fn /\
    inst.inst_opcode <> NOP /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    (concretize_inst amap inst).inst_opcode <> NOP
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >>
  gvs[mk_assign_inst_def, mk_nop_inst_def] >>
  (* The NONE case: alloca output not in amap — contradicts all_allocas_mapped *)
  fs[all_allocas_mapped_def, FLOOKUP_DEF] >>
  first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >>
  simp[] >> Cases_on `inst.inst_outputs` >> gvs[]
QED

(* Under all_allocas_mapped + fn_inst_wf + no input NOPs,
   clear_nops_block (bmt (ci amap) bb) = bmt (ci amap) bb *)
Triviality clear_nops_bmt_identity:
  !amap fn bb.
    all_allocas_mapped fn amap /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions ==>
    clear_nops_block (block_map_transform (concretize_inst amap) bb) =
    block_map_transform (concretize_inst amap) bb
Proof
  rw[clear_nops_block_def, block_map_transform_def,
     basic_block_component_equality] >>
  irule (iffRL FILTER_EQ_ID) >>
  simp[EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >>
  `x.inst_opcode <> NOP` by (fs[EVERY_MEM]) >>
  metis_tac[concretize_inst_not_nop]
QED

(* Inner block sim: exec_block bb s1 vs exec_block (bmt (ci amap) bb) s2
   without clear_nops. Relates side 1 and side 2 under concretize_rel.
   Uses measureInduct on remaining instructions.
   Why true: at each step, get_instruction_bmt gives the transformed inst.
   For non-alloca: step_inst_base is identical modulo CR (concretize_step_inst_base_identity).
   For alloca: ALLOCA on side 1 vs ASSIGN on side 2 (concretize_step_alloca_assign).
   Both preserve CR. Terminators end the block; non-terminators recurse. *)
Triviality is_alloca_op_eq:
  !x. is_alloca_op x ==> (x = ALLOCA)
Proof
  Cases >> simp[is_alloca_op_def]
QED

Triviality concretize_inst_is_terminator:
  !amap inst.
    is_terminator (concretize_inst amap inst).inst_opcode <=>
    is_terminator inst.inst_opcode
Proof
  rpt gen_tac >>
  simp[concretize_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `FLOOKUP amap h` >>
  gvs[mk_nop_inst_def, mk_assign_inst_def] >>
  imp_res_tac is_alloca_op_eq >> gvs[is_terminator_def]
QED

Triviality concretize_inst_phi_identity:
  !amap inst. inst.inst_opcode = PHI ==> concretize_inst amap inst = inst
Proof
  simp[concretize_inst_def, is_alloca_op_def]
QED

Triviality concretize_inst_phi_iff:
  !amap inst. (concretize_inst amap inst).inst_opcode = PHI <=> inst.inst_opcode = PHI
Proof
  rw[concretize_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[mk_assign_inst_def, mk_nop_inst_def, is_alloca_op_def]) >>
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]
QED

Triviality concretize_phi_prefix_length:
  !amap insts.
    phi_prefix_length (MAP (concretize_inst amap) insts) =
    phi_prefix_length insts
Proof
  gen_tac >> Induct >>
  simp[phi_prefix_length_def, concretize_inst_phi_iff]
QED

Triviality concretize_eval_phis_same_state:
  !amap s insts.
    eval_phis s (MAP (concretize_inst amap) insts) = eval_phis s insts
Proof
  gen_tac >> gen_tac >> Induct >>
  simp[eval_phis_def, concretize_inst_phi_iff, concretize_inst_phi_identity]
QED

Triviality concretize_bmt_phi_prefix_length:
  !amap bb.
    phi_prefix_length
      (block_map_transform (concretize_inst amap) bb).bb_instructions =
    phi_prefix_length bb.bb_instructions
Proof
  simp[block_map_transform_def, concretize_phi_prefix_length]
QED

Triviality concretize_bmt_eval_phis_same_state:
  !amap s bb.
    eval_phis s (block_map_transform (concretize_inst amap) bb).bb_instructions =
    eval_phis s bb.bb_instructions
Proof
  simp[block_map_transform_def, concretize_eval_phis_same_state]
QED

Triviality resolve_phi_MEM_operands_concretize:
  !prev ops val_op. resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  recInduct resolve_phi_ind >> rw[resolve_phi_def]
QED

Triviality concretize_rel_prev_bb:
  !amap fn livesets init s1 s2.
    concretize_rel amap fn livesets init s1 s2 ==>
    s1.vs_prev_bb = s2.vs_prev_bb
Proof
  rw[concretize_rel_def, LET_THM]
QED

Triviality concretize_phi_operand_non_pv:
  !amap fn livesets init bb inst out val_op prev s1 s2.
    ssa_form fn /\ amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\ MEM out inst.inst_outputs /\
    out NOTIN pointer_derived_vars fn (FDOM amap) /\
    resolve_phi prev inst.inst_operands = SOME val_op /\
    concretize_rel amap fn livesets init s1 s2 ==>
    eval_operand val_op s1 = eval_operand val_op s2
Proof
  rpt strip_tac >>
  Cases_on `val_op` >> simp[eval_operand_def]
  >- (
    `s NOTIN pointer_derived_vars fn (FDOM amap)` by (
      spose_not_then assume_tac >>
      `MEM (Var s) inst.inst_operands` by
        metis_tac[resolve_phi_MEM_operands_concretize] >>
      `pointer_confined fn (FDOM amap)` by
        fs[concretize_pointer_confined_def] >>
      fs[pointer_confined_def, LET_THM] >>
      first_x_assum (qspecl_then [`bb`, `inst`, `s`] mp_tac) >> simp[] >>
      strip_tac >> gvs[SUBSET_DEF, is_pointer_preserving_op_def,
                       memLocDefsTheory.mem_write_ops_def,
                       memLocDefsTheory.mem_read_ops_def] >>
      metis_tac[]) >>
    fs[concretize_rel_def, LET_THM, lookup_var_def]) >>
  fs[concretize_rel_def, LET_THM]
QED

Triviality concretize_phi_operand_pv:
  !amap fn livesets init bb inst out val_op prev s1 s2 w1.
    ssa_form fn /\ amap_from_allocas fn amap /\ fn_inst_wf fn /\
    phi_pv_all_var fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\ MEM out inst.inst_outputs /\
    out IN pointer_derived_vars fn (FDOM amap) /\
    resolve_phi prev inst.inst_operands = SOME val_op /\
    eval_operand val_op s1 = SOME w1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?w2 aid orig_off sz addr.
      eval_operand val_op s2 = SOME w2 /\
      FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
      alloca_concrete_addr amap fn aid = SOME addr /\
      orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
      w1 - n2w orig_off = w2 - addr /\
      orig_off + sz < dimword (:256) /\
      w2n addr + sz < dimword (:256)
Proof
  rpt strip_tac >>
  `?pv_in. MEM (Var pv_in) inst.inst_operands /\
           pv_in IN pointer_derived_vars fn (FDOM amap)` by (
    irule pp_pv_output_has_pv_operand >>
    simp[is_pointer_preserving_op_def] >> metis_tac[]) >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  `?src. val_op = Var src` by (
    mp_tac (Q.SPECL [`prev`, `inst.inst_operands`, `val_op`]
      phi_resolve_is_var) >> simp[]) >>
  gvs[eval_operand_def] >>
  `src IN pointer_derived_vars fn (FDOM amap)` by (
    fs[phi_pv_all_var_def, LET_THM] >>
    first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >> simp[] >>
    strip_tac >>
    `MEM (Var src) inst.inst_operands` by
      metis_tac[resolve_phi_MEM_operands_concretize] >>
    metis_tac[]) >>
  `lookup_var src s1 <> NONE` by simp[] >>
  drule_all cr_pv_var_displacement >> strip_tac >> gvs[] >>
  qexistsl [`aid`, `orig_off`, `sz`, `addr`] >> simp[]
QED

Triviality concretize_phi_operand_pv_none:
  !amap fn livesets init bb inst out val_op prev s1 s2.
    ssa_form fn /\ amap_from_allocas fn amap /\ fn_inst_wf fn /\
    phi_pv_all_var fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\ MEM out inst.inst_outputs /\
    out IN pointer_derived_vars fn (FDOM amap) /\
    resolve_phi prev inst.inst_operands = SOME val_op /\
    eval_operand val_op s1 = NONE /\
    concretize_rel amap fn livesets init s1 s2 ==>
    eval_operand val_op s2 = NONE
Proof
  rpt strip_tac >>
  `?pv_in. MEM (Var pv_in) inst.inst_operands /\
           pv_in IN pointer_derived_vars fn (FDOM amap)` by (
    irule pp_pv_output_has_pv_operand >>
    simp[is_pointer_preserving_op_def] >> metis_tac[]) >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  `?src. val_op = Var src` by (
    mp_tac (Q.SPECL [`prev`, `inst.inst_operands`, `val_op`]
      phi_resolve_is_var) >> simp[]) >>
  gvs[eval_operand_def] >>
  `src IN pointer_derived_vars fn (FDOM amap)` by (
    fs[phi_pv_all_var_def, LET_THM] >>
    first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >> simp[] >>
    strip_tac >>
    `MEM (Var src) inst.inst_operands` by
      metis_tac[resolve_phi_MEM_operands_concretize] >>
    metis_tac[]) >>
  drule_all cr_pv_var_none >> simp[]
QED

Triviality eval_one_phi_pv_source:
  !fn amap bb inst s out w.
    ssa_form fn /\ amap_from_allocas fn amap /\ fn_inst_wf fn /\
    phi_pv_all_var fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\
    out IN pointer_derived_vars fn (FDOM amap) /\
    eval_one_phi s inst = SOME (out,w) ==>
    ?src. src IN pointer_derived_vars fn (FDOM amap) /\ lookup_var src s = SOME w
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `s.vs_prev_bb` >> gvs[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> gvs[] >>
  Cases_on `eval_operand x' s` >> gvs[] >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  `?pv_in. MEM (Var pv_in) inst.inst_operands /\
           pv_in IN pointer_derived_vars fn (FDOM amap)` by (
    irule pp_pv_output_has_pv_operand >>
    simp[is_pointer_preserving_op_def] >> metis_tac[]) >>
  `?src. x' = Var src` by (
    mp_tac (Q.SPECL [`x`, `inst.inst_operands`, `x'`]
      phi_resolve_is_var) >> simp[]) >>
  gvs[eval_operand_def] >>
  `MEM (Var src) inst.inst_operands` by
    metis_tac[resolve_phi_MEM_operands_concretize] >>
  qexists `src` >> simp[] >>
  fs[phi_pv_all_var_def, LET_THM] >>
  first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Triviality eval_phis_pv_lookup_source:
  !amap fn bb insts s s' y w.
    ssa_form fn /\ amap_from_allocas fn amap /\ fn_inst_wf fn /\
    phi_pv_all_var fn (FDOM amap) /\ MEM bb fn.fn_blocks /\
    (!inst. MEM inst insts ==> MEM inst bb.bb_instructions) /\
    eval_phis s insts = OK s' /\
    y IN pointer_derived_vars fn (FDOM amap) /\
    lookup_var y s' = SOME w ==>
    ?src. src IN pointer_derived_vars fn (FDOM amap) /\ lookup_var src s = SOME w
Proof
  gen_tac >> gen_tac >> gen_tac >> Induct >>
  simp[eval_phis_def, lookup_var_def] >> rpt strip_tac
  >- metis_tac[] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[]
  >- (
    Cases_on `eval_one_phi s h` >> gvs[] >>
    PairCases_on `x` >> gvs[] >>
    Cases_on `eval_phis s insts` >> gvs[] >>
    gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
    Cases_on `y = x0` >> gvs[]
    >- (
      mp_tac (Q.SPECL [`fn`, `amap`, `bb`, `h`, `s`, `x0`, `w`]
        eval_one_phi_pv_source) >>
      impl_tac >- simp[] >>
      strip_tac >> qexists `src` >> fs[lookup_var_def]) >>
    first_x_assum irule >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Triviality concretize_eval_one_phi_none:
  !amap fn livesets init bb inst s1 s2.
    ssa_form fn /\ amap_from_allocas fn amap /\ fn_inst_wf fn /\
    concretize_pointer_confined fn amap /\ phi_pv_all_var fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\
    concretize_rel amap fn livesets init s1 s2 /\
    eval_one_phi s1 inst = NONE ==>
    eval_one_phi s2 inst = NONE
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def] >>
  Cases_on `inst.inst_outputs` >> gvs[eval_one_phi_def] >>
  reverse (Cases_on `t`) >-
    (Cases_on `s1.vs_prev_bb` >> Cases_on `s2.vs_prev_bb` >>
     gvs[eval_one_phi_def]) >>
  gvs[eval_one_phi_def] >>
  Cases_on `s1.vs_prev_bb` >> gvs[]
  >- (sg `s2.vs_prev_bb = NONE` >- fs[concretize_rel_def, LET_THM] >> simp[]) >>
  sg `s2.vs_prev_bb = SOME x`
  >- fs[concretize_rel_def, LET_THM] >>
  simp[] >>
  Cases_on `resolve_phi x inst.inst_operands`
  >- simp[] >>
  gvs[] >>
  Cases_on `h IN pointer_derived_vars fn (FDOM amap)`
  >- (
    Cases_on `eval_operand (THE (resolve_phi x inst.inst_operands)) s1` >> gvs[] >>
    mp_tac (Q.SPECL
      [`amap`, `fn`, `livesets`, `init`, `bb`, `inst`, `h`,
       `THE (resolve_phi x inst.inst_operands)`, `x`, `s1`, `s2`]
      concretize_phi_operand_pv_none) >>
    simp[]) >>
  Cases_on `THE (resolve_phi x inst.inst_operands)` >> gvs[eval_operand_def]
  >- (
    `s NOTIN pointer_derived_vars fn (FDOM amap)` by (
      spose_not_then assume_tac >>
      `MEM (Var s) inst.inst_operands` by
        metis_tac[resolve_phi_MEM_operands_concretize] >>
      `pointer_confined fn (FDOM amap)` by
        fs[concretize_pointer_confined_def] >>
      fs[pointer_confined_def, LET_THM] >>
      first_x_assum (qspecl_then [`bb`, `inst`, `s`] mp_tac) >> simp[] >>
      strip_tac >> gvs[SUBSET_DEF, is_pointer_preserving_op_def,
                       memLocDefsTheory.mem_write_ops_def,
                       memLocDefsTheory.mem_read_ops_def] >>
      metis_tac[]) >>
    fs[concretize_rel_def, LET_THM, lookup_var_def] >>
    res_tac >> gvs[]) >>
  fs[concretize_rel_def, LET_THM] >> gvs[]
QED

Triviality concretize_eval_one_phi_some:
  !amap fn livesets init bb inst s1 s2 out w1 t1 t2.
    ssa_form fn /\ amap_from_allocas fn amap /\ fn_inst_wf fn /\
    concretize_pointer_confined fn amap /\ phi_pv_all_var fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\
    concretize_rel amap fn livesets init s1 s2 /\
    concretize_rel amap fn livesets init t1 t2 /\
    t1.vs_allocas = s1.vs_allocas /\
    eval_one_phi s1 inst = SOME (out, w1) ==>
    ?w2.
      eval_one_phi s2 inst = SOME (out, w2) /\
      concretize_rel amap fn livesets init
        (update_var out w1 t1) (update_var out w2 t2)
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `s1.vs_prev_bb` >> gvs[] >>
  sg `s2.vs_prev_bb = SOME x`
  >- fs[concretize_rel_def, LET_THM] >>
  simp[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> gvs[] >>
  Cases_on `eval_operand (THE (resolve_phi x inst.inst_operands)) s1` >> gvs[] >>
  Cases_on `h IN pointer_derived_vars fn (FDOM amap)`
  >- (
    mp_tac (Q.SPECL
      [`amap`, `fn`, `livesets`, `init`, `bb`, `inst`, `h`,
       `THE (resolve_phi x inst.inst_operands)`, `x`, `s1`, `s2`, `w1`]
      concretize_phi_operand_pv) >>
    impl_tac >- gvs[] >>
    strip_tac >> gvs[] >>
    irule cr_update_var_pv >> simp[] >>
    qexistsl [`addr`, `aid`, `orig_off`, `sz`] >> simp[]) >>
  mp_tac (Q.SPECL
    [`amap`, `fn`, `livesets`, `init`, `bb`, `inst`, `h`,
     `THE (resolve_phi x inst.inst_operands)`, `x`, `s1`, `s2`]
    concretize_phi_operand_non_pv) >>
  impl_tac >- gvs[] >>
  strip_tac >> gvs[] >>
  qexists `w1` >>
  conj_tac >- (
    qpat_x_assum `SOME w1 = eval_operand x' s2` (SUBST1_TAC o SYM) >>
    simp[]) >>
  irule cr_update_var_non_pv >> simp[]
QED

Triviality concretize_eval_phis_rel:
  !amap fn livesets init bb insts s1 s2.
    ssa_form fn /\ amap_from_allocas fn amap /\ fn_inst_wf fn /\
    concretize_pointer_confined fn amap /\ phi_pv_all_var fn (FDOM amap) /\
    MEM bb fn.fn_blocks /\
    (!inst. MEM inst insts ==> MEM inst bb.bb_instructions) /\
    concretize_rel amap fn livesets init s1 s2 ==>
    lift_result
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (concretize_rel amap fn livesets init)
      (eval_phis s1 insts) (eval_phis s2 insts)
Proof
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  Induct >> rpt strip_tac >> simp[eval_phis_def, lift_result_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[lift_result_def]
  >- (
    `MEM h bb.bb_instructions` by metis_tac[MEM] >>
    Cases_on `eval_one_phi s1 h`
    >- (
      `eval_one_phi s2 h = NONE` by
        (irule concretize_eval_one_phi_none >> simp[] >> metis_tac[]) >>
      simp[lift_result_def]) >>
    PairCases_on `x` >>
    `lift_result
       (concretize_rel amap fn livesets init)
       (concretize_rel amap fn livesets init)
       (concretize_rel amap fn livesets init)
       (eval_phis s1 insts) (eval_phis s2 insts)` by (
      first_x_assum irule >> simp[] >> metis_tac[]) >>
    DISJ_CASES_TAC (Q.SPECL [`s1`, `insts`] eval_phis_ok_or_error_defs)
    >- (
      DISJ_CASES_TAC (Q.SPECL [`s2`, `insts`] eval_phis_ok_or_error_defs)
      >- (
        gvs[lift_result_def] >>
        TRY (Cases_on `eval_one_phi s2 h` >> gvs[lift_result_def] >> NO_TAC) >>
        rename1 `eval_phis s1 insts = OK s1_tail` >>
        rename1 `eval_phis s2 insts = OK s2_tail` >>
        `concretize_rel amap fn livesets init s1_tail s2_tail` by (
          first_x_assum (qspecl_then [`s1`, `s2`] mp_tac) >>
          simp[lift_result_def]) >>
        `s1_tail.vs_allocas = s1.vs_allocas` by (
          mp_tac (Q.SPECL [`s1`, `insts`, `s1_tail`]
            venomExecProofsTheory.eval_phis_preserves_alloca_fields) >>
          simp[]) >>
        mp_tac (Q.SPECL
          [`amap`, `fn`, `livesets`, `init`, `bb`, `h`,
           `s1`, `s2`, `x0`, `x1`, `s1_tail`, `s2_tail`]
          concretize_eval_one_phi_some) >>
        impl_tac >- simp[] >>
        strip_tac >> gvs[lift_result_def]) >>
      first_x_assum (qspecl_then [`s1`, `s2`] mp_tac) >>
      gvs[lift_result_def]) >>
    gvs[lift_result_def] >>
    first_x_assum (qspecl_then [`s1`, `s2`] mp_tac) >>
    simp[lift_result_def] >>
    Cases_on `eval_phis s2 insts` >> gvs[lift_result_def] >>
    Cases_on `eval_one_phi s2 h` >> gvs[lift_result_def] >>
    PairCases_on `x` >> gvs[lift_result_def]) >>
  fs[concretize_rel_def, LET_THM]
QED

(* ALLOCA instructions have [Lit sz] operands and single output *)
Triviality alloca_inst_shape:
  !fn bb inst.
    fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = ALLOCA ==>
    ?sz out. inst.inst_operands = [Lit sz] /\ inst.inst_outputs = [out]
Proof
  rw[fn_inst_wf_def, EVERY_MEM] >> res_tac >>
  gvs[inst_wf_def] >>
  Cases_on `inst.inst_outputs` >> fs[] >>
  Cases_on `t` >> fs[]
QED

(* alloca_inv preserved by step_inst_base (via step_inst_non_invoke) *)
Triviality alloca_inv_step_inst_base:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    inst.inst_opcode <> INVOKE /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rpt strip_tac >>
  `step_inst ARB ARB inst s = OK s'` by simp[step_inst_non_invoke] >>
  metis_tac[alloca_inv_step_inst_proof]
QED

(* alloca_inv preserved by vs_inst_idx update *)
Triviality alloca_inv_update_inst_idx:
  !s n. alloca_inv s ==> alloca_inv (s with vs_inst_idx := n)
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED


(* General: removing one element from a SUM over MAP/FILTER *)
Triviality SUM_MAP_FILTER_REMOVE:
  !(f:'a -> num) P l x.
    ALL_DISTINCT l /\ MEM x l /\ P x ==>
    SUM (MAP f (FILTER (\y. P y /\ y <> x) l)) =
    SUM (MAP f (FILTER P l)) - f x
Proof
  gen_tac >> gen_tac >> Induct >> simp[FILTER] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- ( (* x = h: h is removed, FILTER on rest is unchanged *)
    `FILTER (\y. P y /\ y <> h) l = FILTER P l` by
      (simp[rich_listTheory.FILTER_EQ] >> metis_tac[]) >>
    simp[])
  >- ( (* x in tail: h <> x because ~MEM h l and MEM x l *)
    `h <> x` by metis_tac[] >>
    Cases_on `P h` >> simp[] >>
    first_x_assum drule_all >> strip_tac >>
    `f x <= SUM (MAP f (FILTER P l))` by
      (`MEM x (FILTER P l)` by simp[MEM_FILTER] >>
       pop_assum (mp_tac o MATCH_MP SUM_MAP_MEM_bound) >> simp[]) >>
    simp[])
QED

(* inst_id distinct => element-level distinct for FILTER'ed ALLOCA list *)
Triviality filter_alloca_inst_id_eq:
  !l (inst:instruction).
    ALL_DISTINCT (MAP (\i. i.inst_id) l) /\ MEM inst l ==>
    !P. FILTER (\i. P i /\ i.inst_id <> inst.inst_id) l =
        FILTER (\i. P i /\ i <> inst) l
Proof
  Induct >> simp[FILTER] >> rpt strip_tac >> gvs[] >>
  (* h not in l => i.inst_id <> h.inst_id for all i in l *)
  `!i. MEM i l ==> i.inst_id <> h.inst_id /\ i <> h` by
    (rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
  simp[rich_listTheory.FILTER_EQ]
QED

(* fn_remaining decreases by alloc_size when a fresh ALLOCA executes *)
Triviality fn_remaining_alloca_step:
  !fn s inst sz v.
    fn_inst_ids_distinct fn /\
    MEM inst (fn_insts fn) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
    FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
    fn_remaining_alloca_size fn
      (s with vs_allocas := s.vs_allocas |+ (inst.inst_id, v)) =
    fn_remaining_alloca_size fn s - w2n sz
Proof
  rpt strip_tac >>
  simp[fn_remaining_alloca_size_def, FDOM_FUPDATE] >>
  qabbrev_tac `f = \i:instruction.
    case i.inst_operands of [Lit sz'] => w2n sz' | _ => 0` >>
  qabbrev_tac `P = \i:instruction.
    i.inst_opcode = ALLOCA /\ i.inst_id NOTIN FDOM s.vs_allocas` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    gvs[fn_inst_ids_distinct_alt] >>
  `P inst` by (simp[Abbr `P`] >> fs[flookup_thm]) >>
  `f inst = w2n sz` by simp[Abbr `f`] >>
  (* Rewrite goal's FILTER pred: expand P, combine with inst_id <> *)
  `(\i:instruction. i.inst_opcode = ALLOCA /\ i.inst_id <> inst.inst_id /\
      i.inst_id NOTIN FDOM s.vs_allocas) =
   (\i. P i /\ i.inst_id <> inst.inst_id)` by
    (simp[FUN_EQ_THM, Abbr `P`] >> metis_tac[]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  drule_all filter_alloca_inst_id_eq >>
  disch_then (qspec_then `P` (fn th => REWRITE_TAC[th])) >>
  `ALL_DISTINCT (fn_insts fn)` by metis_tac[ALL_DISTINCT_MAP] >>
  drule_all SUM_MAP_FILTER_REMOVE >> simp[]
QED

(* alloca_overflow_safe preserved by vs_inst_idx update *)
Triviality alloca_overflow_safe_update_inst_idx:
  !fn amap s n.
    alloca_overflow_safe fn amap s ==>
    alloca_overflow_safe fn amap (s with vs_inst_idx := n)
Proof
  rw[alloca_overflow_safe_def, fn_remaining_alloca_size_def, fn_insts_def]
  >> metis_tac[]
QED

(* If an element x satisfies P and is MEM l, then f(x) <= SUM (MAP f (FILTER P l)) *)
Triviality MEM_SUM_FILTER_LE:
  !f P l (x:'a). MEM x l /\ P x ==>
    f x <= SUM (MAP f (FILTER P l))
Proof
  gen_tac >> gen_tac >> Induct >> simp[FILTER] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `P h` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

(* An unexecuted ALLOCA's size is bounded by the remaining alloca budget *)
Triviality alloca_size_le_remaining:
  !fn s inst sz bb.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
    FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
    w2n sz <= fn_remaining_alloca_size fn s
Proof
  rpt strip_tac >>
  simp[fn_remaining_alloca_size_def] >>
  `MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts] >>
  qmatch_goalsub_abbrev_tac `SUM (MAP f (FILTER P _))` >>
  `MEM inst (FILTER P (fn_insts fn))` by
    (rw[MEM_FILTER, Abbr `P`] >> fs[flookup_thm]) >>
  drule SUM_MAP_MEM_bound >> disch_then (qspec_then `f` mp_tac) >>
  simp[Abbr `f`]
QED

(* Helper: alloca step through step_inst (not step_inst_base).
   Wraps concretize_step_alloca_assign with step_inst_non_invoke. *)
Triviality alloca_step_inst_sim:
  !inst bb amap fn livesets init s1 s2 fuel ctx.
    fn_inst_wf fn /\ ssa_form fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_alloca_op inst.inst_opcode /\
    all_allocas_mapped fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'. lift_result
      (concretize_rel amap fn livesets init')
      (concretize_rel amap fn livesets init')
      (concretize_rel amap fn livesets init')
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx (concretize_inst amap inst) s2)
Proof
  rpt strip_tac >>
  `inst.inst_opcode = ALLOCA` by metis_tac[is_alloca_op_eq] >>
  drule_all alloca_inst_shape >> strip_tac >> gvs[] >>
  `out IN FDOM amap` by (fs[all_allocas_mapped_def] >> metis_tac[]) >>
  `?addr. FLOOKUP amap out = SOME addr` by (fs[FLOOKUP_DEF] >> metis_tac[]) >>
  `concretize_inst amap inst = mk_assign_inst inst (Lit addr)` by
    (irule concretize_inst_alloca_assign >> simp[]) >>
  `(mk_assign_inst inst (Lit addr)).inst_opcode <> INVOKE` by
    simp[mk_assign_inst_def] >>
  simp[step_inst_non_invoke] >>
  irule concretize_step_alloca_assign >> simp[] >>
  fs[alloca_overflow_safe_def] >>
  rpt conj_tac >> TRY (metis_tac[]) >>
  TRY (`0 <= fn_remaining_alloca_size fn s1` by simp[] >> simp[]) >>
  rpt strip_tac >> drule_all alloca_size_le_remaining >> simp[]
QED

(* FIND with predicate Q /\ id = FIND with id /\ Q (needed because
   find_by_inst_id puts inst_id first, but get_alloca_size_def puts Q first) *)
Triviality find_by_inst_id_alt:
  !Q l inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) l) /\
    MEM inst l /\ Q inst ==>
    FIND (\i. Q i /\ i.inst_id = inst.inst_id) l = SOME inst
Proof
  gen_tac >>
  Induct >> simp[FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[ALL_DISTINCT_APPEND, MEM_MAP]
QED

(* get_alloca_size for a known ALLOCA instruction in the function *)
Triviality get_alloca_size_from_inst:
  !fn bb inst sz.
    fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] ==>
    get_alloca_size fn (Allocation inst.inst_id) = w2n sz
Proof
  rpt strip_tac >>
  simp[get_alloca_size_def] >>
  `MEM inst (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks))` by
    (`MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts] >>
     gvs[fn_insts_def, fn_insts_blocks_flat]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
     (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)))` by
    gvs[fn_inst_ids_distinct_alt, fn_insts_def, fn_insts_blocks_flat] >>
  `FIND (\i. is_alloca_op i.inst_opcode /\ i.inst_id = inst.inst_id)
        (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)) = SOME inst` by
    (match_mp_tac (find_by_inst_id_alt |> Q.SPEC `is_alloca_op o inst_opcode`
       |> SIMP_RULE (srw_ss()) []) >> simp[is_alloca_op_def]) >>
  gvs[]
QED

(* alloca_sizes_match preserved by step_inst for non-INVOKE instructions *)
Triviality alloca_sizes_match_step_inst:
  !fuel ctx inst s s' fn bb.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode <> INVOKE /\
    alloca_sizes_match fn s /\
    fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    alloca_sizes_match fn s'
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- ( (* ALLOCA case *)
    `inst.inst_opcode = ALLOCA` by metis_tac[is_alloca_op_eq] >>
    drule_all alloca_inst_shape >> strip_tac >> gvs[] >>
    `get_alloca_size fn (Allocation inst.inst_id) = w2n sz` by
      (irule get_alloca_size_from_inst >> metis_tac[]) >>
    fs[step_inst_base_def] >>
    gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
    rw[alloca_sizes_match_def] >> rpt strip_tac >>
    gvs[alloca_sizes_match_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
    metis_tac[])
  >- ( (* Non-ALLOCA: vs_allocas unchanged *)
    `inst.inst_opcode <> ALLOCA` by
      (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
    `s'.vs_allocas = s.vs_allocas` by
      (irule step_inst_base_preserves_allocas >> simp[] >> metis_tac[]) >>
    gvs[alloca_sizes_match_def])
QED

(* concretize_rel implies matching control flow fields *)
Triviality concretize_rel_fields:
  !amap fn livesets init s1 s2.
    concretize_rel amap fn livesets init s1 s2 ==>
    s1.vs_current_bb = s2.vs_current_bb /\
    (s1.vs_halted <=> s2.vs_halted)
Proof
  rw[concretize_rel_def, LET_THM]
QED

Triviality alloca_sizes_match_update_inst_idx:
  !fn s n.
    alloca_sizes_match fn s ==>
    alloca_sizes_match fn (s with vs_inst_idx := n)
Proof
  rw[alloca_sizes_match_def]
QED

Triviality alloca_write_before_read_update_inst_idx:
  !fn roots livesets init s n.
    alloca_write_before_read fn roots livesets init s ==>
    alloca_write_before_read fn roots livesets init (s with vs_inst_idx := n)
Proof
  rw[alloca_write_before_read_def, LET_THM, lookup_var_def]
QED

Triviality eval_operand_update_inst_idx:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases_on `op` >> rw[eval_operand_def, lookup_var_def]
QED

Triviality alloca_safe_access_update_inst_idx:
  !fn roots s n.
    alloca_safe_access fn roots s ==>
    alloca_safe_access fn roots (s with vs_inst_idx := n)
Proof
  rw[alloca_safe_access_def, LET_THM, lookup_var_def,
     eval_operand_update_inst_idx]
QED

Triviality concrete_allocas_non_overlapping_update_inst_idx:
  !amap fn s n.
    concrete_allocas_non_overlapping amap fn s ==>
    concrete_allocas_non_overlapping amap fn (s with vs_inst_idx := n)
Proof
  rw[concrete_allocas_non_overlapping_def]
QED

(* exec_block on the original basic block and on the block_map_transform
   (concretize_inst amap) block are related by concretize_rel. Handles
   PHI resolution, alloca→ASSIGN steps, and non-alloca identity steps
   within a single block. *)
Theorem exec_block_bmt_sim:
  !n bb amap fn livesets init fuel ctx s1 s2.
    n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    fn_inst_wf fn /\ ssa_form fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s ==>
       alloca_overflow_safe fn amap s') /\
    (!fuel0 ctx0 inst0 s s' init0 init1.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
    EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions /\
    concretize_rel amap fn livesets init s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx
           (block_map_transform (concretize_inst amap) bb) s2)
Proof
  Induct_on `n`
  >- (
    rpt strip_tac >>
    `~(s1.vs_inst_idx < LENGTH bb.bb_instructions)` by DECIDE_TAC >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    gvs[get_instruction_bmt, get_instruction_def, lift_result_def]) >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_bmt] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >- (
    gvs[lift_result_def]) >>
  rename1 `get_instruction bb s1.vs_inst_idx = SOME inst` >>
  gvs[] >>
  `MEM inst bb.bb_instructions` by (
    fs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  (* Get step-level lift_result for either case *)
  `?init'. lift_result
     (concretize_rel amap fn livesets init')
     (concretize_rel amap fn livesets init')
     (concretize_rel amap fn livesets init')
     (step_inst fuel ctx inst s1)
     (step_inst fuel ctx (concretize_inst amap inst) s2)` by (
    Cases_on `is_alloca_op inst.inst_opcode`
    >- (irule alloca_step_inst_sim >> simp[] >> metis_tac[])
    >- (
      (* Non-alloca: concretize_inst amap inst = inst *)
      `concretize_inst amap inst = inst` by simp[concretize_inst_def] >>
      simp[] >>
      `inst.inst_opcode <> INVOKE` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `inst.inst_opcode <> NOP` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `inst.inst_opcode <> MEMTOP` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `inst.inst_opcode <> LOG` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `inst.inst_opcode <> MCOPY` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `inst.inst_opcode <> EXTCODECOPY` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `inst.inst_opcode <> DRET` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `~is_ext_call_op inst.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
      simp[step_inst_non_invoke] >>
      irule concretize_step_inst_base_identity >> simp[] >> metis_tac[])) >>
  (* Case split step results to wire into block *)
  pop_assum strip_assume_tac >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx (concretize_inst amap inst) s2` >>
  gvs[lift_result_def] >>
  (* All non-matching constructor pairs eliminated by F in assumptions.
     Remaining same-constructor pairs: OK/OK needs terminator handling,
     Halt/Halt, Abort/Abort, IntRet/IntRet just witness with init'. *)
  TRY (qexists `init'` >> simp[lift_result_def] >> NO_TAC) >>
  (* Only OK/OK remains: handle terminator vs non-terminator *)
  `is_terminator (concretize_inst amap inst).inst_opcode <=>
   is_terminator inst.inst_opcode` by
    simp[concretize_inst_is_terminator] >>
  simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- ( (* terminator: halted check *)
    `v.vs_halted <=> v'.vs_halted` by (
      imp_res_tac concretize_rel_fields >> simp[]) >>
    Cases_on `v.vs_halted` >> gvs[] >>
    qexists `init'` >> simp[lift_result_def])
  >- ( (* non-terminator: use IH *)
    `n = LENGTH bb.bb_instructions -
       (v with vs_inst_idx := SUC s2.vs_inst_idx).vs_inst_idx` by
      (fs[get_instruction_def, AllCaseEqs()] >> DECIDE_TAC) >>
    `alloca_inv (v with vs_inst_idx := SUC s2.vs_inst_idx)` by
      (irule alloca_inv_update_inst_idx >>
       metis_tac[alloca_inv_step_inst_proof]) >>
    `alloca_overflow_safe fn amap (v with vs_inst_idx := SUC s2.vs_inst_idx)` by
      (irule alloca_overflow_safe_update_inst_idx >>
       qpat_x_assum `!fuel0 ctx0 inst0 s s'.
         MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
         ~is_terminator inst0.inst_opcode /\
         alloca_overflow_safe fn amap s ==>
         alloca_overflow_safe fn amap s'`
         (qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `v`] mp_tac) >>
       simp[]) >>
    `alloca_write_before_read fn (FDOM amap) livesets init'
       (v with vs_inst_idx := SUC s2.vs_inst_idx)` by
      (irule alloca_write_before_read_update_inst_idx >>
       qpat_x_assum `!fuel0 ctx0 inst0 s s' init0 init1.
         MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
         ~is_terminator inst0.inst_opcode /\
         alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
         alloca_write_before_read fn (FDOM amap) livesets init1 s'`
         (qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `v`, `init`, `init'`] mp_tac) >>
       simp[]) >>
    `alloca_safe_access fn (FDOM amap) (v with vs_inst_idx := SUC s2.vs_inst_idx)` by
      (irule alloca_safe_access_update_inst_idx >>
       qpat_x_assum `!fuel0 ctx0 inst0 s s'.
         MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
         ~is_terminator inst0.inst_opcode /\
         alloca_safe_access fn (FDOM amap) s ==>
         alloca_safe_access fn (FDOM amap) s'`
         (qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `v`] mp_tac) >>
       simp[]) >>
    `concrete_allocas_non_overlapping amap fn
       (v with vs_inst_idx := SUC s2.vs_inst_idx)` by
      (irule concrete_allocas_non_overlapping_update_inst_idx >>
       qpat_x_assum `!fuel0 ctx0 inst0 s s'.
         MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
         ~is_terminator inst0.inst_opcode /\
         concrete_allocas_non_overlapping amap fn s ==>
         concrete_allocas_non_overlapping amap fn s'`
         (qspecl_then [`fuel`, `ctx`, `inst`, `s1`, `v`] mp_tac) >>
       simp[]) >>
    `alloca_sizes_match fn (v with vs_inst_idx := SUC s2.vs_inst_idx)` by
      (irule alloca_sizes_match_update_inst_idx >>
       match_mp_tac alloca_sizes_match_step_inst >>
       MAP_EVERY qexists [`fuel`, `ctx`, `inst`, `s1`, `bb`] >>
       simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
    `concretize_rel amap fn livesets init'
       (v with vs_inst_idx := SUC s2.vs_inst_idx)
       (v' with vs_inst_idx := SUC s2.vs_inst_idx)` by
      (irule concretize_rel_update_inst_idx >> simp[]) >>
    qpat_x_assum `!bb amap fn livesets init fuel ctx s1 s2.
      _ ==> ?init'. lift_result _ _ _ (run_block_non_phis fuel ctx bb s1) _`
      (qspecl_then [`bb`, `amap`, `fn`, `livesets`, `init'`, `fuel`, `ctx`,
        `v with vs_inst_idx := SUC s2.vs_inst_idx`,
        `v' with vs_inst_idx := SUC s2.vs_inst_idx`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
    simp[])
QED

(* exec_block on the original block vs exec_block on the concretized block
   (clear_nops ∘ block_map_transform ∘ concretize_inst) preserves concretize_rel.
   Under all_allocas_mapped and no input NOPs, clear_nops is identity, so
   this reduces to exec_block_bmt_sim. *)
Theorem concretize_exec_block_sim:
  !bb amap fn livesets init fuel ctx s1 s2.
    fn_inst_wf fn /\ ssa_form fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s ==>
       alloca_overflow_safe fn amap s') /\
    (!fuel0 ctx0 inst0 s s' init0 init1.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel0 ctx0 inst0 s s'.
       MEM inst0 bb.bb_instructions /\ step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
    EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions /\
    concretize_rel amap fn livesets init s1 s2 /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx
           (clear_nops_block
              (block_map_transform (concretize_inst amap) bb)) s2)
Proof
  rpt strip_tac >>
  `clear_nops_block (block_map_transform (concretize_inst amap) bb) =
   block_map_transform (concretize_inst amap) bb` by
    (irule clear_nops_bmt_identity >> metis_tac[]) >>
  simp[] >>
  irule exec_block_bmt_sim >> simp[] >> metis_tac[]
QED

(* alloca_sizes_match preserved by exec_block for non-INVOKE blocks *)
Triviality alloca_sizes_match_exec_block:
  !n fuel ctx bb s s' fn.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    exec_block fuel ctx bb s = OK s' /\
    alloca_sizes_match fn s /\
    fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions ==>
    alloca_sizes_match fn s'
Proof
  Induct_on `n`
  >- (
    rpt strip_tac >>
    `~(s.vs_inst_idx < LENGTH bb.bb_instructions)` by DECIDE_TAC >>
    fs[Once exec_block_def, get_instruction_def])
  >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `MEM inst bb.bb_instructions` by (
    fs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `inst.inst_opcode <> INVOKE` by (fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[AllCaseEqs()] >>
  strip_tac >> gvs[]
  >- ( (* terminator, not halted: s' from step_inst directly *)
    irule alloca_sizes_match_step_inst >> metis_tac[])
  >- ( (* non-terminator: use IH *)
    sg `alloca_sizes_match fn v`
    >- (drule_all alloca_sizes_match_step_inst >> simp[]) >>
    sg `alloca_sizes_match fn (v with vs_inst_idx := SUC s.vs_inst_idx)`
    >- (irule alloca_sizes_match_update_inst_idx >> simp[]) >>
    sg `n = LENGTH bb.bb_instructions - SUC s.vs_inst_idx`
    >- (fs[get_instruction_def, AllCaseEqs()] >> DECIDE_TAC) >>
    first_x_assum irule >> simp[] >>
    qexists `bb` >> qexists `ctx` >> qexists `fuel` >>
    qexists `v with vs_inst_idx := SUC s.vs_inst_idx` >>
    simp[])
QED

Triviality alloca_overflow_safe_state_eq:
  !fn amap s s'.
    alloca_overflow_safe fn amap s /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    s'.vs_memory = s.vs_memory ==>
    alloca_overflow_safe fn amap s'
Proof
  rw[alloca_overflow_safe_def, fn_remaining_alloca_size_def] >> metis_tac[]
QED

val terminator_alloca_frame_tac =
  gvs[step_inst_base_def, LET_THM] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >>
       gvs[jump_to_def, halt_state_def, revert_state_def,
           set_returndata_def]);

Triviality step_terminator_ok_preserves_alloca_overflow_safe:
  !fuel ctx inst s s' fn amap.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> DRET /\
    alloca_overflow_safe fn amap s ==>
    alloca_overflow_safe fn amap s'
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  gvs[step_inst_non_invoke] >>
  irule alloca_overflow_safe_state_eq >>
  qexists_tac `s` >> simp[] >>
  qpat_x_assum `is_terminator _` mp_tac >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def]
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
  >- terminator_alloca_frame_tac
QED

Triviality alloca_overflow_safe_exec_block:
  !n fuel ctx bb s s' fn amap.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    exec_block fuel ctx bb s = OK s' /\
    alloca_overflow_safe fn amap s /\
    MEM bb fn.fn_blocks /\
    EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
    (!fuel0 ctx0 bb inst0 s0 s1.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s0 = OK s1 /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s0 ==>
       alloca_overflow_safe fn amap s1) ==>
    alloca_overflow_safe fn amap s'
Proof
  Induct_on `n`
  >- (
    rpt strip_tac >>
    `~(s.vs_inst_idx < LENGTH bb.bb_instructions)` by DECIDE_TAC >>
    fs[Once exec_block_def, get_instruction_def]) >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `MEM inst bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `inst.inst_opcode <> DRET` by (fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[AllCaseEqs()] >>
  strip_tac >> gvs[]
  >- (irule step_terminator_ok_preserves_alloca_overflow_safe >> metis_tac[]) >>
  sg `alloca_overflow_safe fn amap v`
  >- (qpat_x_assum `!fuel0 ctx0 bb inst0 s0 s1. _`
        (qspecl_then [`fuel`, `ctx`, `bb`, `inst`, `s`, `v`] mp_tac) >>
      simp[]) >>
  sg `alloca_overflow_safe fn amap (v with vs_inst_idx := SUC s.vs_inst_idx)`
  >- (irule alloca_overflow_safe_update_inst_idx >> simp[]) >>
  sg `n = LENGTH bb.bb_instructions - SUC s.vs_inst_idx`
  >- (fs[get_instruction_def, AllCaseEqs()] >> DECIDE_TAC) >>
  qpat_x_assum `!fuel ctx bb s s' fn amap. _ ==> alloca_overflow_safe fn amap s'`
    (qspecl_then [`fuel`, `ctx`, `bb`,
       `v with vs_inst_idx := SUC s.vs_inst_idx`, `s'`, `fn`, `amap`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Triviality eval_phis_alloca_inv_update_inst_idx:
  !s insts s' n.
    eval_phis s insts = OK s' /\ alloca_inv s ==>
    alloca_inv (s' with vs_inst_idx := n)
Proof
  rw[] >>
  drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
  strip_tac >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Triviality alloca_overflow_safe_update_vars:
  !fn amap s vars.
    alloca_overflow_safe fn amap s ==>
    alloca_overflow_safe fn amap (s with vs_vars := vars)
Proof
  rw[alloca_overflow_safe_def, fn_remaining_alloca_size_def] >> metis_tac[]
QED

Triviality eval_phis_alloca_overflow_safe_update_inst_idx:
  !fn amap s insts s' n.
    eval_phis s insts = OK s' /\ alloca_overflow_safe fn amap s ==>
    alloca_overflow_safe fn amap (s' with vs_inst_idx := n)
Proof
  rw[] >>
  drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >> strip_tac >>
  gvs[] >>
  qpat_x_assum `s' = s with vs_vars := s'.vs_vars` SUBST1_TAC >>
  irule alloca_overflow_safe_update_inst_idx >>
  irule alloca_overflow_safe_update_vars >> simp[]
QED

Triviality eval_phis_alloca_write_before_read_update_inst_idx:
  !amap fn livesets init bb insts s s' n.
    ssa_form fn /\ amap_from_allocas fn amap /\ fn_inst_wf fn /\
    phi_pv_all_var fn (FDOM amap) /\ MEM bb fn.fn_blocks /\
    (!inst. MEM inst insts ==> MEM inst bb.bb_instructions) /\
    eval_phis s insts = OK s' /\
    alloca_write_before_read fn (FDOM amap) livesets init s ==>
    alloca_write_before_read fn (FDOM amap) livesets init
      (s' with vs_inst_idx := n)
Proof
  rw[alloca_write_before_read_def, LET_THM] >>
  rename1 `v IN pointer_derived_vars fn (FDOM amap)` >>
  rename1 `lookup_var v (s' with vs_inst_idx := n) = SOME w` >>
  `lookup_var v s' = SOME w` by fs[lookup_var_def] >>
  `?src. src IN pointer_derived_vars fn (FDOM amap) /\ lookup_var src s = SOME w` by (
    irule eval_phis_pv_lookup_source >> simp[] >> metis_tac[]) >>
  `s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `s'.vs_allocas = s.vs_allocas` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_alloca_fields] >>
  fs[alloca_write_before_read_def, LET_THM] >>
  first_x_assum (qspecl_then [`src`, `w`, `aid`, `off`, `sz`] mp_tac) >>
  simp[]
QED

Triviality eval_phis_concrete_allocas_non_overlapping_update_inst_idx:
  !amap fn s insts s' n.
    eval_phis s insts = OK s' /\ concrete_allocas_non_overlapping amap fn s ==>
    concrete_allocas_non_overlapping amap fn (s' with vs_inst_idx := n)
Proof
  rw[] >>
  drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
  strip_tac >>
  gvs[concrete_allocas_non_overlapping_def] >>
  first_assum ACCEPT_TAC
QED

Triviality eval_phis_alloca_sizes_match_update_inst_idx:
  !fn s insts s' n.
    eval_phis s insts = OK s' /\ alloca_sizes_match fn s ==>
    alloca_sizes_match fn (s' with vs_inst_idx := n)
Proof
  rw[] >>
  drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
  strip_tac >>
  gvs[alloca_sizes_match_def] >>
  first_assum ACCEPT_TAC
QED

(* --- 3c. Main theorem by fuel induction ---
   concretize_function = function_map_transform bt, proved above.
   Fuel induction following block_sim_function_inv_cross pattern. *)

(* Main correctness theorem: concretize_function amap fn produces a
   function that simulates the original under concretize_rel. Proved by
   fuel induction: each block step preserves the relation through PHI
   resolution, instruction-by-instruction simulation, and block
   continuation. *)
Theorem concretize_function_correct_proof:
  !amap fn livesets init fuel ctx s1 s2.
    venom_wf ctx /\ fn_inst_wf fn /\ ssa_form fn /\
    fn_inst_ids_distinct fn /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    (!bb s s' n.
       MEM bb fn.fn_blocks /\ eval_phis s bb.bb_instructions = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) (s' with vs_inst_idx := n)) /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel ctx bb s s' init0 init1.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s ==>
       alloca_overflow_safe fn amap s') /\
    (!fuel0 ctx0 bb inst0 s s' init0 init1.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    live_non_overlapping livesets amap fn /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
                EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions)
      fn.fn_blocks /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (run_blocks fuel ctx fn s1)
        (run_blocks fuel ctx (concretize_function amap fn) s2)
Proof
  REWRITE_TAC [concretize_function_as_fmt] >>
  MAP_EVERY qid_spec_tac [`s2`,`s1`,`init`] >>
  Induct_on `fuel`
  >- (rpt strip_tac >> qexists `init` >> simp[run_blocks_def, lift_result_def]) >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC [run_blocks_unfold] >>
  simp[function_map_transform_def] >>
  qabbrev_tac `bt = \bb. clear_nops_block
      (block_map_transform (concretize_inst amap) bb)` >>
  `!lbl. lookup_block lbl (MAP bt fn.fn_blocks) =
     OPTION_MAP bt (lookup_block lbl fn.fn_blocks)` by
    (strip_tac >> irule lookup_block_map_proof >>
     simp[Abbr `bt`, clear_nops_block_def, block_map_transform_def]) >>
  `s2.vs_current_bb = s1.vs_current_bb` by fs[concretize_rel_def, LET_THM] >>
  simp[] >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks`
  >- (qexists `init` >> simp[lift_result_def]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
   EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `clear_nops_block (block_map_transform (concretize_inst amap) bb) =
   block_map_transform (concretize_inst amap) bb` by
    metis_tac[clear_nops_bmt_identity] >>
  qunabbrev_tac `bt` >>
  simp[] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[concretize_bmt_eval_phis_same_state,
       concretize_bmt_phi_prefix_length] >>
  `lift_result
     (concretize_rel amap fn livesets init)
     (concretize_rel amap fn livesets init)
     (concretize_rel amap fn livesets init)
     (eval_phis s1 bb.bb_instructions)
     (eval_phis s2 bb.bb_instructions)` by
    (irule concretize_eval_phis_rel >> simp[] >> metis_tac[]) >>
  DISJ_CASES_TAC (Q.SPECL [`s1`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (
    DISJ_CASES_TAC (Q.SPECL [`s2`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
    >- (
      gvs[lift_result_def] >>
      rename1 `eval_phis s1 bb.bb_instructions = OK s1_phi` >>
      rename1 `eval_phis s2 bb.bb_instructions = OK s2_phi` >>
      qabbrev_tac `p = phi_prefix_length bb.bb_instructions` >>
      `concretize_rel amap fn livesets init s1_phi s2_phi` by
        first_assum ACCEPT_TAC >>
      `concretize_rel amap fn livesets init
         (s1_phi with vs_inst_idx := p) (s2_phi with vs_inst_idx := p)` by
        (irule concretize_rel_update_inst_idx >> simp[]) >>
      `alloca_inv (s1_phi with vs_inst_idx := p)` by
        metis_tac[eval_phis_alloca_inv_update_inst_idx] >>
      `alloca_overflow_safe fn amap (s1_phi with vs_inst_idx := p)` by
        metis_tac[eval_phis_alloca_overflow_safe_update_inst_idx] >>
      `alloca_write_before_read fn (FDOM amap) livesets init
         (s1_phi with vs_inst_idx := p)` by
        metis_tac[eval_phis_alloca_write_before_read_update_inst_idx] >>
      `alloca_safe_access fn (FDOM amap) (s1_phi with vs_inst_idx := p)` by (
        qpat_x_assum `!bb s s' n.
          MEM bb fn.fn_blocks /\ eval_phis s bb.bb_instructions = OK s' /\
          alloca_safe_access fn (FDOM amap) s ==>
          alloca_safe_access fn (FDOM amap) (s' with vs_inst_idx := n)`
          (qspecl_then [`bb`, `s1`, `s1_phi`, `p`] mp_tac) >>
        simp[]) >>
      `concrete_allocas_non_overlapping amap fn (s1_phi with vs_inst_idx := p)` by
        metis_tac[eval_phis_concrete_allocas_non_overlapping_update_inst_idx] >>
      `alloca_sizes_match fn (s1_phi with vs_inst_idx := p)` by
        metis_tac[eval_phis_alloca_sizes_match_update_inst_idx] >>
      `?init'. lift_result
         (concretize_rel amap fn livesets init')
         (concretize_rel amap fn livesets init')
         (concretize_rel amap fn livesets init')
         (exec_block fuel ctx bb (s1_phi with vs_inst_idx := p))
         (exec_block fuel ctx (block_map_transform (concretize_inst amap) bb)
            (s2_phi with vs_inst_idx := p))` by (
        irule exec_block_bmt_sim >> simp[Abbr `p`] >> metis_tac[]) >>
      pop_assum strip_assume_tac >>
      qpat_x_assum
        `lift_result (concretize_rel amap fn livesets init')
           (concretize_rel amap fn livesets init')
           (concretize_rel amap fn livesets init')
           (exec_block fuel ctx bb (s1_phi with vs_inst_idx := p))
           (exec_block fuel ctx
             (block_map_transform (concretize_inst amap) bb)
             (s2_phi with vs_inst_idx := p))` mp_tac >>
      (Cases_on `exec_block fuel ctx bb (s1_phi with vs_inst_idx := p)` THEN_LT
       TRYALL (Cases_on
         `exec_block fuel ctx (block_map_transform (concretize_inst amap) bb)
            (s2_phi with vs_inst_idx := p)`)) >>
      PURE_REWRITE_TAC[lift_result_def] >> simp_tac std_ss [] >> TRY strip_tac >>
      (ALL_TAC THEN_LT TRYALL
        (qpat_x_assum
           `exec_block fuel ctx bb (s1_phi with vs_inst_idx := p) = r1`
           (fn th => assume_tac th >> PURE_REWRITE_TAC[th]) >>
         qpat_x_assum
           `exec_block fuel ctx (block_map_transform (concretize_inst amap) bb)
              (s2_phi with vs_inst_idx := p) = r2`
           (fn th => assume_tac th >> PURE_REWRITE_TAC[th]))) >>
      (ALL_TAC THEN_LT TRYALL
        (qexists `init'` >> simp[lift_result_def] >>
         TRY (first_assum ACCEPT_TAC) >> NO_TAC)) >>
      simp_tac bool_ss [venomExecSemanticsTheory.exec_result_case_def] >>
      imp_res_tac concretize_rel_fields >>
      IF_CASES_TAC >> gvs[]
      >- (qexists `init'` >> simp[lift_result_def]) >>
      `alloca_inv v` by
        metis_tac[alloca_inv_exec_block_proof] >>
      `alloca_overflow_safe fn amap v` by (
        mp_tac (Q.SPECL [`LENGTH bb.bb_instructions - p`, `fuel`, `ctx`, `bb`,
          `s1_phi with vs_inst_idx := p`, `v`, `fn`, `amap`]
          alloca_overflow_safe_exec_block) >>
        simp[Abbr `p`] >> metis_tac[]) >>
      `alloca_write_before_read fn (FDOM amap) livesets init' v` by (
        qpat_x_assum `!fuel ctx bb s s' init0 init1.
          MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
          alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
          alloca_write_before_read fn (FDOM amap) livesets init1 s'`
          (qspecl_then [`fuel`, `ctx`, `bb`,
            `s1_phi with vs_inst_idx := p`, `v`, `init`, `init'`] mp_tac) >>
        simp[]) >>
      `alloca_safe_access fn (FDOM amap) v` by (
        qpat_x_assum `!fuel ctx bb s s'.
          MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
          alloca_safe_access fn (FDOM amap) s ==>
          alloca_safe_access fn (FDOM amap) s'`
          (qspecl_then [`fuel`, `ctx`, `bb`,
            `s1_phi with vs_inst_idx := p`, `v`] mp_tac) >>
        simp[]) >>
      `concrete_allocas_non_overlapping amap fn v` by (
        qpat_x_assum `!fuel ctx bb s s'.
          MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
          concrete_allocas_non_overlapping amap fn s ==>
          concrete_allocas_non_overlapping amap fn s'`
          (qspecl_then [`fuel`, `ctx`, `bb`,
            `s1_phi with vs_inst_idx := p`, `v`] mp_tac) >>
        simp[]) >>
      `alloca_sizes_match fn v` by (
        match_mp_tac alloca_sizes_match_exec_block >>
        MAP_EVERY qexists
          [`LENGTH bb.bb_instructions - p`, `fuel`, `ctx`, `bb`,
           `s1_phi with vs_inst_idx := p`] >>
        simp[Abbr `p`] >> metis_tac[]) >>
      last_x_assum
        (qspecl_then [`amap`, `fn`, `livesets`, `init'`, `ctx`, `v`, `v'`] mp_tac) >>
      PURE_REWRITE_TAC[function_map_transform_def] >>
      simp_tac std_ss [] >>
      impl_tac >- (rpt conj_tac >> simp[] >> metis_tac[]) >>
      disch_then (qx_choose_then `init''` assume_tac) >>
      qexists `init''` >> simp[function_map_transform_def]) >>
    gvs[lift_result_def]) >>
  gvs[lift_result_def] >>
  Cases_on `eval_phis s2 bb.bb_instructions` >> gvs[lift_result_def] >>
  qexists `init` >> simp[lift_result_def]
QED
