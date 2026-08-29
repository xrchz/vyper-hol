(*
 * Copy Forwarding — Semantic Equivalence Properties
 *
 * Semantic bridge between pointer_confined (structural: pointer-derived
 * vars only at memory-address or pointer-preserving positions) and
 * copy forwarding pass correctness (NOP mcopy + rewrite dst→src).
 *
 * Complements allocaRemapProofs which handles a different scenario:
 *   allocaRemap : same code, different alloca addresses, same content
 *   copyFwdEquiv: different code (operand rewrite), same addresses,
 *                 content differs at dead (dst) alloca
 *
 * The copy forwarding argument:
 *   1. invoke writes data D to src region
 *   2. mcopy (original) copies D to dst / nop (transformed) does nothing
 *   3. Rewritten instructions read from src (transformed) vs dst (original)
 *   4. Both regions have D → same values read → same observable output
 *   5. pointer_confined ensures pointer values never reach observable state
 *
 * TOP-LEVEL:
 *   cross_mem_region_equiv     — regions in different memories match
 *   mcopy_establishes_equiv    — mcopy makes dst content = src content
 *   mcopy_preserves_disjoint   — mcopy doesn't touch other regions
 *   copy_fwd_cross_equiv       — mcopy vs nop → cross equiv holds
 *   copy_fwd_rel               — simulation invariant for copy forwarding
 *   mload_cross_equiv          — MLOAD same result at cross-equiv regions
 *   copy_fwd_read_equiv        — read instruction: rewritten inst preserves rel
 *   copy_fwd_write_equiv       — write instruction: rewritten inst preserves rel
 *   copy_fwd_terminator_equiv  — terminator: rewritten inst preserves rel
 *   copy_fwd_rel_preserved_identical_inst — non-clobbering inst preserves invariant
 *)

Theory copyFwdEquiv
Ancestors
  allocaRemapDefs pointerConfinedDefs memLocDefs
  venomExecSemantics venomState stateEquiv
  finite_map list rich_list
Libs
  dep_rewrite

(* =========================================================================
   1. Cross-State Memory Region Equivalence
   ========================================================================= *)

(* Two memory regions in possibly-different memories have identical content.
   Uses mem_byte_at (from allocaRemapDefs) for OOB-safe byte access.
   This is the cross-state analog of alloca_mem_agrees (which is per-alloca). *)
Definition cross_mem_region_equiv_def:
  cross_mem_region_equiv
    (mem1 : word8 list) (addr1 : num)
    (mem2 : word8 list) (addr2 : num)
    (sz : num) ⇔
    ∀i. i < sz ⇒
      mem_byte_at mem1 (addr1 + i) = mem_byte_at mem2 (addr2 + i)
End

(* Symmetry *)
Theorem cross_mem_region_equiv_sym:
  ∀m1 a1 m2 a2 sz.
    cross_mem_region_equiv m1 a1 m2 a2 sz ⇒
    cross_mem_region_equiv m2 a2 m1 a1 sz
Proof
  rw[cross_mem_region_equiv_def]
QED

(* Sub-region *)
Theorem cross_mem_region_equiv_sub:
  ∀m1 a1 m2 a2 n k.
    cross_mem_region_equiv m1 a1 m2 a2 n ∧ k ≤ n ⇒
    cross_mem_region_equiv m1 a1 m2 a2 k
Proof
  rw[cross_mem_region_equiv_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

(* Reflexive when same memory, same address *)
Theorem cross_mem_region_equiv_refl:
  ∀mem addr sz. cross_mem_region_equiv mem addr mem addr sz
Proof
  rw[cross_mem_region_equiv_def]
QED

(* =========================================================================
   2. MCOPY and Region Equivalence — Helpers
   ========================================================================= *)

(* Reading from TAKE n (DROP m l ++ REPLICATE n 0w) equals mem_byte_at *)
Theorem take_drop_replicate_el:
  ∀i n m (l : word8 list).
    i < n ⇒
    EL i (TAKE n (DROP m l ++ REPLICATE n 0w)) = mem_byte_at l (m + i)
Proof
  rpt strip_tac >> simp[mem_byte_at_def, EL_TAKE, EL_APPEND_EQN, LENGTH_DROP] >>
  Cases_on `i < LENGTH l - m` >> simp[EL_DROP, EL_REPLICATE]
QED

(* Length of memory after write_memory_with_expansion *)
Theorem wmwe_length:
  ∀offset bytes s.
    LENGTH (write_memory_with_expansion offset bytes s).vs_memory ≥
    offset + LENGTH bytes
Proof
  rw[write_memory_with_expansion_def, LET_THM]
QED

(* The actual newmem in wmwe *)
Theorem wmwe_vs_memory:
  ∀offset bytes s.
    (write_memory_with_expansion offset bytes s).vs_memory =
    let mem = s.vs_memory in
    let needed = offset + LENGTH bytes − LENGTH mem in
    let expanded = if needed > 0 then mem ++ REPLICATE needed 0w
                   else mem in
    TAKE offset expanded ++ bytes ++ DROP (offset + LENGTH bytes) expanded
Proof
  rw[write_memory_with_expansion_def, LET_THM]
QED

(* write_memory_with_expansion: reading a written byte *)
Theorem wmwe_byte_at_written:
  ∀offset bytes s i.
    i < LENGTH bytes ⇒
    mem_byte_at (write_memory_with_expansion offset bytes s).vs_memory
      (offset + i) = EL i bytes
Proof
  rpt strip_tac >>
  rewrite_tac[wmwe_vs_memory] >> simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `TAKE offset expanded ++ bytes ++ _` >>
  `LENGTH expanded >= offset + LENGTH bytes` by
    (simp[Abbr `expanded`] >> IF_CASES_TAC >> simp[LENGTH_APPEND, LENGTH_REPLICATE]) >>
  simp[mem_byte_at_def, LENGTH_APPEND, LENGTH_TAKE_EQ, LENGTH_DROP,
       EL_APPEND_EQN]
QED

(* write_memory_with_expansion: reading an unwritten byte *)
Theorem wmwe_byte_at_outside:
  ∀offset bytes s addr.
    (addr < offset ∨ offset + LENGTH bytes ≤ addr) ⇒
    mem_byte_at (write_memory_with_expansion offset bytes s).vs_memory addr =
    mem_byte_at s.vs_memory addr
Proof
  rpt strip_tac >>
  rewrite_tac[wmwe_vs_memory] >> simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `TAKE offset expanded ++ _ ++ _` >>
  rename1 `Abbrev (expanded = if _ then mem ++ _ else mem)` >>
  `LENGTH expanded >= offset + LENGTH bytes ∧
   LENGTH expanded >= LENGTH mem ∧
   (∀a. a < LENGTH mem ⇒ EL a expanded = EL a mem)` by
    (simp[Abbr `expanded`] >> IF_CASES_TAC >>
     simp[LENGTH_APPEND, LENGTH_REPLICATE, EL_APPEND_EQN]) >>
  simp[mem_byte_at_def, LENGTH_APPEND, LENGTH_TAKE_EQ, LENGTH_DROP,
       EL_APPEND_EQN] >>
  rpt strip_tac >> gvs[EL_TAKE, EL_DROP] >>
  Cases_on `addr < LENGTH mem` >> gvs[] >>
  simp[Abbr `expanded`] >>
  rpt IF_CASES_TAC >>
  gvs[EL_APPEND_EQN, EL_REPLICATE, LENGTH_APPEND, LENGTH_REPLICATE]
QED

(* =========================================================================
   2b. MCOPY and Region Equivalence
   ========================================================================= *)

(* After mcopy dst src sz, each byte in [dst, dst+sz) equals the
   corresponding byte from [src, src+sz) in the PRE-copy memory.
   This is the foundational property of the copy. *)
(* LENGTH of mcopy data *)
Theorem mcopy_data_length:
  ∀src sz mem. LENGTH (TAKE sz (DROP src mem ++ REPLICATE sz 0w)) = sz
Proof
  simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP, LENGTH_REPLICATE]
QED

Theorem mcopy_establishes_equiv:
  ∀s dst src sz.
    let s' = mcopy dst src sz s in
    ∀i. i < sz ⇒
      mem_byte_at s'.vs_memory (dst + i) =
      mem_byte_at s.vs_memory (src + i)
Proof
  simp[mcopy_def, LET_THM] >> rpt strip_tac >>
  simp[wmwe_byte_at_written, mcopy_data_length, take_drop_replicate_el]
QED

(* mcopy does not modify bytes outside [dst, dst+sz).
   (It may expand memory with zeros, but those are beyond existing size.) *)
Theorem mcopy_preserves_disjoint:
  ∀s dst src sz addr region_sz.
    (addr + region_sz ≤ dst ∨ dst + sz ≤ addr) ⇒
    let s' = mcopy dst src sz s in
    ∀i. i < region_sz ⇒
      mem_byte_at s'.vs_memory (addr + i) =
      mem_byte_at s.vs_memory (addr + i)
Proof
  simp[mcopy_def, LET_THM] >> rpt strip_tac >>
  irule wmwe_byte_at_outside >> simp[mcopy_data_length]
QED

(* The cross-state property needed at the mcopy/nop divergence point.
   Original: mcopy ran → dst has data from src (pre-copy).
   Transformed: nop ran → src still has its data (unchanged).
   If src wasn't modified between invoke and copy, then
   dst-in-original and src-in-transformed have the same content. *)
Theorem copy_fwd_cross_equiv:
  ∀mem dst_addr src_addr sz.
    let mem_after_copy = (mcopy dst_addr src_addr sz
                           ((init_venom_state "") with vs_memory := mem)).vs_memory in
    cross_mem_region_equiv mem_after_copy dst_addr mem src_addr sz
Proof
  rw[cross_mem_region_equiv_def, LET_THM] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`((init_venom_state "") with vs_memory := mem)`, `dst_addr`, `src_addr`, `sz`]
    mcopy_establishes_equiv) >> simp[LET_THM] >>
  disch_then drule >> simp[]
QED

(* =========================================================================
   3. Memory Reads Under Cross-Equivalence
   ========================================================================= *)

(* Bridge: cross_mem_region_equiv implies TAKE/DROP equality
   (needed because mload/sha3/return use TAKE/DROP, not mem_byte_at). *)
Theorem cross_equiv_take_drop:
  ∀mem1 addr1 mem2 addr2 sz.
    cross_mem_region_equiv mem1 addr1 mem2 addr2 sz ⇒
    TAKE sz (DROP addr1 mem1 ++ REPLICATE sz 0w) =
    TAKE sz (DROP addr2 mem2 ++ REPLICATE sz 0w)
Proof
  rw[cross_mem_region_equiv_def] >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP,
                         LENGTH_REPLICATE] >>
  rpt strip_tac >> simp[take_drop_replicate_el]
QED

(* MLOAD: reading 32 bytes from cross-equivalent regions gives same word. *)
Theorem mload_cross_equiv:
  ∀s1 s2 addr1 addr2.
    cross_mem_region_equiv s1.vs_memory addr1 s2.vs_memory addr2 32 ⇒
    mload addr1 s1 = mload addr2 s2
Proof
  rw[mload_def] >> rpt strip_tac >>
  imp_res_tac cross_equiv_take_drop >> fs[]
QED

(* SHA3: hashing cross-equivalent regions gives same hash. *)
Theorem sha3_cross_equiv:
  ∀mem1 addr1 mem2 addr2 sz.
    cross_mem_region_equiv mem1 addr1 mem2 addr2 sz ⇒
    let data1 = TAKE sz (DROP addr1 mem1 ++ REPLICATE sz 0w) in
    let data2 = TAKE sz (DROP addr2 mem2 ++ REPLICATE sz 0w) in
    data1 = data2
Proof
  rpt strip_tac >> imp_res_tac cross_equiv_take_drop >> fs[]
QED

(* =========================================================================
   4. Copy Forwarding Simulation Relation

   Captures the state of the two executions between the NOP'd mcopy
   and the last rewritten use. The key property: states agree on
   everything except memory at the dst alloca (which was never written
   in the transformed execution).

   In the ORIGINAL execution, instructions use dst-alias operands
   to access dst's memory (which has copied data).
   In the TRANSFORMED execution, those operands were rewritten to
   src_root, so instructions access src's memory (which has original
   data from the invoke).

   cross_mem_region_equiv connects the two: dst-in-original has the
   same content as src-in-transformed.
   ========================================================================= *)

Definition copy_fwd_rel_def:
  copy_fwd_rel (dst_addr : num) (src_addr : num) (alloca_sz : num) s1 s2 ⇔
    (* Observable state agrees *)
    observable_equiv s1 s2 ∧
    (* All variables agree *)
    (∀v. lookup_var v s1 = lookup_var v s2) ∧
    (* The dst region in s1 and the src region in s2 have same content.
       s1 = original (mcopy wrote to dst), s2 = transformed (src unchanged). *)
    cross_mem_region_equiv
      s1.vs_memory dst_addr s2.vs_memory src_addr alloca_sz ∧
    (* The src region is the same in both (not clobbered) *)
    cross_mem_region_equiv
      s1.vs_memory src_addr s2.vs_memory src_addr alloca_sz ∧
    (* Control and remaining internal state agrees *)
    s1.vs_call_ctx = s2.vs_call_ctx ∧
    s1.vs_tx_ctx = s2.vs_tx_ctx ∧
    s1.vs_block_ctx = s2.vs_block_ctx ∧
    s1.vs_data_section = s2.vs_data_section ∧
    s1.vs_labels = s2.vs_labels ∧
    s1.vs_code = s2.vs_code ∧
    s1.vs_params = s2.vs_params ∧
    s1.vs_prev_hashes = s2.vs_prev_hashes ∧
    s1.vs_allocas = s2.vs_allocas ∧
    s1.vs_alloca_next = s2.vs_alloca_next ∧
    s1.vs_current_bb = s2.vs_current_bb ∧
    s1.vs_inst_idx = s2.vs_inst_idx ∧
    s1.vs_prev_bb = s2.vs_prev_bb
End

(* copy_fwd_rel implies observable_equiv *)
Theorem copy_fwd_rel_observable_equiv:
  ∀dst src sz s1 s2.
    copy_fwd_rel dst src sz s1 s2 ⇒
    observable_equiv s1 s2
Proof
  rw[copy_fwd_rel_def]
QED

(* =========================================================================
   5. Per-Instruction Equivalence Under Operand Rewrite

   The core theorem: if instruction i_orig uses variable dst_var at a
   memory-address position (iao_ofst), and i_xfrm is the same instruction
   with dst_var replaced by src_root at that position, then stepping
   i_orig in s1 and i_xfrm in s2 (under copy_fwd_rel) produces
   equivalent results.

   This is the theorem that the IRCF proof uses for each rewritten use.
   ========================================================================= *)

(* For a read instruction (MLOAD, SHA3): the output value is the same. *)
Theorem copy_fwd_read_equiv:
  ∀i_orig i_xfrm s1 s2
   dst_addr src_addr alloca_sz dst_var src_var out.
    copy_fwd_rel dst_addr src_addr alloca_sz s1 s2 ∧
    (* i_orig reads from dst_var, i_xfrm reads from src_var *)
    i_orig.inst_opcode = i_xfrm.inst_opcode ∧
    i_orig.inst_outputs = i_xfrm.inst_outputs ∧
    (* The only operand difference: dst_var → src_var at iao_ofst *)
    (∃ops. mem_read_ops i_orig = SOME ops ∧ ops.iao_ofst = Var dst_var) ∧
    (∃ops. mem_read_ops i_xfrm = SOME ops ∧ ops.iao_ofst = Var src_var) ∧
    (* Non-offset operands are identical *)
    (∀pos. pos < LENGTH i_orig.inst_operands ∧
           EL pos i_orig.inst_operands ≠ Var dst_var ⇒
           EL pos i_orig.inst_operands = EL pos i_xfrm.inst_operands) ∧
    (* dst_var and src_var point to the right addresses *)
    lookup_var dst_var s1 = SOME (n2w dst_addr) ∧
    lookup_var src_var s2 = SOME (n2w src_addr) ∧
    (* Read size within alloca bounds *)
    (∀sz_op max_sz. mem_read_ops i_orig = SOME <| iao_ofst := Var dst_var;
               iao_size := SOME sz_op; iao_max_size := max_sz |> ⇒
             ∀sz_val. eval_operand sz_op s1 = SOME sz_val ⇒
                      w2n sz_val ≤ alloca_sz) ∧
    alloca_sz ≥ 32 ⇒
    ∀s1' s2'.
      step_inst_base i_orig s1 = OK s1' ∧
      step_inst_base i_xfrm s2 = OK s2' ⇒
      (∀out. MEM out i_orig.inst_outputs ⇒
             lookup_var out s1' = lookup_var out s2')
Proof
  cheat
QED

(* For a write instruction (MSTORE, MCOPY dst): observable state is
   preserved. Memory differs but only at the respective alloca regions. *)
Theorem copy_fwd_write_equiv:
  ∀i_orig i_xfrm s1 s2
   dst_addr src_addr alloca_sz dst_var src_var.
    copy_fwd_rel dst_addr src_addr alloca_sz s1 s2 ∧
    i_orig.inst_opcode = i_xfrm.inst_opcode ∧
    (∃ops. mem_write_ops i_orig = SOME ops ∧ ops.iao_ofst = Var dst_var) ∧
    (∃ops. mem_write_ops i_xfrm = SOME ops ∧ ops.iao_ofst = Var src_var) ∧
    (∀pos. pos < LENGTH i_orig.inst_operands ∧
           EL pos i_orig.inst_operands ≠ Var dst_var ⇒
           EL pos i_orig.inst_operands = EL pos i_xfrm.inst_operands) ∧
    lookup_var dst_var s1 = SOME (n2w dst_addr) ∧
    lookup_var src_var s2 = SOME (n2w src_addr) ⇒
    ∀s1' s2'.
      step_inst_base i_orig s1 = OK s1' ∧
      step_inst_base i_xfrm s2 = OK s2' ⇒
      observable_equiv s1' s2' ∧
      (∀v. lookup_var v s1' = lookup_var v s2') ∧
      (* Invariant preserved: cross-equiv still holds for src region,
         and dst/src cross-equiv updated for the new memory contents *)
      cross_mem_region_equiv
        s1'.vs_memory src_addr s2'.vs_memory src_addr alloca_sz
Proof
  cheat
QED

(* For terminators (RETURN, REVERT): produces same observable result. *)
Theorem copy_fwd_terminator_equiv:
  ∀i_orig i_xfrm s1 s2
   dst_addr src_addr alloca_sz dst_var src_var.
    copy_fwd_rel dst_addr src_addr alloca_sz s1 s2 ∧
    i_orig.inst_opcode = i_xfrm.inst_opcode ∧
    i_orig.inst_opcode ∈ {RETURN; REVERT} ∧
    (∃ops. mem_read_ops i_orig = SOME ops ∧ ops.iao_ofst = Var dst_var) ∧
    (∃ops. mem_read_ops i_xfrm = SOME ops ∧ ops.iao_ofst = Var src_var) ∧
    (∀pos. pos < LENGTH i_orig.inst_operands ∧
           EL pos i_orig.inst_operands ≠ Var dst_var ⇒
           EL pos i_orig.inst_operands = EL pos i_xfrm.inst_operands) ∧
    lookup_var dst_var s1 = SOME (n2w dst_addr) ∧
    lookup_var src_var s2 = SOME (n2w src_addr) ∧
    (∀sz_val. eval_operand (EL 1 i_orig.inst_operands) s1 = SOME sz_val ⇒
              w2n sz_val ≤ alloca_sz) ⇒
    lift_result observable_equiv observable_equiv observable_equiv
      (step_inst_base i_orig s1)
      (step_inst_base i_xfrm s2)
Proof
  cheat
QED

(* =========================================================================
   6. Invariant Preservation

   Instructions between the NOP'd copy and the rewritten uses that do
   NOT touch the dst or src variables maintain the copy_fwd_rel.
   The clobber analysis in the pass ensures no such instruction writes
   to the src region.
   ========================================================================= *)

(* An instruction that is IDENTICAL in both executions and doesn't
   clobber the src or dst regions preserves copy_fwd_rel. *)
Theorem copy_fwd_rel_preserved_identical_inst:
  ∀inst s1 s2 s1' s2' dst_addr src_addr alloca_sz.
    copy_fwd_rel dst_addr src_addr alloca_sz s1 s2 ∧
    step_inst_base inst s1 = OK s1' ∧
    step_inst_base inst s2 = OK s2' ∧
    (* Instruction doesn't write to src or dst regions *)
    (∀ofst write_sz max_sz.
      mem_write_ops inst = SOME <| iao_ofst := ofst;
        iao_size := SOME write_sz; iao_max_size := max_sz |> ⇒
      ∀a wsz.
        eval_operand ofst s1 = SOME a ∧
        eval_operand write_sz s1 = SOME wsz ⇒
        (w2n a + w2n wsz ≤ dst_addr ∨ dst_addr + alloca_sz ≤ w2n a) ∧
        (w2n a + w2n wsz ≤ src_addr ∨ src_addr + alloca_sz ≤ w2n a)) ⇒
    copy_fwd_rel dst_addr src_addr alloca_sz s1' s2'
Proof
  cheat
QED

(* =========================================================================
   7. ASSIGN Transparency

   ASSIGN forwards values unchanged. pointer_confined + ASSIGN means
   the output is pointer-derived (if input was), so it stays in the
   pointer-derived set and remains confined.
   ========================================================================= *)

Theorem assign_transparent:
  ∀inst s s' out v.
    inst.inst_opcode = ASSIGN ∧
    inst.inst_operands = [Var v] ∧
    inst.inst_outputs = [out] ∧
    step_inst_base inst s = OK s' ⇒
    lookup_var out s' = lookup_var v s
Proof
  rpt strip_tac >>
  gvs[step_inst_base_def, eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> gvs[update_var_def, FLOOKUP_UPDATE]
QED

Theorem phi_transparent:
  !inst s out prev v.
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var v) ==>
    !val. eval_one_phi s inst = SOME (out,val) ==>
      val = THE (lookup_var v s) /\
      lookup_var out (update_var out val s) = lookup_var v s
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def, AllCaseEqs()] >>
  gvs[eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> gvs[update_var_def, FLOOKUP_UPDATE]
QED
