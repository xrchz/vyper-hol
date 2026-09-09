(*
 * Counterexamples for mem_ssa Props theorem statements.
 *
 * Documents why certain preconditions are needed and why one theorem
 * (mem_ssa_phi_at_frontier) was dropped. Three issues are covered:
 *
 * 1. mem_ssa_reaching_acyclic: FALSE without cfg = cfg_analyze fn /\
 *    dom = dom_analyze cfg fn. Cyclic idom creates reaching cycles.
 *    MECHANICAL proof below. Corrected: memSSAPropsTheory.mem_ssa_reaching_acyclic
 *
 * 2. mem_ssa_clobber_sound: FALSE in two ways:
 *    (a) MnPhi access nodes trivially satisfy completely_contains via
 *        ml_empty. Fixed by adding !blk. THE(...) <> MnPhi blk.
 *    (b) Same-block later defs are not on the reaching chain but do
 *        dominate the access. Fixed by using strict_dominates instead
 *        of dominates. INFORMAL argument + supporting lemmas below.
 *    Corrected: memSSAPropsTheory.mem_ssa_clobber_sound
 *
 * 3. mem_ssa_phi_at_frontier: FALSE because Phase 4 removes redundant
 *    phis, breaking the frontier witness. No consumer. DROPPED from Props.
 *    INFORMAL argument below.
 *)
Theory memSSACex
Ancestors
  memSSAProofs basePtrDefs memLocDefs dominatorDefs memSSADefs cfgDefs venomInst venomWf venomState
Libs
  alistTheory finite_mapTheory listTheory pred_setTheory

(* =====================================================================
   1. mem_ssa_reaching_acyclic — mechanical counterexample
   =====================================================================
   With cyclic da_idom (idom(A)=B, idom(B)=A) and two blocks each having
   one MSTORE, Phase 3 creates ms_reaching[1]=2, ms_reaching[2]=1.
   This gives reaching_chain ms 2 1 1 — a cycle.

   The original statement quantified over arbitrary cfg/dom. The corrected
   statement requires cfg = cfg_analyze fn /\ dom = dom_analyze cfg fn,
   which guarantees acyclic idom.
   ===================================================================== *)

Definition cex_fn_def:
  cex_fn = mk_raw_function "test"
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 1; inst_opcode := MSTORE;
            inst_operands := [Var "dst"; Var "val"]; inst_outputs := [] |>;
         <| inst_id := 2; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 3; inst_opcode := MSTORE;
            inst_operands := [Var "dst2"; Var "val2"]; inst_outputs := [] |>;
         <| inst_id := 4; inst_opcode := JMP;
            inst_operands := [Label "A"]; inst_outputs := [] |>] |>]
End

Definition cex_cfg_def:
  cex_cfg = <| cfg_succs := FEMPTY; cfg_preds := FEMPTY;
               cfg_reachable := FEMPTY; cfg_dfs_post := [];
               cfg_dfs_pre := ["A"; "B"] |>
End

(* Cyclic idom: idom(A) = B, idom(B) = A *)
Definition cex_dom_def:
  cex_dom = <| da_dominators := FEMPTY;
               da_idom := FEMPTY |+ ("A", "B") |+ ("B", "A");
               da_dominated := FEMPTY; da_frontier := FEMPTY |>
End

Theorem insert_phis_empty_frontier[local]:
  !wl ms cfg dom ef fuel.
    dom.da_frontier = FEMPTY ==>
    mem_ssa_insert_phis ms cfg dom ef fuel wl = ms
Proof
  Induct_on `fuel` >> simp[mem_ssa_insert_phis_def] >>
  Induct_on `wl` >> simp[mem_ssa_insert_phis_def, LET_THM] >>
  rpt strip_tac >>
  `frontier_of dom h = []`
    by simp[frontier_of_def, fmap_lookup_list_def, FLOOKUP_DEF] >>
  simp[mem_ssa_process_frontiers_def]
QED

val _ = computeLib.add_funs
  [prove(``SET_TO_LIST (EMPTY:string set) = ([]:(string list))``,
         simp[SET_TO_LIST_THM]),
   prove(``SET_TO_LIST (EMPTY:num set) = ([]:(num list))``,
         simp[SET_TO_LIST_THM]),
   prove(``SET_TO_LIST (EMPTY:(string # num list) set) = []:((string # num list) list)``,
         simp[SET_TO_LIST_THM])];

val cex_unfold = [mem_ssa_build_def, LET_THM, cex_cfg_def, cex_dom_def,
                  insert_phis_empty_frontier, fmap_to_alist_FEMPTY];

Theorem cex_wf_function:
  wf_function cex_fn
Proof
  simp[wf_function_def, cex_fn_def, mk_raw_function_def,
       fn_has_entry_def, fn_inst_ids_distinct_def, fn_labels_def,
       bb_well_formed_def, fn_succs_closed_def, bb_succs_def,
       get_successors_def, get_label_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (Cases_on `i` >> fs[is_terminator_def] >> Cases_on `n` >> fs[is_terminator_def]) >>
  TRY (Cases_on `j` >> fs[] >> Cases_on `n` >> fs[]) >>
  fs[is_terminator_def, get_label_def]
QED

Theorem cex_reaching_cycle:
  FLOOKUP (mem_ssa_build cex_cfg cex_dom FEMPTY cex_fn AddrSp_Memory).ms_reaching
    1 = SOME 2 /\
  FLOOKUP (mem_ssa_build cex_cfg cex_dom FEMPTY cex_fn AddrSp_Memory).ms_reaching
    2 = SOME 1
Proof
  simp cex_unfold >> EVAL_TAC
QED

Theorem cex_node_1_in_fdom:
  1 IN FDOM (mem_ssa_build cex_cfg cex_dom FEMPTY cex_fn AddrSp_Memory).ms_nodes
Proof
  simp cex_unfold >> EVAL_TAC
QED

Theorem mem_ssa_reaching_acyclic_FALSE:
  ~(!(cfg:cfg_analysis) (dom:dom_analysis) bp (fn:ir_function) addr_sp ms aid.
      wf_function fn /\
      ms = mem_ssa_build cfg dom bp fn addr_sp /\
      aid IN FDOM ms.ms_nodes /\ aid <> 0 ==>
      ~(?n. n > 0 /\ reaching_chain ms n aid aid))
Proof
  simp[] >>
  qexistsl_tac [`cex_cfg`, `cex_dom`, `FEMPTY`, `cex_fn`, `AddrSp_Memory`] >>
  simp[] >>
  qexists_tac `1` >>
  simp[cex_wf_function, cex_node_1_in_fdom] >>
  qexists_tac `2` >> simp[] >>
  simp[reaching_chain_compute, cex_reaching_cycle]
QED

(* =====================================================================
   2a. mem_ssa_clobber_sound — MnPhi issue (supporting lemmas)
   =====================================================================
   MnPhi nodes have mn_loc = ml_empty (size 0), and completely_contains
   trivially holds for ml_empty. Phase 3 skips phis, so get_clobbered
   returns SOME 0 immediately. Any MnDef with a non-empty location
   would then violate the conclusion.
   Corrected by requiring !blk. THE(...) <> MnPhi blk.
   ===================================================================== *)

Theorem mn_loc_phi_is_empty:
  !blk. mn_loc (MnPhi blk) = ml_empty
Proof
  simp[mn_loc_def]
QED

Theorem completely_contains_ml_empty:
  !loc. completely_contains loc ml_empty
Proof
  simp[completely_contains_def, ml_empty_def]
QED

Theorem get_clobbered_phi_returns_0:
  !ms fuel phi_id blk.
    FLOOKUP ms.ms_nodes phi_id = SOME (MnPhi blk) /\
    FLOOKUP ms.ms_reaching phi_id = NONE /\
    phi_id <> 0 ==>
    mem_ssa_get_clobbered ms fuel phi_id = SOME 0
Proof
  rpt strip_tac >>
  simp[mem_ssa_get_clobbered_def, mn_loc_def]
QED

(* =====================================================================
   2b. mem_ssa_clobber_sound — same-block later def (informal)
   =====================================================================
   Even with the MnPhi fix, the original statement (using dominates
   rather than strict_dominates) is FALSE.

   walk_clobber follows ms_reaching backward. Phase 3's find_prev_def
   only finds defs BEFORE the access in instruction order. A store
   AFTER the access in the same block creates an MnDef that is never
   on the reaching chain, yet dominates the access (via dom_self).

   Scenario (single entry block B):
     Instructions: [inst1 (MLOAD, loc1), inst2 (MSTORE, loc2), STOP]
     loc1 = (offset=100, size=32), loc2 = (offset=50, size=200)
     completely_contains loc2 loc1 = T

   After mem_ssa_build:
     - find_prev_def for inst1: no def before it → reaching = 0
     - get_clobbered walks from 0 → returns SOME 0
     - But MnDef(inst2) has def_blk = B, dominates B B, and
       completely_contains loc2 loc1 = T → contradiction

   Corrected by using strict_dominates (def_blk strictly dominates
   access block), which excludes same-block defs.

   Full mechanical proof would require evaluating cfg_analyze/dom_analyze,
   which don't terminate under EVAL. Supporting lemmas below demonstrate
   the key steps.
   ===================================================================== *)

Theorem find_prev_def_first_inst:
  !ms inst insts.
    mem_ssa_find_prev_def ms (inst :: insts) inst.inst_id = NONE
Proof
  simp[mem_ssa_find_prev_def_def]
QED

Theorem walk_clobber_at_zero:
  !ms fuel visited qloc.
    mem_ssa_walk_clobber ms (SUC fuel) visited 0 qloc = (NONE, visited)
Proof
  simp[mem_ssa_walk_clobber_def]
QED

Theorem get_clobbered_reaching_zero:
  !ms fuel access_id node.
    FLOOKUP ms.ms_nodes access_id = SOME node /\
    FLOOKUP ms.ms_reaching access_id = SOME 0 /\
    access_id <> 0 /\
    fuel > 0 ==>
    mem_ssa_get_clobbered ms fuel access_id = SOME 0
Proof
  rpt strip_tac >>
  simp[mem_ssa_get_clobbered_def] >>
  Cases_on `fuel` >> fs[] >>
  simp[mem_ssa_walk_clobber_def]
QED

Theorem completely_contains_example:
  completely_contains
    <| ml_offset := SOME 50; ml_size := SOME 200;
       ml_alloca := NONE; ml_volatile := F |>
    <| ml_offset := SOME 100; ml_size := SOME 32;
       ml_alloca := NONE; ml_volatile := F |>
Proof
  simp[completely_contains_def]
QED

(* =====================================================================
   3. mem_ssa_phi_at_frontier — informal counterexample (DROPPED)
   =====================================================================
   The statement says: if a phi survives at lbl after Phase 4, then
   some src_lbl has (block_defs ≠ [] OR src_lbl IN FDOM ms_block_phis)
   AND lbl IN frontier(src_lbl).

   FALSE because Phase 4 removes redundant phis:

   CFG: Entry → A, Entry → B, A → C, B → C
   - A, B each have MSTORE → MnDefs, frontier({A,B}) = {C}
   - Phase 2: phi placed at C
   - If both operands reach the same def (Entry's), phi is redundant
   - Phase 4 removes C's phi

   With 3 levels (X → Y → Z):
   - X has def, frontier(X) = {Y}
   - Phase 2 places phi at Y, frontier(Y) = {Z}, places phi at Z
   - Y's phi is redundant → removed by Phase 4
   - Z's phi survives, but the only src_lbl with Z in its frontier is Y,
     which no longer has phi or defs in the post-Phase4 state

   No consumer for this theorem. Dropped from Props.
   ===================================================================== *)


