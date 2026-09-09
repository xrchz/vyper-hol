(*
 * DFS decomposition of generate_fn_plan_aux
 *
 * Structural properties of the DFS traversal in generate_fn_plan_aux:
 *   - visited set grows monotonically
 *   - each visited block has generate_block_plan called on it
 *   - output ops contain per-block contributions at known offsets
 *
 * These connect generate_fn_plan (flat stack_op list) to
 * gen_fn_sim_fuel (which needs per-block ps_fn and bops_fn).
 *
 * STATUS: Currently not imported by the active codegen correctness chain.
 * Keep as plausible future infrastructure for closing gen_fn_simulation in
 * venomToAsmPropsScript.sml, not dead code.
 *)


Theory fnPlanDecomp
Ancestors
  stackPlanGen stackPlanTypes stackModel planExec codegenRel asmSem stackOpSim allocMono list rich_list arithmetic pred_set finite_map
Libs
  BasicProvers

(* ===== Visited set monotonicity =====
   generate_fn_plan_aux only adds to the visited set, never removes.
   visited is now a string list; monotonicity is set visited ⊆ set visited'. *)

(* Visited monotonicity: MEM lbl visited ==> MEM lbl visited', derived
   directly from stackPlanGenTheory's clean subset boundary. *)
Theorem fn_plan_aux_visited_mem:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') ==>
    !lbl. MEM lbl visited ==> MEM lbl visited') /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') ==>
    !lbl. MEM lbl visited ==> MEM lbl visited')
Proof
  conj_tac
  >- (rpt strip_tac >>
      drule generate_fn_plan_aux_visited_mono >>
      simp[SUBSET_DEF])
  >> rpt strip_tac >>
     drule generate_succs_plan_visited_mono >>
     simp[SUBSET_DEF]
QED

(* ===== Per-block plan extraction =====

   When generate_fn_plan_aux visits a block lbl (i.e., lbl ends up
   in visited' but wasn't in visited), it called generate_block_plan
   on that block. The block_ops appear contiguously within the output.

   We state this as: the output ops are a concatenation where each
   newly-visited block contributes its block_ops as a sub-list.
   For asm_block_at decomposition, we need the offsets. *)

(* Helper: ops contain sub at offset *)
Definition ops_contain_at_def:
  ops_contain_at off ops sub <=>
    off + LENGTH sub <= LENGTH ops /\
    !i. i < LENGTH sub ==> EL (off + i) ops = EL i sub
End

(* ops_contain_at reflexivity: any list contains itself at offset 0 *)
Theorem ops_contain_at_refl:
  !ops. ops_contain_at 0 ops ops
Proof
  simp[ops_contain_at_def]
QED

(* ops_contain_at composition: if sub is in inner at off1,
   and inner is a suffix of outer (at offset prefix_len),
   then sub is in outer at prefix_len + off1. *)
Theorem ops_contain_at_prepend:
  !prefix inner sub off.
    ops_contain_at off inner sub ==>
    ops_contain_at (LENGTH prefix + off) (prefix ++ inner) sub
Proof
  rpt gen_tac >> rpt disch_tac >>
  gvs[ops_contain_at_def] >>
  rpt strip_tac >>
  `LENGTH prefix + off + i = LENGTH prefix + (off + i)` by decide_tac >>
  simp[EL_APPEND2]
QED
(* Also: contained in inner -> contained in inner ++ suffix *)
Theorem ops_contain_at_append:
  !inner suffix sub off.
    ops_contain_at off inner sub ==>
    ops_contain_at off (inner ++ suffix) sub
Proof
  rpt gen_tac >> rpt disch_tac >>
  gvs[ops_contain_at_def] >>
  rpt strip_tac >>
  `off + i < LENGTH inner` by decide_tac >>
  simp[EL_APPEND1]
QED

(* Combined: sub contained in inner at off → sub contained in
   prefix ++ inner ++ suffix at LENGTH prefix + off *)
Theorem ops_contain_at_embed:
  !prefix inner suffix sub off.
    ops_contain_at off inner sub ==>
    ops_contain_at (LENGTH prefix + off) (prefix ++ inner ++ suffix) sub
Proof
  rpt strip_tac >>
  drule ops_contain_at_append >>
  disch_then (qspec_then `suffix` mp_tac) >>
  strip_tac >>
  drule ops_contain_at_prepend >>
  disch_then (qspec_then `prefix` mp_tac) >>
  simp[]
QED

(* Lifting: sub in middle component of a 3-way concat, through execute_plan initial_fmp *)
Theorem ops_contain_at_in_concat3:
  !prefix inner suffix sub off.
    ops_contain_at off (execute_plan initial_fmp inner) (execute_plan initial_fmp sub) ==>
    ops_contain_at (LENGTH (execute_plan initial_fmp prefix) + off)
      (execute_plan initial_fmp (prefix ++ inner ++ suffix))
      (execute_plan initial_fmp sub)
Proof
  rpt strip_tac >>
  REWRITE_TAC[execute_plan_append, GSYM APPEND_ASSOC] >>
  irule ops_contain_at_prepend >>
  irule ops_contain_at_append >> simp[]
QED

(* Lifting: sub in left component of a 2-way concat *)
Theorem ops_contain_at_in_concat2_left:
  !left right sub off.
    ops_contain_at off (execute_plan initial_fmp left) (execute_plan initial_fmp sub) ==>
    ops_contain_at off
      (execute_plan initial_fmp (left ++ right))
      (execute_plan initial_fmp sub)
Proof
  rpt strip_tac >>
  REWRITE_TAC[execute_plan_append] >>
  irule ops_contain_at_append >> simp[]
QED

(* Lifting: sub in right component of a 2-way concat *)
Theorem ops_contain_at_in_concat2_right:
  !left right sub off.
    ops_contain_at off (execute_plan initial_fmp right) (execute_plan initial_fmp sub) ==>
    ops_contain_at (LENGTH (execute_plan initial_fmp left) + off)
      (execute_plan initial_fmp (left ++ right))
      (execute_plan initial_fmp sub)
Proof
  rpt strip_tac >>
  REWRITE_TAC[execute_plan_append] >>
  irule ops_contain_at_prepend >> simp[]
QED

(* Main per-block extraction (mutual induction).
   For each newly visited block, its block_ops appear somewhere
   in the output, and generate_block_plan was called on it. *)
Theorem fn_plan_aux_per_block:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') ==>
    !lbl bb.
      lookup_block lbl fn.fn_blocks = SOME bb /\
      MEM lbl visited' /\ ~MEM lbl visited ==>
      ?ps_lbl block_ops ps_after off.
        generate_block_plan liveness dfg cfg fn bb ps_lbl =
          SOME (block_ops, ps_after) /\
        ops_contain_at off (execute_plan initial_fmp ops)
          (execute_plan initial_fmp block_ops)) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') ==>
    !lbl bb.
      lookup_block lbl fn.fn_blocks = SOME bb /\
      MEM lbl visited' /\ ~MEM lbl visited ==>
      ?ps_lbl block_ops ps_after off.
        generate_block_plan liveness dfg cfg fn bb ps_lbl =
          SOME (block_ops, ps_after) /\
        ops_contain_at off (execute_plan initial_fmp ops)
          (execute_plan initial_fmp block_ops))
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  (* base: worklist = [] *)
  >- (rpt gen_tac >> rpt strip_tac >>
      gvs[Once generate_fn_plan_aux_def])
  (* step: worklist = lbl :: rest *)
  >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_ :: _) _ _ = _` mp_tac >>
    simp[Once generate_fn_plan_aux_def] >>
    IF_CASES_TAC >> gvs[]
    (* MEM lbl visited: IH matches directly *)
    >- metis_tac[]
    (* ~MEM lbl visited *)
    >> Cases_on `lookup_block lbl fn.fn_blocks` >> gvs[]
    (* NONE: rest with lbl :: visited *)
    >- (
      strip_tac >> rpt gen_tac >> strip_tac >>
      `lbl' <> lbl` by (strip_tac >> gvs[]) >>
      `~MEM lbl' (lbl :: visited)` by gvs[] >>
      metis_tac[]
    )
    (* SOME bb_h *)
    >> rename1 `lookup_block lbl _ = SOME bb_h` >>
    Cases_on `generate_block_plan liveness dfg cfg fn bb_h ps` >> simp[] >>
    rename1 `_ = SOME bp` >> Cases_on `bp` >> simp[] >>
    rename1 `_ = SOME (block_ops_h, ps1)` >>
    Cases_on `generate_succs_plan liveness dfg cfg fn ps1.ps_stack
               ps1.ps_spilled (cfg_succs_of cfg lbl)
               (lbl :: visited) ps1` >> simp[] >>
    rename1 `_ = SOME sp` >> Cases_on `sp` >> simp[] >>
    rename1 `_ = SOME (succ_ops, vp1)` >> Cases_on `vp1` >> simp[] >>
    rename1 `_ = SOME (succ_ops, vis2, ps2)` >>
    Cases_on `generate_fn_plan_aux liveness dfg cfg fn worklist vis2 ps2`
    >> simp[] >>
    rename1 `_ = SOME rp` >> Cases_on `rp` >> simp[] >>
    rename1 `_ = SOME (rest_ops, vp2)` >> Cases_on `vp2` >>
    rename1 `_ = SOME (rest_ops, vis_rest, ps_rest)` >> simp[] >>
    strip_tac >> gvs[] >>
    rpt gen_tac >> strip_tac >>
    Cases_on `lbl' = lbl`
    >- (
      (* lbl' = lbl: this block at offset 0 *)
      gvs[] >>
      qexistsl_tac [`ps`, `block_ops_h`, `ps1`, `0`] >> simp[] >>
      REWRITE_TAC[execute_plan_append] >>
      irule ops_contain_at_append >>
      irule ops_contain_at_append >>
      simp[ops_contain_at_refl]
    )
    >> `~MEM lbl' (lbl :: visited)` by gvs[] >>
    Cases_on `MEM lbl' vis2`
    >- (
      (* In succs: establish IH result via subgoal *)
      `?ps_lbl block_ops ps_after off.
         generate_block_plan liveness dfg cfg fn bb ps_lbl =
           SOME (block_ops, ps_after) /\
         ops_contain_at off (execute_plan initial_fmp succ_ops)
           (execute_plan initial_fmp block_ops)` by metis_tac[] >>
      qexistsl_tac [`ps_lbl`, `block_ops`, `ps_after`,
                     `LENGTH (execute_plan initial_fmp block_ops_h) + off`] >>
      simp[] >>
      drule ops_contain_at_in_concat3 >>
      disch_then (qspecl_then [`block_ops_h`, `rest_ops`] mp_tac) >>
      simp[]
    )
    >- (
      (* In rest: lbl' was visited by the rest fn_plan_aux call *)
      `MEM lbl' vis_rest /\ ~MEM lbl' vis2` by
        (gvs[] >>
         imp_res_tac (cj 1 fn_plan_aux_visited_mem) >> metis_tac[]) >>
      `?ps_lbl block_ops ps_after off.
         generate_block_plan liveness dfg cfg fn bb ps_lbl =
           SOME (block_ops, ps_after) /\
         ops_contain_at off (execute_plan initial_fmp rest_ops)
           (execute_plan initial_fmp block_ops)` by metis_tac[] >>
      qexistsl_tac [`ps_lbl`, `block_ops`, `ps_after`,
                     `LENGTH (execute_plan initial_fmp (block_ops_h ++ succ_ops)) + off`] >>
      simp[] >>
      drule ops_contain_at_in_concat2_right >>
      disch_then (qspec_then `block_ops_h ++ succ_ops` mp_tac) >>
      REWRITE_TAC[execute_plan_append, GSYM APPEND_ASSOC] >>
      simp[]
    )
  )
  (* base: succs = [] *)
  >- (rpt gen_tac >> rpt strip_tac >>
      gvs[Once generate_fn_plan_aux_def])
  (* step: succs = succ :: rest_succs *)
  >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `generate_succs_plan _ _ _ _ _ _ (_ :: _) _ _ = _` mp_tac >>
    simp[Once generate_fn_plan_aux_def] >>
    every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
    rpt gen_tac >> strip_tac >>
    rename1 `lookup_block qlbl _ = SOME qbb` >>
    rename1 `generate_fn_plan_aux _ _ _ _ [_] visited _ =
               SOME (s_ops, vis_s, ps_s)` >>
    rename1 `generate_succs_plan _ _ _ _ _ _ _ vis_s _ =
               SOME (rest_ops, vis_r, ps_r)` >>
    Cases_on `MEM qlbl vis_s`
    >- (
      (* qlbl found by fn_plan_aux on [succ] *)
      `?ps_lbl block_ops ps_after off.
         generate_block_plan liveness dfg cfg fn qbb ps_lbl =
           SOME (block_ops, ps_after) /\
         ops_contain_at off (execute_plan initial_fmp s_ops)
           (execute_plan initial_fmp block_ops)` by metis_tac[] >>
      qexistsl_tac [`ps_lbl`, `block_ops`, `ps_after`, `off`] >> simp[] >>
      drule ops_contain_at_in_concat2_left >>
      disch_then (qspec_then `rest_ops` mp_tac) >> simp[]
    )
    >- (
      (* qlbl found by succs_plan on rest *)
      `MEM qlbl vis_r /\ ~MEM qlbl vis_s` by gvs[] >>
      `?ps_lbl block_ops ps_after off.
         generate_block_plan liveness dfg cfg fn qbb ps_lbl =
           SOME (block_ops, ps_after) /\
         ops_contain_at off (execute_plan initial_fmp rest_ops)
           (execute_plan initial_fmp block_ops)` by metis_tac[] >>
      qexistsl_tac [`ps_lbl`, `block_ops`, `ps_after`,
                     `LENGTH (execute_plan initial_fmp s_ops) + off`] >> simp[] >>
      drule ops_contain_at_in_concat2_right >>
      disch_then (qspec_then `s_ops` mp_tac) >> simp[]
    )
  )
QED

(* ===== Entry state extraction =====
   When generate_fn_plan_aux visits a block, the entry plan state
   has the same sa_spill_base and monotonically larger sa_next_offset. *)

Theorem fn_plan_aux_entry_state:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') ==>
    !lbl bb.
      lookup_block lbl fn.fn_blocks = SOME bb /\
      MEM lbl visited' /\ ~MEM lbl visited ==>
      ?ps_lbl block_ops ps_after off.
        generate_block_plan liveness dfg cfg fn bb ps_lbl =
          SOME (block_ops, ps_after) /\
        ops_contain_at off (execute_plan initial_fmp ops)
          (execute_plan initial_fmp block_ops) /\
        ps_lbl.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
        ps.ps_alloc.sa_next_offset <= ps_lbl.ps_alloc.sa_next_offset) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') ==>
    !lbl bb.
      lookup_block lbl fn.fn_blocks = SOME bb /\
      MEM lbl visited' /\ ~MEM lbl visited ==>
      ?ps_lbl block_ops ps_after off.
        generate_block_plan liveness dfg cfg fn bb ps_lbl =
          SOME (block_ops, ps_after) /\
        ops_contain_at off (execute_plan initial_fmp ops)
          (execute_plan initial_fmp block_ops) /\
        ps_lbl.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
        ps.ps_alloc.sa_next_offset <= ps_lbl.ps_alloc.sa_next_offset)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  (* base: worklist = [] *)
  >- (rpt gen_tac >> rpt strip_tac >>
      gvs[Once generate_fn_plan_aux_def])
  (* step: worklist = lbl :: rest *)
  >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_ :: _) _ _ = _` mp_tac >>
    simp[Once generate_fn_plan_aux_def] >>
    IF_CASES_TAC >> gvs[]
    (* MEM lbl visited: IH on rest *)
    >- metis_tac[]
    (* ~MEM lbl visited *)
    >> Cases_on `lookup_block lbl fn.fn_blocks` >> gvs[]
    (* NONE: rest with lbl :: visited *)
    >- (
      strip_tac >> rpt gen_tac >> strip_tac >>
      `lbl' <> lbl` by (strip_tac >> gvs[]) >>
      `~MEM lbl' (lbl :: visited)` by gvs[] >>
      metis_tac[]
    )
    (* SOME bb_h *)
    >> rename1 `lookup_block lbl _ = SOME bb_h` >>
    Cases_on `generate_block_plan liveness dfg cfg fn bb_h ps` >> simp[] >>
    rename1 `_ = SOME bp` >> Cases_on `bp` >> simp[] >>
    rename1 `_ = SOME (block_ops_h, ps1)` >>
    Cases_on `generate_succs_plan liveness dfg cfg fn ps1.ps_stack
               ps1.ps_spilled (cfg_succs_of cfg lbl)
               (lbl :: visited) ps1` >> simp[] >>
    rename1 `_ = SOME sp` >> Cases_on `sp` >> simp[] >>
    rename1 `_ = SOME (succ_ops, vp1)` >> Cases_on `vp1` >> simp[] >>
    rename1 `_ = SOME (succ_ops, vis2, ps2)` >>
    Cases_on `generate_fn_plan_aux liveness dfg cfg fn worklist vis2 ps2`
    >> simp[] >>
    rename1 `_ = SOME rp` >> Cases_on `rp` >> simp[] >>
    rename1 `_ = SOME (rest_ops, vp2)` >> Cases_on `vp2` >>
    rename1 `_ = SOME (rest_ops, vis_rest, ps_rest)` >> simp[] >>
    strip_tac >> gvs[] >>
    rpt gen_tac >> strip_tac >>
    Cases_on `lbl' = lbl`
    >- (
      (* lbl' = lbl: this block with entry state ps *)
      gvs[] >>
      qexistsl_tac [`ps`, `block_ops_h`, `ps1`, `0`] >> simp[] >>
      REWRITE_TAC[execute_plan_append] >>
      irule ops_contain_at_append >>
      irule ops_contain_at_append >>
      simp[ops_contain_at_refl]
    )
    >> `~MEM lbl' (lbl :: visited)` by gvs[] >>
    Cases_on `MEM lbl' vis2`
    >- (
      (* In succs: IH gives result *)
      `?ps_lbl block_ops ps_after off.
         generate_block_plan liveness dfg cfg fn bb ps_lbl =
           SOME (block_ops, ps_after) /\
         ops_contain_at off (execute_plan initial_fmp succ_ops)
           (execute_plan initial_fmp block_ops) /\
         ps_lbl.ps_alloc.sa_spill_base = ps1.ps_alloc.sa_spill_base /\
         ps1.ps_alloc.sa_next_offset <= ps_lbl.ps_alloc.sa_next_offset`
           by metis_tac[] >>
      qexistsl_tac [`ps_lbl`, `block_ops`, `ps_after`,
                     `LENGTH (execute_plan initial_fmp block_ops_h) + off`] >>
      simp[] >> rpt conj_tac
      >- (drule ops_contain_at_in_concat3 >>
          disch_then (qspecl_then [`block_ops_h`, `rest_ops`] mp_tac) >>
          simp[])
      (* Bridge alloc from ps to ps_lbl via generate_block_plan_alloc_mono *)
      >> (
        qpat_x_assum `generate_block_plan _ _ _ _ bb_h ps = _`
          (fn th => assume_tac (MATCH_MP generate_block_plan_alloc_mono th)) >>
        gvs[] >> decide_tac)
    )
    >- (
      (* In rest: IH gives result relative to ps2.
         Bridge: ps -> ps1 (block_plan) -> ps2 (succs_plan) *)
      `MEM lbl' vis_rest /\ ~MEM lbl' vis2` by
        (gvs[] >>
         imp_res_tac (cj 1 fn_plan_aux_visited_mem) >> metis_tac[]) >>
      `?ps_lbl block_ops ps_after off.
         generate_block_plan liveness dfg cfg fn bb ps_lbl =
           SOME (block_ops, ps_after) /\
         ops_contain_at off (execute_plan initial_fmp rest_ops)
           (execute_plan initial_fmp block_ops) /\
         ps_lbl.ps_alloc.sa_spill_base = ps2.ps_alloc.sa_spill_base /\
         ps2.ps_alloc.sa_next_offset <= ps_lbl.ps_alloc.sa_next_offset`
           by metis_tac[] >>
      qexistsl_tac [`ps_lbl`, `block_ops`, `ps_after`,
                     `LENGTH (execute_plan initial_fmp (block_ops_h ++ succ_ops)) + off`] >>
      simp[] >> rpt conj_tac
      >- (drule ops_contain_at_in_concat2_right >>
          disch_then (qspec_then `block_ops_h ++ succ_ops` mp_tac) >>
          REWRITE_TAC[execute_plan_append, GSYM APPEND_ASSOC] >>
          simp[])
      (* Bridge: ps → ps1 → ps2, need fn_eom = and next_offset ≤ *)
      >> (
        qpat_x_assum `generate_block_plan _ _ _ _ bb_h ps = _`
          (fn th => assume_tac (MATCH_MP generate_block_plan_alloc_mono th)) >>
        qpat_x_assum `generate_succs_plan _ _ _ _ _ _ _ _ ps1 = _`
          (fn th => assume_tac (MATCH_MP (cj 2 fn_plan_aux_alloc_mono) th)) >>
        gvs[] >> decide_tac)
    )
  )
  (* base: succs = [] *)
  >- (rpt gen_tac >> rpt strip_tac >>
      gvs[Once generate_fn_plan_aux_def])
  (* step: succs = succ :: rest_succs *)
  >- (
    rpt gen_tac >> strip_tac >>
    simp[Once generate_fn_plan_aux_def] >>
    every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
    rpt gen_tac >> strip_tac >>
    rename1 `generate_fn_plan_aux _ _ _ _ [_] visited _ =
               SOME (s_ops, vis_s, ps_s)` >>
    rename1 `generate_succs_plan _ _ _ _ _ _ _ vis_s _ =
               SOME (rest_ops, vis_r, ps_r)` >>
    Cases_on `MEM lbl vis_s`
    >- (
      (* lbl in vis_s: use IH1 (fn_plan_aux) *)
      qpat_x_assum `!lbl bb. _ /\ MEM lbl vis_s /\ _ ==> _`
        (qspecl_then [`lbl`, `bb`] mp_tac) >>
      simp[] >> disch_then (qx_choosel_then
        [`ps1`, `bops1`, `pa1`, `off1`] strip_assume_tac) >>
      qexistsl_tac [`ps1`, `bops1`, `pa1`, `off1`] >> simp[] >>
      drule ops_contain_at_in_concat2_left >>
      disch_then (qspec_then `rest_ops` mp_tac) >> simp[]
    )
    >- (
      (* lbl in vis_r \ vis_s: use IH2 (succs_plan) *)
      qpat_x_assum `!lbl bb. _ /\ MEM lbl vis_r /\ _ ==> _`
        (qspecl_then [`lbl`, `bb`] mp_tac) >>
      simp[] >> disch_then (qx_choosel_then
        [`ps2`, `bops2`, `pa2`, `off2`] strip_assume_tac) >>
      qpat_assum `generate_fn_plan_aux _ _ _ _ [_] _ _ = _`
        (fn th => assume_tac (MATCH_MP (cj 1 fn_plan_aux_alloc_mono) th)) >>
      qexistsl_tac [`ps2`, `bops2`, `pa2`,
                     `LENGTH (execute_plan initial_fmp s_ops) + off2`] >>
      gvs[] >> rpt conj_tac
      >- (drule ops_contain_at_in_concat2_right >>
          disch_then (qspec_then `s_ops` mp_tac) >> simp[])
      >> decide_tac
    )
  )
QED

(* ===== asm_block_at from ops_contain_at =====

   If the full asm program is at some PC and block_ops are
   contained within it, then asm_block_at holds for the sub-block. *)

Theorem asm_block_at_from_contain:
  !prog pc full_asm sub_asm off.
    asm_block_at prog pc full_asm /\
    ops_contain_at off full_asm sub_asm ==>
    asm_block_at prog (pc + off) sub_asm
Proof
  rpt gen_tac >> rpt disch_tac >>
  gvs[asm_block_at_def, ops_contain_at_def] >>
  rpt strip_tac >>
  rename1 `j < LENGTH sub_asm` >>
  `off + j < LENGTH full_asm` by decide_tac >>
  qpat_x_assum `!x. x < LENGTH full_asm ==> _`
    (qspec_then `off + j` mp_tac) >> simp[]
QED

(* ===== Entry label becomes visited =====

   When the DFS starts with [lbl] and empty visited list, lbl ends
   up in the final visited list. *)

Theorem fn_plan_aux_entry_visited:
  !liveness dfg cfg fn lbl ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn [lbl] [] ps =
      SOME (ops, visited', ps') ==>
    MEM lbl visited'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ [_] _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def] >>
  (* ~MEM lbl [] is automatic *)
  Cases_on `lookup_block lbl fn.fn_blocks` >> simp[]
  >- (
    (* NONE: recurse on [] with [lbl] *)
    strip_tac >>
    drule (cj 1 fn_plan_aux_visited_mem) >>
    simp[]
  )
  >> (* SOME bb: process block, succs, then rest=[] *)
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  (* lbl ∈ [lbl] ⊆ intermediate visited by succs_plan monotonicity *)
  rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ =
             SOME (_, vis2, _)` >>
  rename1 `generate_fn_plan_aux _ _ _ _ [] vis2 _ =
             SOME (_, visited', _)` >>
  `MEM lbl vis2` by
    (drule (cj 2 fn_plan_aux_visited_mem) >> simp[]) >>
  metis_tac[cj 1 fn_plan_aux_visited_mem]
QED
