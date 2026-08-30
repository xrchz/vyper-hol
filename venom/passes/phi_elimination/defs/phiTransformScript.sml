(*
 * PHI Elimination Transformation Definitions
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (initial PHI elimination pass)
 *
 * This theory defines the PHI elimination transformation.
 * The pass replaces PHI nodes that have a single origin with direct assignments,
 * then stably sorts the block by Python's ensure_well_formed key so remaining
 * PHIs/PARAMs stay before executable instructions.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - transform_inst       : Transform a single instruction
 *   - transform_insts      : Transform and stable-sort instructions
 *   - transform_block      : Transform a basic block
 *   - transform_function   : Transform an entire function
 *   - transform_context    : Transform a context (all functions)
 *
 * HELPER THEOREMS:
 *   - transform_block_label      : Label preservation
 *   - transform_block_length     : Length preservation
 *   - lookup_block_transform     : Lookup commutes with transform
 *   - transform_inst_non_phi     : Non-PHI instructions unchanged
 *   - transform_inst_preserves_terminator : Terminator status preserved
 *
 * ============================================================================
 *)

Theory phiTransform
Ancestors
  list finite_map pred_set sorting rich_list
  venomState venomInst venomWf venomExecSemantics phiDefs phiOrigins

(* ==========================================================================
   PHI Elimination Transformation
   ========================================================================== *)

(* TOP-LEVEL: Transform a single instruction.
   If it's a PHI with single origin, replace with ASSIGN from origin's output. *)
Definition transform_inst_def:
  transform_inst dfg inst =
    case phi_single_origin dfg inst of
      SOME origin =>
        (case origin.inst_outputs of
           [src_var] =>
             inst with <|
               inst_opcode := ASSIGN;
               inst_operands := [Var src_var]
             |>
         | _ => inst)
    | NONE => inst
End

(* Python's ensure_well_formed uses stable sort by key:
   PHI/PARAM first, regular instructions next, terminators last. *)
Definition transform_insts_def:
  transform_insts dfg insts =
    let insts' = MAP (transform_inst dfg) insts in
      FILTER (\inst. is_pseudo inst.inst_opcode) insts' ++
      FILTER (\inst. ~is_pseudo inst.inst_opcode /\
                     ~is_terminator inst.inst_opcode) insts' ++
      FILTER (\inst. is_terminator inst.inst_opcode) insts'
End

(* TOP-LEVEL: Transform a basic block by transforming and reordering instructions *)
Definition transform_block_def:
  transform_block dfg bb =
    bb with bb_instructions := transform_insts dfg bb.bb_instructions
End

(* TOP-LEVEL: Transform a function - builds DFG and transforms all blocks *)
Definition transform_function_def:
  transform_function fn =
    let dfg = dfg_build_function fn in
    fn with fn_blocks := MAP (transform_block dfg) fn.fn_blocks
End

(* TOP-LEVEL: Transform a context (all functions) - main entry point *)
Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End

(* ==========================================================================
   Transformation Properties - Helper Lemmas
   ========================================================================== *)

(* Helper: Transform preserves block label *)
Theorem transform_block_label:
  !dfg bb. (transform_block dfg bb).bb_label = bb.bb_label
Proof
  rw[transform_block_def]
QED

Triviality transform_partition_length:
  !insts.
    LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts ++
            FILTER (\inst. ~is_pseudo inst.inst_opcode /\
                           ~is_terminator inst.inst_opcode) insts ++
            FILTER (\inst. is_terminator inst.inst_opcode) insts) =
    LENGTH insts
Proof
  Induct >> simp[LENGTH_APPEND] >> Cases_on `h.inst_opcode` >>
  simp[is_pseudo_def, is_terminator_def, LENGTH_APPEND] >>
  fs[LENGTH_APPEND] >> decide_tac
QED

Theorem transform_insts_length:
  !dfg insts. LENGTH (transform_insts dfg insts) = LENGTH insts
Proof
  rw[transform_insts_def, transform_partition_length]
QED

Theorem transform_block_length:
  !dfg bb.
    LENGTH (transform_block dfg bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[transform_block_def, transform_insts_length]
QED

Triviality transform_partition_perm:
  !insts.
    PERM insts
      (FILTER (\inst. is_pseudo inst.inst_opcode) insts ++
       FILTER (\inst. ~is_pseudo inst.inst_opcode /\
                      ~is_terminator inst.inst_opcode) insts ++
       FILTER (\inst. is_terminator inst.inst_opcode) insts)
Proof
  Induct >> simp[PERM_REFL] >> rpt strip_tac >>
  Cases_on `is_pseudo h.inst_opcode` >> fs[PERM_CONS_IFF] >-
    (Cases_on `h.inst_opcode` >>
     fs[is_pseudo_def, is_terminator_def, PERM_CONS_IFF]) >>
  Cases_on `is_terminator h.inst_opcode` >> fs[]
  >- (simp[PERM_CONS_EQ_APPEND] >>
      qexists_tac `FILTER (\inst. is_pseudo inst.inst_opcode) insts ++
                   FILTER (\inst. ~is_pseudo inst.inst_opcode /\
                                  ~is_terminator inst.inst_opcode) insts` >>
      qexists_tac `FILTER (\inst. is_terminator inst.inst_opcode) insts` >>
      simp[APPEND_ASSOC]) >>
  simp[PERM_CONS_EQ_APPEND] >>
  qexists_tac `FILTER (\inst. is_pseudo inst.inst_opcode) insts` >>
  qexists_tac `FILTER (\inst. ~is_pseudo inst.inst_opcode /\
                              ~is_terminator inst.inst_opcode) insts ++
               FILTER (\inst. is_terminator inst.inst_opcode) insts` >>
  simp[APPEND_ASSOC]
QED

Theorem transform_insts_perm:
  !dfg insts. PERM (MAP (transform_inst dfg) insts) (transform_insts dfg insts)
Proof
  rw[transform_insts_def, transform_partition_perm]
QED

Triviality terminator_not_pseudo:
  !op. is_terminator op ==> ~is_pseudo op
Proof
  Cases >> simp[is_terminator_def, is_pseudo_def]
QED

Triviality append_pred_prefix:
  !P xs ys.
    EVERY P xs /\ EVERY ($~ o P) ys ==>
    !i j. i < j /\ j < LENGTH (xs ++ ys) /\ P (EL j (xs ++ ys)) ==>
          P (EL i (xs ++ ys))
Proof
  rpt strip_tac >>
  Cases_on `j < LENGTH xs`
  >- (`i < LENGTH xs` by decide_tac >>
      `EL i (xs ++ ys) = EL i xs` by simp[rich_listTheory.EL_APPEND1] >>
      qpat_x_assum `EVERY P xs` mp_tac >> simp[EVERY_EL]) >>
  `LENGTH xs <= j` by decide_tac >>
  `j - LENGTH xs < LENGTH ys` by fs[] >>
  `EL j (xs ++ ys) = EL (j - LENGTH xs) ys` by simp[rich_listTheory.EL_APPEND2] >>
  `~P (EL (j - LENGTH xs) ys)` by
    (qpat_x_assum `EVERY ($~ o P) ys` mp_tac >>
     simp[EVERY_EL, combinTheory.o_DEF]) >>
  metis_tac[]
QED

Triviality append_pseudos_prefix:
  !xs ys lbl.
    EVERY (\inst. is_pseudo inst.inst_opcode) xs /\
    EVERY (\inst. ~is_pseudo inst.inst_opcode) ys ==>
    pseudos_prefix <| bb_label := lbl; bb_instructions := xs ++ ys |>
Proof
  rw[pseudos_prefix_def] >>
  qspecl_then [`\inst. is_pseudo inst.inst_opcode`, `xs`, `ys`]
    mp_tac append_pred_prefix >>
  simp[combinTheory.o_DEF] >>
  metis_tac[]
QED

Theorem transform_insts_pseudos_prefix:
  !dfg insts lbl.
    pseudos_prefix <| bb_label := lbl; bb_instructions := transform_insts dfg insts |>
Proof
  rw[transform_insts_def] >>
  qabbrev_tac `insts' = MAP (transform_inst dfg) insts` >>
  qspecl_then
    [`FILTER (\inst. is_pseudo inst.inst_opcode) insts'`,
     `FILTER (\inst. ~is_pseudo inst.inst_opcode /\
              ~is_terminator inst.inst_opcode) insts' ++
      FILTER (\inst. is_terminator inst.inst_opcode) insts'`]
    mp_tac append_pseudos_prefix >>
  simp[EVERY_APPEND, EVERY_MEM, MEM_FILTER] >>
  impl_tac >- metis_tac[terminator_not_pseudo] >>
  simp[]
QED

Theorem transform_block_pseudos_prefix:
  !dfg bb. pseudos_prefix (transform_block dfg bb)
Proof
  rw[transform_block_def] >>
  qspecl_then [`dfg`, `bb.bb_instructions`, `bb.bb_label`]
    mp_tac transform_insts_pseudos_prefix >>
  simp[pseudos_prefix_def]
QED

(* ==========================================================================
   Lookup Helpers
   ========================================================================== *)

(* Helper: Lookup commutes with transform *)
Theorem lookup_block_transform:
  !lbl blocks dfg.
    lookup_block lbl (MAP (transform_block dfg) blocks) =
    OPTION_MAP (transform_block dfg) (lookup_block lbl blocks)
Proof
  Induct_on `blocks` >> simp[lookup_block_def, FIND_thm, transform_block_label] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def, FIND_thm, transform_block_label]
QED

Theorem lookup_block_MEM:
  !lbl blocks bb.
    lookup_block lbl blocks = SOME bb ==> MEM bb blocks
Proof
  Induct_on `blocks` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def] >>
  res_tac >> simp[]
QED

Theorem lookup_block_at_hd:
  !lbl blocks bb.
    blocks <> [] /\
    lbl = (HD blocks).bb_label /\
    lookup_block lbl blocks = SOME bb ==>
    bb = HD blocks
Proof
  Cases_on `blocks` >> simp[lookup_block_def, FIND_thm]
QED

(* ==========================================================================
   Instruction Transform Properties
   ========================================================================== *)

Theorem transform_inst_identity:
  !dfg inst.
    phi_single_origin dfg inst = NONE ==>
    transform_inst dfg inst = inst
Proof
  rw[transform_inst_def]
QED

Theorem phi_single_origin_has_output:
  !dfg inst origin.
    phi_single_origin dfg inst = SOME origin ==>
    ?v. origin.inst_outputs = [v] /\ dfg_lookup dfg v = SOME origin
Proof
  rw[phi_single_origin_def] >> gvs[AllCaseEqs()] >>
  `compute_origins dfg inst DELETE inst <> {}` by
    (strip_tac >> gvs[]) >>
  `CHOICE (compute_origins dfg inst DELETE inst) IN
   (compute_origins dfg inst DELETE inst)` by
    metis_tac[pred_setTheory.CHOICE_DEF] >>
  fs[pred_setTheory.IN_DELETE] >>
  drule_all compute_origins_non_self_in_dfg >> strip_tac >>
  metis_tac[dfg_lookup_single_output]
QED

Theorem transform_inst_phi_iff:
  !dfg inst.
    (transform_inst dfg inst).inst_opcode = PHI <=>
    inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE
Proof
  rpt gen_tac >>
  Cases_on `phi_single_origin dfg inst` >> simp[transform_inst_def] >>
  rename1 `phi_single_origin dfg inst = SOME origin` >>
  drule phi_single_origin_has_output >> strip_tac >>
  simp[]
QED

Theorem transform_inst_kept_phi:
  !dfg inst.
    (transform_inst dfg inst).inst_opcode = PHI ==>
    transform_inst dfg inst = inst
Proof
  rw[transform_inst_phi_iff, transform_inst_identity]
QED

Theorem transform_inst_param_iff:
  !dfg inst.
    (transform_inst dfg inst).inst_opcode = PARAM <=> inst.inst_opcode = PARAM
Proof
  rpt gen_tac >>
  Cases_on `phi_single_origin dfg inst`
  >- (simp[transform_inst_def]) >>
  rename1 `phi_single_origin dfg inst = SOME origin` >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  drule phi_single_origin_has_output >> strip_tac >>
  fs[transform_inst_def, is_phi_inst_def]
QED

Theorem transform_inst_pseudo_iff:
  !dfg inst.
    is_pseudo (transform_inst dfg inst).inst_opcode <=>
    inst.inst_opcode = PARAM \/
    inst.inst_opcode = FMP_PARAM \/
    inst.inst_opcode = RETPC_PARAM \/
    (inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE)
Proof
  rpt gen_tac >>
  Cases_on `phi_single_origin dfg inst`
  >- (simp[transform_inst_def] >>
      Cases_on `inst.inst_opcode` >> simp[is_pseudo_def]) >>
  rename1 `phi_single_origin dfg inst = SOME origin` >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  drule phi_single_origin_has_output >> strip_tac >>
  fs[transform_inst_def, is_phi_inst_def, is_pseudo_def]
QED

Theorem transform_inst_single_origin_assign:
  !dfg inst origin.
    phi_single_origin dfg inst = SOME origin ==>
    ?src_var.
      origin.inst_outputs = [src_var] /\
      transform_inst dfg inst =
        inst with <| inst_opcode := ASSIGN; inst_operands := [Var src_var] |>
Proof
  rpt strip_tac >>
  drule phi_single_origin_has_output >> strip_tac >>
  simp[transform_inst_def]
QED

Theorem transform_inst_single_origin_not_pseudo:
  !dfg inst origin.
    phi_single_origin dfg inst = SOME origin ==>
    ~is_pseudo (transform_inst dfg inst).inst_opcode
Proof
  rpt strip_tac >>
  drule transform_inst_single_origin_assign >> strip_tac >>
  gvs[is_pseudo_def]
QED

Theorem transform_inst_single_origin_not_terminator:
  !dfg inst origin.
    phi_single_origin dfg inst = SOME origin ==>
    ~is_terminator (transform_inst dfg inst).inst_opcode
Proof
  rpt strip_tac >>
  drule transform_inst_single_origin_assign >> strip_tac >>
  gvs[is_terminator_def]
QED

Triviality transform_inst_pseudo_phi:
  !dfg inst.
    is_pseudo (transform_inst dfg inst).inst_opcode /\
    inst.inst_opcode = PHI ==>
    (transform_inst dfg inst).inst_opcode = PHI
Proof
  rpt strip_tac >>
  fs[transform_inst_pseudo_iff, transform_inst_phi_iff]
QED

Triviality phi_prefix_tail:
  !h t.
    (!i j. i < j /\ j < LENGTH (h::t) /\ (EL j (h::t)).inst_opcode = PHI ==>
           (EL i (h::t)).inst_opcode = PHI) ==>
    (!i j. i < j /\ j < LENGTH t /\ (EL j t).inst_opcode = PHI ==>
           (EL i t).inst_opcode = PHI)
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]
QED

Triviality phi_prefix_non_phi_head_tail_no_phi:
  !h t.
    h.inst_opcode <> PHI /\
    (!i j. i < j /\ j < LENGTH (h::t) /\ (EL j (h::t)).inst_opcode = PHI ==>
           (EL i (h::t)).inst_opcode = PHI) ==>
    EVERY (\inst. inst.inst_opcode <> PHI) t
Proof
  rpt strip_tac >> simp[EVERY_EL] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]
QED

Triviality filter_kept_phi_empty_when_no_phi:
  !dfg l.
    EVERY (\inst. inst.inst_opcode <> PHI) l ==>
    FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) l = []
Proof
  Induct_on `l` >> simp[]
QED

Triviality filter_pseudo_transform_phi_prefix:
  !dfg l.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) ==>
    FILTER (\inst. is_pseudo inst.inst_opcode) (MAP (transform_inst dfg) l) =
    FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) l ++
    FILTER (\inst. is_param_opcode inst.inst_opcode) l
Proof
  gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
  sg `(!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
          (EL i l).inst_opcode = PHI)`
  >- (rpt strip_tac >>
      qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH l) /\
                     (EL j (h::l)).inst_opcode = PHI ==>
                     (EL i (h::l)).inst_opcode = PHI`
        (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  sg `FILTER (\inst. is_pseudo inst.inst_opcode) (MAP (transform_inst dfg) l) =
      FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) l ++
      FILTER (\inst. is_param_opcode inst.inst_opcode) l`
  >- metis_tac[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (Cases_on `phi_single_origin dfg h` >>
      simp[transform_inst_phi_iff, transform_inst_kept_phi,
           transform_inst_pseudo_iff, is_pseudo_def, is_param_opcode_def]) >>
  sg `EVERY (\inst. inst.inst_opcode <> PHI) l`
  >- (simp[EVERY_EL] >> rpt strip_tac >>
      qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH l) /\
                     (EL j (h::l)).inst_opcode = PHI ==>
                     (EL i (h::l)).inst_opcode = PHI`
        (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  sg `FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) l = []`
  >- (irule filter_kept_phi_empty_when_no_phi >> simp[]) >>
  Cases_on `is_param_opcode h.inst_opcode` >>
  gvs[transform_inst_pseudo_iff, is_param_opcode_iff,
      transform_inst_def, phi_single_origin_def, is_phi_inst_def]
QED

Triviality terminator_opcode_not_phi:
  !op. is_terminator op ==> op <> PHI
Proof
  Cases >> simp[is_terminator_def]
QED

Theorem transform_insts_phi_prefix:
  !dfg insts lbl.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> ==>
    !i j.
      i < j /\ j < LENGTH (transform_insts dfg insts) /\
      (EL j (transform_insts dfg insts)).inst_opcode = PHI ==>
      (EL i (transform_insts dfg insts)).inst_opcode = PHI
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def, transform_insts_def] >>
  qabbrev_tac `phis = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `regulars = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
                         (MAP (transform_inst dfg) insts)` >>
  qabbrev_tac `terms = FILTER (\inst. is_terminator inst.inst_opcode)
                      (MAP (transform_inst dfg) insts)` >>
  sg `FILTER (\inst. is_pseudo inst.inst_opcode) (MAP (transform_inst dfg) insts) = phis ++ params`
  >- (unabbrev_all_tac >> irule filter_pseudo_transform_phi_prefix >>
      rpt strip_tac >> metis_tac[]) >>
  sg `transform_insts dfg insts = phis ++ params ++ regulars ++ terms`
  >- simp[transform_insts_def, Abbr `regulars`, Abbr `terms`] >>
  sg `EVERY (\inst. inst.inst_opcode = PHI) phis`
  >- simp[Abbr `phis`, EVERY_MEM, MEM_FILTER] >>
  sg `EVERY (\inst. inst.inst_opcode <> PHI) (params ++ regulars ++ terms)`
  >- (simp[EVERY_APPEND, Abbr `params`, Abbr `regulars`, Abbr `terms`,
           EVERY_MEM, MEM_FILTER] >>
      conj_tac
      >- (rpt strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_pseudo_def, is_param_opcode_def]) >>
      rpt strip_tac >> metis_tac[terminator_opcode_not_phi]) >>
  gvs[APPEND_ASSOC] >>
  qspecl_then [`\inst. inst.inst_opcode = PHI`, `phis`,
               `params ++ regulars ++ terms`]
    mp_tac append_pred_prefix >>
  simp_tac std_ss [combinTheory.o_DEF] >>
  asm_simp_tac std_ss [EVERY_APPEND] >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >> simp[]
QED


Triviality phi_prefix_length_no_phi:
  !ys. EVERY (\inst. inst.inst_opcode <> PHI) ys ==> phi_prefix_length ys = 0
Proof
  Induct >> simp[phi_prefix_length_def]
QED

Triviality phi_prefix_all_phi:
  !insts. EVERY (\inst. inst.inst_opcode = PHI) (TAKE (phi_prefix_length insts) insts)
Proof
  Induct_on `insts` >> rw[phi_prefix_length_def]
QED

Triviality filter_regular_transform_phi_prefix:
  !dfg phis.
    EVERY (\inst. inst.inst_opcode = PHI) phis ==>
    FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
      (MAP (transform_inst dfg) phis) =
    MAP (transform_inst dfg)
      (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin) phis)
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  Cases_on `phi_single_origin dfg h`
  >- simp[transform_inst_def, is_pseudo_def] >>
  drule transform_inst_single_origin_assign >> strip_tac >>
  simp[is_pseudo_def, is_terminator_def]
QED

Triviality phi_prefix_length_le_local:
  !insts. phi_prefix_length insts <= LENGTH insts
Proof
  Induct_on `insts` >> rw[phi_prefix_length_def]
QED

Theorem transform_regulars_decompose_phi_prefix:
  !dfg insts.
    FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
      (MAP (transform_inst dfg) insts) =
    MAP (transform_inst dfg)
      (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length insts) insts)) ++
    FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
      (MAP (transform_inst dfg) (DROP (phi_prefix_length insts) insts))
Proof
  rpt gen_tac >>
  qabbrev_tac `p = phi_prefix_length insts` >>
  `MAP (transform_inst dfg) insts =
   MAP (transform_inst dfg) (TAKE p insts) ++
   MAP (transform_inst dfg) (DROP p insts)` by
    (`insts = TAKE p insts ++ DROP p insts` by
       simp[TAKE_DROP, phi_prefix_length_le_local, Abbr `p`] >>
     pop_assum SUBST1_TAC >> simp[MAP_APPEND]) >>
  pop_assum SUBST1_TAC >>
  simp[FILTER_APPEND] >>
  `EVERY (\inst. inst.inst_opcode = PHI) (TAKE p insts)` by
    simp[Abbr `p`, phi_prefix_all_phi] >>
  simp[filter_regular_transform_phi_prefix]
QED

Theorem transform_insts_decompose_phi_prefix:
  !dfg insts lbl.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> ==>
    transform_insts dfg insts =
      FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts ++
      FILTER (\inst. is_param_opcode inst.inst_opcode) insts ++
      MAP (transform_inst dfg)
        (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
          (TAKE (phi_prefix_length insts) insts)) ++
      FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
        (MAP (transform_inst dfg) (DROP (phi_prefix_length insts) insts)) ++
      FILTER (\inst. is_terminator inst.inst_opcode) (MAP (transform_inst dfg) insts)
Proof
  rpt strip_tac >>
  simp[transform_insts_def, LET_DEF] >>
  `FILTER (\inst. is_pseudo inst.inst_opcode) (MAP (transform_inst dfg) insts) =
   FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts ++
   FILTER (\inst. is_param_opcode inst.inst_opcode) insts` by
    (irule filter_pseudo_transform_phi_prefix >>
     fs[bb_well_formed_def]) >>
  `FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
      (MAP (transform_inst dfg) insts) =
   MAP (transform_inst dfg)
      (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length insts) insts)) ++
   FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
      (MAP (transform_inst dfg) (DROP (phi_prefix_length insts) insts))` by
    ACCEPT_TAC (Q.SPECL [`dfg`, `insts`] transform_regulars_decompose_phi_prefix) >>
  asm_rewrite_tac[] >>
  rewrite_tac[APPEND_ASSOC]
QED

Triviality eval_phis_no_phi_local:
  !s ys. EVERY (\inst. inst.inst_opcode <> PHI) ys ==> eval_phis s ys = OK s
Proof
  gen_tac >> Induct >> simp[eval_phis_def]
QED

Triviality phi_prefix_length_append_no_phi:
  !xs ys.
    EVERY (\inst. inst.inst_opcode = PHI) xs /\
    EVERY (\inst. inst.inst_opcode <> PHI) ys ==>
    phi_prefix_length (xs ++ ys) = LENGTH xs
Proof
  Induct >> simp[phi_prefix_length_def, phi_prefix_length_no_phi] >>
  rpt strip_tac >> gvs[]
QED

Triviality take_phi_prefix_append_no_phi:
  !xs ys.
    EVERY (\inst. inst.inst_opcode = PHI) xs /\
    EVERY (\inst. inst.inst_opcode <> PHI) ys ==>
    TAKE (phi_prefix_length (xs ++ ys)) (xs ++ ys) = xs
Proof
  rpt strip_tac >>
  `phi_prefix_length (xs ++ ys) = LENGTH xs` by
    (irule phi_prefix_length_append_no_phi >> simp[]) >>
  simp[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Triviality eval_phis_append_no_phi:
  !s xs ys.
    EVERY (\inst. inst.inst_opcode = PHI) xs /\
    EVERY (\inst. inst.inst_opcode <> PHI) ys ==>
    eval_phis s (xs ++ ys) = eval_phis s xs
Proof
  gen_tac >> Induct >> simp[eval_phis_def, eval_phis_no_phi_local] >> rpt strip_tac >>
  gvs[] >> Cases_on `eval_one_phi s h` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

Theorem transform_insts_phi_prefix_exact:
  !dfg insts lbl.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> ==>
    let kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts in
      phi_prefix_length (transform_insts dfg insts) = LENGTH kept /\
      TAKE (phi_prefix_length (transform_insts dfg insts)) (transform_insts dfg insts) = kept /\
      eval_phis s (transform_insts dfg insts) = eval_phis s kept
Proof
  rpt strip_tac >> simp[LET_DEF] >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `regulars = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
                         (MAP (transform_inst dfg) insts)` >>
  qabbrev_tac `terms = FILTER (\inst. is_terminator inst.inst_opcode)
                      (MAP (transform_inst dfg) insts)` >>
  `FILTER (\inst. is_pseudo inst.inst_opcode) (MAP (transform_inst dfg) insts) = kept ++ params` by
    (unabbrev_all_tac >> irule filter_pseudo_transform_phi_prefix >>
     fs[bb_well_formed_def] >> rpt strip_tac >> metis_tac[]) >>
  `transform_insts dfg insts = kept ++ (params ++ regulars ++ terms)` by
    simp[transform_insts_def, Abbr `regulars`, Abbr `terms`, APPEND_ASSOC] >>
  `EVERY (\inst. inst.inst_opcode = PHI) kept` by
    simp[Abbr `kept`, EVERY_MEM, MEM_FILTER] >>
  `EVERY (\inst. inst.inst_opcode <> PHI) (params ++ regulars ++ terms)` by
    (simp[EVERY_APPEND, Abbr `params`, Abbr `regulars`, Abbr `terms`,
          EVERY_MEM, MEM_FILTER] >>
     conj_tac
     >- (rpt strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_pseudo_def, is_param_opcode_def]) >>
     rpt strip_tac >> metis_tac[terminator_opcode_not_phi]) >>
  rpt conj_tac
  >- (qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
      irule phi_prefix_length_append_no_phi >> simp[])
  >- (qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
      irule take_phi_prefix_append_no_phi >> simp[])
  >- (qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
      irule eval_phis_append_no_phi >> simp[])
QED

Theorem transform_inst_non_phi:
  !dfg inst.
    ~is_phi_inst inst ==>
    transform_inst dfg inst = inst
Proof
  rw[transform_inst_def, phi_single_origin_def]
QED

Theorem transform_inst_preserves_outputs:
  !dfg inst. (transform_inst dfg inst).inst_outputs = inst.inst_outputs
Proof
  rw[transform_inst_def] >>
  Cases_on `phi_single_origin dfg inst` >> simp[] >>
  Cases_on `x.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem transform_inst_preserves_id:
  !dfg inst. (transform_inst dfg inst).inst_id = inst.inst_id
Proof
  rw[transform_inst_def] >>
  Cases_on `phi_single_origin dfg inst` >> simp[] >>
  Cases_on `x.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem transform_inst_preserves_operands_non_phi:
  !dfg inst.
    ~is_phi_inst inst ==>
    (transform_inst dfg inst).inst_operands = inst.inst_operands
Proof
  rw[transform_inst_non_phi]
QED

Theorem transform_insts_outputs_perm:
  !dfg insts.
    PERM (FLAT (MAP (\i. i.inst_outputs) (transform_insts dfg insts)))
         (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  rpt strip_tac >>
  `PERM (MAP (\i. i.inst_outputs) (MAP (transform_inst dfg) insts))
        (MAP (\i. i.inst_outputs) (transform_insts dfg insts))` by
    metis_tac[transform_insts_perm, PERM_MAP] >>
  `MAP (\i. i.inst_outputs) (MAP (transform_inst dfg) insts) =
   MAP (\i. i.inst_outputs) insts` by
    simp[MAP_MAP_o, combinTheory.o_DEF, transform_inst_preserves_outputs] >>
  metis_tac[PERM_FLAT, PERM_SYM]
QED

Theorem transform_insts_ids_perm:
  !dfg insts.
    PERM (MAP (\i. i.inst_id) (transform_insts dfg insts))
         (MAP (\i. i.inst_id) insts)
Proof
  rpt strip_tac >>
  `PERM (MAP (\i. i.inst_id) (MAP (transform_inst dfg) insts))
        (MAP (\i. i.inst_id) (transform_insts dfg insts))` by
    metis_tac[transform_insts_perm, PERM_MAP] >>
  `MAP (\i. i.inst_id) (MAP (transform_inst dfg) insts) =
   MAP (\i. i.inst_id) insts` by
    simp[MAP_MAP_o, combinTheory.o_DEF, transform_inst_preserves_id] >>
  metis_tac[PERM_SYM]
QED

Theorem transform_blocks_outputs_perm:
  !dfg blocks.
    PERM (FLAT (MAP (\i. i.inst_outputs)
             (fn_insts_blocks (MAP (transform_block dfg) blocks))))
         (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks blocks)))
Proof
  gen_tac >> Induct >> simp[fn_insts_blocks_def] >>
  simp[transform_block_def, MAP_APPEND, FLAT_APPEND] >>
  rpt strip_tac >>
  metis_tac[transform_insts_outputs_perm, PERM_CONG]
QED

Theorem transform_blocks_ids_perm:
  !dfg blocks.
    PERM (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
             (MAP (transform_block dfg) blocks)))
         (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) blocks))
Proof
  gen_tac >> Induct >> simp[transform_block_def] >>
  rpt strip_tac >>
  metis_tac[transform_insts_ids_perm, PERM_CONG]
QED

Theorem transform_inst_preserves_terminator:
  !dfg inst.
    is_terminator (transform_inst dfg inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rw[transform_inst_def] >>
  Cases_on `phi_single_origin dfg inst` >> simp[] >>
  Cases_on `x.inst_outputs` >> simp[is_terminator_def] >>
  Cases_on `t` >> simp[is_terminator_def] >>
  fs[phi_single_origin_def] >>
  Cases_on `is_phi_inst inst` >> fs[is_phi_inst_def, is_terminator_def]
QED

Theorem transform_inst_phi_to_assign:
  !dfg inst origin src_var.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] ==>
    transform_inst dfg inst =
      inst with <| inst_opcode := ASSIGN; inst_operands := [Var src_var] |>
Proof
  rw[transform_inst_def]
QED

Theorem transform_inst_nonterminator:
  !dfg inst.
    ~is_terminator inst.inst_opcode ==>
    ~is_terminator (transform_inst dfg inst).inst_opcode
Proof
  rw[transform_inst_preserves_terminator]
QED

Triviality filter_last_when_last_passes:
  !P l. l <> [] /\ P (LAST l) ==> FILTER P l <> [] /\ LAST (FILTER P l) = LAST l
Proof
  gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `l = []`
  >- (gvs[LAST_DEF] >> simp[FILTER]) >>
  gvs[LAST_DEF] >>
  `FILTER P l <> [] /\ LAST (FILTER P l) = LAST l` by simp[] >>
  Cases_on `P h` >> gvs[FILTER, LAST_DEF]
QED

Triviality terminator_not_phi:
  !op. is_terminator op ==> op <> PHI
Proof
  Cases >> simp[is_terminator_def]
QED

Theorem transform_insts_last:
  !dfg insts.
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode ==>
    LAST (transform_insts dfg insts) = LAST insts
Proof
  rpt strip_tac >>
  rw[transform_insts_def] >>
  qabbrev_tac `insts' = MAP (transform_inst dfg) insts` >>
  `insts' <> []` by simp[Abbr `insts'`] >>
  `LAST insts' = transform_inst dfg (LAST insts)` by
    simp[Abbr `insts'`, LAST_MAP] >>
  `is_terminator (LAST insts').inst_opcode` by
    simp[transform_inst_preserves_terminator] >>
  `FILTER (\inst. is_terminator inst.inst_opcode) insts' <> [] /\
   LAST (FILTER (\inst. is_terminator inst.inst_opcode) insts') = LAST insts'` by
    (irule filter_last_when_last_passes >> simp[]) >>
  `transform_inst dfg (LAST insts) = LAST insts` by
    (irule transform_inst_non_phi >>
     fs[is_phi_inst_def] >> metis_tac[terminator_not_phi]) >>
  simp[LAST_APPEND_NOT_NIL]
QED

Triviality filter_terminator_singleton:
  !insts.
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode /\
    (!i. i < LENGTH insts /\ is_terminator (EL i insts).inst_opcode ==>
         i = PRE (LENGTH insts)) ==>
    FILTER (\inst. is_terminator inst.inst_opcode) insts = [LAST insts]
Proof
  Induct_on `insts` >> simp[] >> rpt strip_tac >>
  Cases_on `insts = []`
  >- (gvs[LAST_DEF] >> simp[]) >>
  `~is_terminator h.inst_opcode` by
    (strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  sg `insts <> [] /\ is_terminator (LAST insts).inst_opcode /\
      (!i. i < LENGTH insts /\ is_terminator (EL i insts).inst_opcode ==>
           i = PRE (LENGTH insts))`
  >- (conj_tac >- simp[] >> conj_tac
      >- (Cases_on `insts` >> gvs[LAST_DEF]) >>
      rpt strip_tac >>
      qpat_x_assum `!i. i < SUC (LENGTH insts) /\ _ ==> _`
        (qspec_then `SUC i` mp_tac) >> simp[]) >>
  `FILTER (\inst. is_terminator inst.inst_opcode) insts = [LAST insts]` by
    metis_tac[] >>
  simp[] >>
  Cases_on`insts` >- fs[] >>
  simp[]
QED

Triviality transform_insts_terminator_only_last:
  !dfg insts i.
    insts <> [] /\
    is_terminator (LAST insts).inst_opcode /\
    (!i. i < LENGTH insts /\ is_terminator (EL i insts).inst_opcode ==>
         i = PRE (LENGTH insts)) /\
    i < LENGTH (transform_insts dfg insts) /\
    is_terminator (EL i (transform_insts dfg insts)).inst_opcode ==>
    i = PRE (LENGTH (transform_insts dfg insts))
Proof
  rpt strip_tac >>
  rw[transform_insts_def] >>
  qabbrev_tac `insts' = MAP (transform_inst dfg) insts` >>
  qabbrev_tac `pseudos = FILTER (\inst. is_pseudo inst.inst_opcode) insts'` >>
  qabbrev_tac `regulars = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode) insts'` >>
  qabbrev_tac `terms = FILTER (\inst. is_terminator inst.inst_opcode) insts'` >>
  `insts' <> []` by simp[Abbr `insts'`] >>
  `LAST insts' = transform_inst dfg (LAST insts)` by simp[Abbr `insts'`, LAST_MAP] >>
  `is_terminator (LAST insts').inst_opcode` by simp[transform_inst_preserves_terminator] >>
  sg `(!k. k < LENGTH insts' /\ is_terminator (EL k insts').inst_opcode ==>
        k = PRE (LENGTH insts'))`
  >- (qunabbrev_tac `insts'` >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!i. i < LENGTH insts /\ is_terminator (EL i insts).inst_opcode ==>
                     i = PRE (LENGTH insts)` (qspec_then `k` mp_tac) >>
      simp[] >> impl_tac
      >- (`EL k (MAP (transform_inst dfg) insts) = transform_inst dfg (EL k insts)` by
            simp[EL_MAP] >>
          metis_tac[transform_inst_preserves_terminator]) >>
      simp[]) >>
  `terms = [LAST insts]` by
    (qunabbrev_tac `terms` >>
     qspecl_then [`insts'`] mp_tac filter_terminator_singleton >> simp[] >>
     simp[Abbr `insts'`, LAST_MAP] >>
     `transform_inst dfg (LAST insts) = LAST insts` by
       (irule transform_inst_non_phi >> fs[is_phi_inst_def] >> metis_tac[terminator_not_phi]) >>
     simp[]) >>
  qabbrev_tac `prefix = pseudos ++ regulars` >>
  `pseudos ++ regulars ++ terms = prefix ++ [LAST insts]` by
    simp[Abbr `prefix`] >>
  `transform_insts dfg insts = prefix ++ [LAST insts]` by
    (simp[transform_insts_def, Abbr `insts'`, Abbr `pseudos`,
          Abbr `regulars`, Abbr `terms`] >>
     simp[Abbr `prefix`]) >>
  `EVERY (\inst. ~is_terminator inst.inst_opcode) prefix` by
    (simp[Abbr `prefix`, Abbr `pseudos`, Abbr `regulars`, EVERY_APPEND,
          EVERY_MEM, MEM_FILTER] >>
     metis_tac[terminator_not_pseudo]) >>
  qpat_x_assum `transform_insts dfg insts = prefix ++ [LAST insts]`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE[th]) >> rewrite_tac[th]) >>
  Cases_on `i < LENGTH prefix`
  >- (`EL i (prefix ++ [LAST insts]) = EL i prefix` by simp[rich_listTheory.EL_APPEND1] >>
      `~is_terminator (EL i prefix).inst_opcode` by fs[EVERY_EL] >>
      fs[]) >>
  `i = LENGTH prefix` by fs[] >>
  `LENGTH prefix = LENGTH pseudos + LENGTH regulars` by simp[Abbr `prefix`] >>
  BasicProvers.VAR_EQ_TAC >>
  pop_assum SUBST1_TAC >>
  BasicProvers.VAR_EQ_TAC >>
  simp_tac(srw_ss()++ARITH_ss)[arithmeticTheory.PRE_SUB1]
QED

Theorem transform_block_well_formed:
  !dfg bb. bb_well_formed bb ==> bb_well_formed (transform_block dfg bb)
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def, transform_block_def] >>
  rpt conj_tac
  >- (Cases_on `bb.bb_instructions` >> fs[] >>
      strip_tac >> qspecl_then [`dfg`, `h::t`] mp_tac transform_insts_length >> simp[])
  >- (Cases_on `bb.bb_instructions` >> gvs[] >>
      qspecl_then [`dfg`, `h::t`] mp_tac transform_insts_last >> simp[])
  >- (rpt strip_tac >> irule transform_insts_terminator_only_last >> simp[])
  >- (rpt strip_tac >>
      qspecl_then [`dfg`, `bb.bb_instructions`, `bb.bb_label`]
        mp_tac transform_insts_phi_prefix >>
      simp[bb_well_formed_def] >>
      impl_tac >- metis_tac[] >>
      disch_then (qspecl_then [`i`, `j`] mp_tac) >> simp[])
QED

Theorem transform_block_succs:
  !dfg bb. bb_well_formed bb ==> bb_succs (transform_block dfg bb) = bb_succs bb
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def, transform_block_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `transform_insts dfg (h::t)`
  >- (qspecl_then [`dfg`, `h::t`] mp_tac transform_insts_length >> simp[]) >>
  `LAST (h'::t') = LAST (h::t)` by
    (qspecl_then [`dfg`, `h::t`] mp_tac transform_insts_last >> simp[]) >>
  simp[bb_succs_def]
QED

Theorem MEM_transform_inst_transform_insts:
  !dfg inst insts.
    MEM inst insts ==> MEM (transform_inst dfg inst) (transform_insts dfg insts)
Proof
  rw[transform_insts_def, MEM_FILTER, MEM_MAP] >>
  Cases_on `is_pseudo (transform_inst dfg inst).inst_opcode` >> simp[] >-
    metis_tac[] >>
  Cases_on `is_terminator (transform_inst dfg inst).inst_opcode` >> simp[] >>
  metis_tac[]
QED

Theorem MEM_transform_inst_transform_block:
  !dfg bb inst.
    MEM inst bb.bb_instructions ==>
    MEM (transform_inst dfg inst) (transform_block dfg bb).bb_instructions
Proof
  rw[transform_block_def, MEM_transform_inst_transform_insts]
QED

(* Helper for callers that separately establish the stable-sort result is unchanged. *)
Theorem transform_block_identity:
  !dfg bb.
    transform_insts dfg bb.bb_instructions = bb.bb_instructions ==>
    (transform_block dfg bb).bb_instructions = bb.bb_instructions
Proof
  rw[transform_block_def]
QED

(* Running a block is the same when the transformed block is syntactically unchanged. *)
Theorem exec_block_transform_identity:
  !bb s dfg fuel ctx.
    transform_block dfg bb = bb ==>
    exec_block fuel ctx (transform_block dfg bb) s = exec_block fuel ctx bb s
Proof
  rw[]
QED
