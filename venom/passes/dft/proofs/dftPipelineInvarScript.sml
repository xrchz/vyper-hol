(*
 * DFT Pipeline Invariance — supporting lemmas
 *
 * Key results:
 *   inst_data_deps_id_agree — under unique_defs + id-structure agreement,
 *     inst_data_deps returns same inst_ids for permuted block_insts
 *   build_eda_agree — same effect-ful subsequence and id set => same eda map
 *   build_full_eda_pseudo_strip — build_full_eda ignores pseudo instructions
 *
 * Definitions:
 *   has_effects — predicate for instructions with non-empty effect sets
 *   eda_fold_step — single-step fold function used in build_eda
 *)

Theory dftPipelineInvar
Ancestors
  dftStructural dftIdempotent dftDefs venomExecSemantics venomEffects
  passSharedDefs venomInst list rich_list sorting finite_map pred_set combin
Libs
  BasicProvers

(* ================================================================
   Helpers
   ================================================================ *)

Theorem unique_defs_no_shared_output:
  !insts i j var.
    unique_defs insts /\
    MEM i insts /\ MEM j insts /\ i <> j /\
    MEM var i.inst_outputs /\ MEM var j.inst_outputs ==>
    F
Proof
  rpt gen_tac >> strip_tac >> fs[unique_defs_def] >>
  `?ni. ni < LENGTH insts /\ EL ni insts = i` by metis_tac[MEM_EL] >>
  `?nj. nj < LENGTH insts /\ EL nj insts = j` by metis_tac[MEM_EL] >>
  `ni <> nj` by (strip_tac >> gvs[]) >>
  `ni < nj \/ nj < ni` by DECIDE_TAC >| [
    first_x_assum (qspecl_then [`ni`, `nj`] mp_tac) >>
    simp[IN_DISJOINT] >> metis_tac[],
    first_x_assum (qspecl_then [`nj`, `ni`] mp_tac) >>
    simp[IN_DISJOINT] >> metis_tac[]
  ]
QED

Theorem producing_inst_perm_id:
  !insts1 insts2 var i1 i2.
    unique_defs insts1 /\
    producing_inst insts1 var = SOME i1 /\
    producing_inst insts2 var = SOME i2 /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) ==>
    i2.inst_id = i1.inst_id
Proof
  rpt strip_tac >>
  `MEM i2 insts2 /\ MEM var i2.inst_outputs` by metis_tac[producing_inst_unique] >>
  `?k. MEM k insts1 /\ k.inst_id = i2.inst_id /\ k.inst_outputs = i2.inst_outputs`
    by metis_tac[] >>
  `MEM var k.inst_outputs` by metis_tac[] >>
  `MEM i1 insts1 /\ MEM var i1.inst_outputs` by metis_tac[producing_inst_unique] >>
  Cases_on `k = i1` >> gvs[] >>
  metis_tac[unique_defs_no_shared_output]
QED

Triviality producing_inst_none_no_mem:
  !insts var.
    producing_inst insts var = NONE ==>
    !i. MEM i insts ==> ~MEM var i.inst_outputs
Proof
  Induct >> rw[producing_inst_def] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem producing_inst_none_agree:
  !insts1 insts2 var.
    producing_inst insts1 var = NONE /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_outputs = j.inst_outputs) ==>
    producing_inst insts2 var = NONE
Proof
  rpt strip_tac >>
  Cases_on `producing_inst insts2 var` >> simp[] >>
  rename1 `SOME i2` >>
  imp_res_tac producing_inst_unique >>
  `?k. MEM k insts1 /\ k.inst_outputs = i2.inst_outputs` by metis_tac[] >>
  `~MEM var k.inst_outputs` by metis_tac[producing_inst_none_no_mem] >>
  metis_tac[]
QED

(* ================================================================
   operand_producer inst_id agreement
   ================================================================ *)

(* Under unique_defs, operand_producer on two lists with same
   inst_id+outputs elements returns OPTION_MAP with same inst_id *)
Triviality operand_producer_id_agree:
  !insts1 insts2 op.
    unique_defs insts1 /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) /\
    (!k. MEM k insts1 ==>
         ?j. MEM j insts2 /\ j.inst_id = k.inst_id /\
             j.inst_outputs = k.inst_outputs) ==>
    case (operand_producer insts1 op, operand_producer insts2 op) of
      (NONE, NONE) => T
    | (SOME i1, SOME i2) => i1.inst_id = i2.inst_id
    | (NONE, SOME _) => F
    | (SOME _, NONE) => F
Proof
  rpt strip_tac >>
  Cases_on `op` >> simp[operand_producer_def] >>
  Cases_on `producing_inst insts1 s` >>
  Cases_on `producing_inst insts2 s` >> simp[]
  (* NONE/SOME: use producing_inst_none_agree to derive contradiction *)
  >- (rename1 `_ = SOME i2` >>
      `!j. MEM j insts2 ==> ?k. MEM k insts1 /\ k.inst_outputs = j.inst_outputs`
        by (rpt strip_tac >> res_tac >> metis_tac[]) >>
      drule_all producing_inst_none_agree >> gvs[])
  (* SOME/NONE: symmetric case *)
  >- (rename1 `_ = SOME i1` >>
      `!j. MEM j insts1 ==> ?k. MEM k insts2 /\ k.inst_outputs = j.inst_outputs`
        by (rpt strip_tac >> res_tac >> metis_tac[]) >>
      drule_all producing_inst_none_agree >> gvs[])
  (* SOME/SOME: use producing_inst_perm_id *)
  >> drule_all producing_inst_perm_id >> simp[]
QED

(* ================================================================
   inst_data_deps inst_id agreement
   ================================================================ *)

(* MAP THE o FILTER IS_SOME o MAP preserves inst_id when individual
   elements agree on inst_id *)
Triviality map_the_filter_id_agree:
  !f1 f2 ls.
    (!x. MEM x ls ==>
      case (f1 x, f2 x) of
        (NONE, NONE) => T
      | (SOME a, SOME b) => a.inst_id = b.inst_id
      | (NONE, SOME _) => F
      | (SOME _, NONE) => F) ==>
    MAP (\i. i.inst_id) (MAP THE (FILTER IS_SOME (MAP f1 ls))) =
    MAP (\i. i.inst_id) (MAP THE (FILTER IS_SOME (MAP f2 ls)))
Proof
  ntac 2 gen_tac >> Induct >- simp[] >>
  rpt strip_tac >>
  (* Discharge IH: restrict MEM hypothesis to tail *)
  `MAP (\i. i.inst_id) (MAP THE (FILTER IS_SOME (MAP f1 ls))) =
   MAP (\i. i.inst_id) (MAP THE (FILTER IS_SOME (MAP f2 ls)))` by
    (first_x_assum irule >> rpt strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[MEM]) >>
  (* Handle the head *)
  first_x_assum (qspec_then `h` mp_tac) >> simp[MEM] >>
  Cases_on `f1 h` >> Cases_on `f2 h` >> simp[MAP, FILTER]
QED

(* Key nub lemma: if MAP f agrees and f is injective on each list's elements,
   then MAP f after nub also agrees. Proof via nub_MAP_INJ. *)
Triviality nub_map_agree:
  !f xs ys.
    MAP f xs = MAP f ys /\
    INJ f (set xs) UNIV /\
    INJ f (set ys) UNIV ==>
    MAP f (nub xs) = MAP f (nub ys)
Proof
  rpt strip_tac >>
  `nub (MAP f xs) = MAP f (nub xs)` by metis_tac[nub_MAP_INJ] >>
  `nub (MAP f ys) = MAP f (nub ys)` by metis_tac[nub_MAP_INJ] >>
  metis_tac[]
QED

(* producing_inst returns unique objects: same inst_id implies same object,
   because producing_inst scans the list and returns the first match,
   and under unique_defs + ALL_DISTINCT inst_ids, the match is unique. *)
Triviality producing_inst_inj:
  !insts v1 v2 i1 i2.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    producing_inst insts v1 = SOME i1 /\
    producing_inst insts v2 = SOME i2 /\
    i1.inst_id = i2.inst_id ==>
    i1 = i2
Proof
  Induct >> rw[producing_inst_def] >>
  BasicProvers.every_case_tac >> gvs[MEM_MAP] >>
  imp_res_tac producing_inst_unique >> metis_tac[]
QED

(* operand_producer SOME results come from producing_inst *)
Triviality operand_producer_is_producing:
  !insts op i.
    operand_producer insts op = SOME i ==>
    ?v. producing_inst insts v = SOME i
Proof
  Cases_on `op` >> rw[operand_producer_def] >> metis_tac[]
QED

(* Any element of MAP THE (FILTER IS_SOME (MAP f ls)) is f(x) for some x in ls *)
Triviality mem_map_the_filter:
  !f ls x.
    MEM x (MAP THE (FILTER IS_SOME (MAP f ls))) ==>
    ?y. MEM y ls /\ f y = SOME x
Proof
  ntac 1 gen_tac >> Induct >> simp[MAP, FILTER] >> rpt strip_tac >>
  Cases_on `f h` >> gvs[FILTER, MEM] >> metis_tac[]
QED

(* Helper: any member of a deps list (var_deps or order_deps) comes from
   producing_inst, giving us a SOME equation we can feed to producing_inst_inj *)
Triviality mem_var_deps_producing:
  !insts ops x.
    MEM x (MAP THE (FILTER IS_SOME (MAP (operand_producer insts) ops))) ==>
    ?v. producing_inst insts v = SOME x
Proof
  rpt strip_tac >>
  drule mem_map_the_filter >> strip_tac >>
  drule operand_producer_is_producing >> metis_tac[]
QED

Triviality mem_order_deps_producing:
  !insts order x.
    MEM x (MAP THE (FILTER IS_SOME (MAP (producing_inst insts) order))) ==>
    ?v. producing_inst insts v = SOME x
Proof
  rpt strip_tac >> drule mem_map_the_filter >> metis_tac[]
QED

(* var_deps and order_deps elements satisfy INJ inst_id.
   Matches inst_data_deps_def (order_deps include self-dep filter). *)
Triviality deps_list_inj:
  !insts order inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    let var_deps = MAP THE (FILTER IS_SOME
      (MAP (operand_producer insts) inst.inst_operands)) in
    let order_deps =
      if is_terminator inst.inst_opcode
      then FILTER (\d. d.inst_id <> inst.inst_id)
             (MAP THE (FILTER IS_SOME (MAP (producing_inst insts) order)))
      else [] in
    INJ (\i. i.inst_id) (set (var_deps ++ order_deps)) UNIV
Proof
  rpt strip_tac >> simp[INJ_DEF] >> rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[MEM_APPEND, MEM, MEM_FILTER] >>
  rpt (first_x_assum
    (strip_assume_tac o MATCH_MP mem_var_deps_producing)) >>
  rpt (first_x_assum
    (strip_assume_tac o MATCH_MP mem_order_deps_producing)) >>
  irule producing_inst_inj >> metis_tac[]
QED

(* Helper: var_deps MAP inst_id agrees *)
Triviality var_deps_id_agree:
  !insts1 insts2 ops.
    unique_defs insts1 /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) /\
    (!k. MEM k insts1 ==>
         ?j. MEM j insts2 /\ j.inst_id = k.inst_id /\
             j.inst_outputs = k.inst_outputs) ==>
    MAP (\i. i.inst_id)
      (MAP THE (FILTER IS_SOME (MAP (operand_producer insts1) ops))) =
    MAP (\i. i.inst_id)
      (MAP THE (FILTER IS_SOME (MAP (operand_producer insts2) ops)))
Proof
  rpt strip_tac >> irule map_the_filter_id_agree >> rpt strip_tac >>
  mp_tac (Q.SPECL [`insts1`, `insts2`, `x`] operand_producer_id_agree) >>
  impl_tac >- metis_tac[] >>
  Cases_on `operand_producer insts1 x` >>
  Cases_on `operand_producer insts2 x` >> simp[]
QED

(* Helper: order_deps MAP inst_id agrees *)
Triviality order_deps_id_agree:
  !insts1 insts2 order.
    unique_defs insts1 /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) /\
    (!k. MEM k insts1 ==>
         ?j. MEM j insts2 /\ j.inst_id = k.inst_id /\
             j.inst_outputs = k.inst_outputs) ==>
    MAP (\i. i.inst_id)
      (MAP THE (FILTER IS_SOME (MAP (producing_inst insts1) order))) =
    MAP (\i. i.inst_id)
      (MAP THE (FILTER IS_SOME (MAP (producing_inst insts2) order)))
Proof
  rpt strip_tac >> irule map_the_filter_id_agree >> rpt strip_tac >>
  Cases_on `producing_inst insts1 x` >>
  Cases_on `producing_inst insts2 x` >> simp[]
  (* NONE/SOME on insts2: use none_agree insts1→insts2 *)
  >- (`!j. MEM j insts2 ==> ?k. MEM k insts1 /\ k.inst_outputs = j.inst_outputs`
       by (rpt strip_tac >> res_tac >> metis_tac[]) >>
      drule_all producing_inst_none_agree >> gvs[])
  (* SOME/NONE on insts2: use none_agree insts2→insts1 *)
  >- (`!j. MEM j insts1 ==> ?k. MEM k insts2 /\ k.inst_outputs = j.inst_outputs`
       by (rpt strip_tac >> res_tac >> metis_tac[]) >>
      drule_all producing_inst_none_agree >> gvs[])
  >> drule_all producing_inst_perm_id >> simp[]
QED

(* If MAP f l1 = MAP f l2, filtering by a predicate on f preserves the
   MAP f agreement. Used for the FILTER in inst_data_deps order_deps. *)
Triviality filter_map_agree:
  !f P l1 l2.
    MAP f l1 = MAP f l2 ==>
    MAP f (FILTER (\x. P (f x)) l1) = MAP f (FILTER (\x. P (f x)) l2)
Proof
  Induct_on `l1` >> Cases_on `l2` >> simp[] >>
  rpt strip_tac >> Cases_on `P (f h)` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* inst_data_deps returns same inst_ids for two agreeing block_insts lists *)
Theorem inst_data_deps_id_agree:
  !insts1 insts2 order inst.
    unique_defs insts1 /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts1) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts2) /\
    (!j. MEM j insts2 ==>
         ?k. MEM k insts1 /\ k.inst_id = j.inst_id /\
             k.inst_outputs = j.inst_outputs) /\
    (!k. MEM k insts1 ==>
         ?j. MEM j insts2 /\ j.inst_id = k.inst_id /\
             j.inst_outputs = k.inst_outputs) ==>
    MAP (\i. i.inst_id)
      (inst_data_deps insts2 order inst) =
    MAP (\i. i.inst_id)
      (inst_data_deps insts1 order inst)
Proof
  rpt strip_tac >>
  simp[inst_data_deps_def, LET_THM] >>
  imp_res_tac var_deps_id_agree >>
  imp_res_tac order_deps_id_agree >>
  `MAP (\i. i.inst_id)
     (FILTER (\d. d.inst_id <> inst.inst_id)
       (MAP THE (FILTER IS_SOME (MAP (producing_inst insts2) order)))) =
   MAP (\i. i.inst_id)
     (FILTER (\d. d.inst_id <> inst.inst_id)
       (MAP THE (FILTER IS_SOME (MAP (producing_inst insts1) order))))` by
    (qspecl_then [`\d. d.inst_id`, `\x. x <> inst.inst_id`]
       mp_tac filter_map_agree >> simp[]) >>
  irule nub_map_agree >> rpt conj_tac
  >- (Cases_on `is_terminator inst.inst_opcode` >> gvs[MAP_APPEND])
  >- (mp_tac (Q.SPECL [`insts2`, `order`, `inst`] deps_list_inj) >>
      simp[LET_THM, LIST_TO_SET_APPEND])
  >> mp_tac (Q.SPECL [`insts1`, `order`, `inst`] deps_list_inj) >>
  simp[LET_THM, LIST_TO_SET_APPEND]
QED

(* ================================================================
   Effect-free instruction lemmas
   ================================================================ *)

(* Flippable opcodes are effect-free: no writes, no reads *)
Triviality is_flippable_effect_free:
  !op. is_flippable op ==>
    write_effects op = {} /\ read_effects op = {}
Proof
  Cases >> simp[is_flippable_def, is_commutative_def, is_comparator_def,
                write_effects_def, read_effects_def, empty_effects_def]
QED

(* Effect-free instructions are identity in compute_effect_deps *)
Triviality compute_effect_deps_eff_free:
  !et inst.
    write_effects inst.inst_opcode = {} /\
    read_effects inst.inst_opcode = {} ==>
    compute_effect_deps et inst = ([], et)
Proof
  rpt strip_tac >>
  simp[compute_effect_deps_def, LET_THM, effects_to_list_def,
       FILTER_EQ_NIL, EVERY_MEM, MEM]
QED

(* ================================================================
   compute_effect_deps key locality
   ================================================================ *)

(* All effect values appear in the master list *)
Triviality effect_mem_all:
  !e. MEM e [Eff_STORAGE; Eff_TRANSIENT; Eff_MEMORY; Eff_FMP;
             Eff_IMMUTABLES; Eff_RETURNDATA; Eff_LOG; Eff_BALANCE;
             Eff_EXTCODE]
Proof
  Cases >> simp[]
QED

(* MEM in effects_to_list ⟺ membership in the set *)
Triviality mem_effects_to_list:
  !e S. MEM e (effects_to_list S) <=> e IN S
Proof
  rpt gen_tac >>
  ONCE_REWRITE_TAC[effects_to_list_def] >>
  simp[MEM_FILTER, effect_mem_all]
QED

(* FOLDL over write effects preserves FLOOKUP at keys outside the update set *)
Triviality foldl_write_preserves_lw:
  !weffs et inst e. ~MEM e weffs ==>
    FLOOKUP (FOLDL (\acc weff.
       <| et_last_write := acc.et_last_write |+ (weff, inst);
          et_all_reads := acc.et_all_reads |+ (weff, []) |>)
      et weffs).et_last_write e = FLOOKUP et.et_last_write e
Proof
  Induct >> simp[FOLDL] >> rpt strip_tac >> fs[] >>
  first_x_assum (qspecl_then
    [`<| et_last_write := et.et_last_write |+ (h, inst);
         et_all_reads := et.et_all_reads |+ (h, []) |>`,
     `inst`, `e`] mp_tac) >> simp[FLOOKUP_UPDATE]
QED

Triviality foldl_write_preserves_ar:
  !weffs et inst e. ~MEM e weffs ==>
    FLOOKUP (FOLDL (\acc weff.
       <| et_last_write := acc.et_last_write |+ (weff, inst);
          et_all_reads := acc.et_all_reads |+ (weff, []) |>)
      et weffs).et_all_reads e = FLOOKUP et.et_all_reads e
Proof
  Induct >> simp[FOLDL] >> rpt strip_tac >> fs[] >>
  first_x_assum (qspecl_then
    [`<| et_last_write := et.et_last_write |+ (h, inst);
         et_all_reads := et.et_all_reads |+ (h, []) |>`,
     `inst`, `e`] mp_tac) >> simp[FLOOKUP_UPDATE]
QED

(* FOLDL over read effects: preserves et_last_write entirely *)
Triviality foldl_read_preserves_lw:
  !reffs et inst.
    (FOLDL (\acc reff.
       acc with et_all_reads :=
         acc.et_all_reads |+ (reff, et_get_reads acc reff ++ [inst]))
      et reffs).et_last_write = et.et_last_write
Proof
  Induct >> simp[FOLDL] >> rpt gen_tac >>
  first_x_assum (qspecl_then
    [`et with et_all_reads :=
        et.et_all_reads |+ (h, et_get_reads et h ++ [inst])`, `inst`] mp_tac) >>
  simp[]
QED

(* FOLDL over read effects: preserves FLOOKUP et_all_reads at keys outside *)
Triviality foldl_read_preserves_ar:
  !reffs et inst e. ~MEM e reffs ==>
    FLOOKUP (FOLDL (\acc reff.
       acc with et_all_reads :=
         acc.et_all_reads |+ (reff, et_get_reads acc reff ++ [inst]))
      et reffs).et_all_reads e = FLOOKUP et.et_all_reads e
Proof
  Induct >> simp[FOLDL] >> rpt strip_tac >> fs[] >>
  first_x_assum (qspecl_then
    [`et with et_all_reads :=
        et.et_all_reads |+ (h, et_get_reads et h ++ [inst])`,
     `inst`, `e`] mp_tac) >> simp[FLOOKUP_UPDATE]
QED

(* Main locality lemma: compute_effect_deps preserves et keys outside
   the instruction's write_effects ∪ read_effects *)
Triviality compute_effect_deps_preserves_key:
  !et inst e.
    e NOTIN write_effects inst.inst_opcode /\
    e NOTIN read_effects inst.inst_opcode ==>
    FLOOKUP (SND (compute_effect_deps et inst)).et_last_write e =
      FLOOKUP et.et_last_write e /\
    FLOOKUP (SND (compute_effect_deps et inst)).et_all_reads e =
      FLOOKUP et.et_all_reads e
Proof
  rpt strip_tac >>
  simp[compute_effect_deps_def, LET_THM] >>
  `~MEM e (effects_to_list (write_effects inst.inst_opcode))`
    by simp[mem_effects_to_list] >>
  `~MEM e (effects_to_list (read_effects inst.inst_opcode))`
    by simp[mem_effects_to_list] >>
  simp[foldl_read_preserves_lw, foldl_read_preserves_ar,
       foldl_write_preserves_lw, foldl_write_preserves_ar]
QED

(* Converse of preserves_key: compute_effect_deps depends only on
   effect keys of the instruction *)
(* Helper: write FOLDL preserves FLOOKUP agreement at all keys *)
Triviality foldl_write_agree:
  !wl et1 et2 inst.
    (!e. FLOOKUP et1.et_last_write e = FLOOKUP et2.et_last_write e /\
         FLOOKUP et1.et_all_reads e = FLOOKUP et2.et_all_reads e) ==>
    (!e.
      FLOOKUP (FOLDL (\acc weff.
         <| et_last_write := acc.et_last_write |+ (weff, inst);
            et_all_reads := acc.et_all_reads |+ (weff, []) |>) et1 wl).et_last_write e =
      FLOOKUP (FOLDL (\acc weff.
         <| et_last_write := acc.et_last_write |+ (weff, inst);
            et_all_reads := acc.et_all_reads |+ (weff, []) |>) et2 wl).et_last_write e) /\
    (!e.
      FLOOKUP (FOLDL (\acc weff.
         <| et_last_write := acc.et_last_write |+ (weff, inst);
            et_all_reads := acc.et_all_reads |+ (weff, []) |>) et1 wl).et_all_reads e =
      FLOOKUP (FOLDL (\acc weff.
         <| et_last_write := acc.et_last_write |+ (weff, inst);
            et_all_reads := acc.et_all_reads |+ (weff, []) |>) et2 wl).et_all_reads e)
Proof
  Induct >> simp[FOLDL] >> rpt strip_tac >> (
    first_x_assum (qspecl_then [
      `<| et_last_write := et1.et_last_write |+ (h, inst);
          et_all_reads := et1.et_all_reads |+ (h, []) |>`,
      `<| et_last_write := et2.et_last_write |+ (h, inst);
          et_all_reads := et2.et_all_reads |+ (h, []) |>`,
      `inst`] mp_tac) >>
    simp[] >> (impl_tac >- (gen_tac >> simp[FLOOKUP_UPDATE] >> rw[] >> simp[])) >>
    simp[])
QED

(* Helper: read FOLDL agrees when bases agree *)
Triviality foldl_read_agree:
  !rl et1 et2 inst.
    (!e. FLOOKUP et1.et_last_write e = FLOOKUP et2.et_last_write e) /\
    (!e. FLOOKUP et1.et_all_reads e = FLOOKUP et2.et_all_reads e) ==>
    FOLDL (\acc reff. acc with et_all_reads :=
      acc.et_all_reads |+ (reff, (case FLOOKUP acc.et_all_reads reff of
        NONE => [] | SOME rs => rs) ++ [inst])) et1 rl =
    FOLDL (\acc reff. acc with et_all_reads :=
      acc.et_all_reads |+ (reff, (case FLOOKUP acc.et_all_reads reff of
        NONE => [] | SOME rs => rs) ++ [inst])) et2 rl
Proof
  Induct >> rpt strip_tac
  >- (simp[FOLDL, effect_track_component_equality, FLOOKUP_EXT, FUN_EQ_THM])
  >- (
    simp[FOLDL] >> first_x_assum irule >> conj_tac
    >- (gen_tac >> simp[foldl_read_preserves_lw])
    >- (gen_tac >> simp[FLOOKUP_UPDATE] >> rw[] >> simp[]))
QED

Triviality compute_effect_deps_locality:
  !et1 et2 inst.
    (!e. FLOOKUP et1.et_last_write e = FLOOKUP et2.et_last_write e /\
         FLOOKUP et1.et_all_reads e = FLOOKUP et2.et_all_reads e) ==>
    compute_effect_deps et1 inst = compute_effect_deps et2 inst
Proof
  rpt strip_tac >>
  simp[compute_effect_deps_def, LET_THM, et_get_reads_def] >>
  irule foldl_read_agree >>
  mp_tac (Q.SPECL [`effects_to_list (write_effects inst.inst_opcode)`,
                    `et1`, `et2`, `inst`] foldl_write_agree) >>
  simp[]
QED

(* ================================================================
   build_eda: tracking state depends only on effect-ful subsequence
   ================================================================ *)

(* Predicate: instruction has non-empty effects *)
Definition has_effects_def:
  has_effects i <=> write_effects i.inst_opcode <> {} \/
                    read_effects i.inst_opcode <> {}
End

(* Define the FOLDL step function used in build_eda *)
Definition eda_fold_step_def:
  eda_fold_step (acc_map, et) inst =
    let (deps, et') = compute_effect_deps et inst in
    (acc_map |+ (inst.inst_id, deps), et')
End

(* The SND of eda_fold_step doesn't depend on the map accumulator *)
Triviality eda_fold_step_snd:
  !acc et inst. SND (eda_fold_step (acc, et) inst) = SND (compute_effect_deps et inst)
Proof
  rpt gen_tac >> simp[eda_fold_step_def, LET_THM] >>
  Cases_on `compute_effect_deps et inst` >> simp[]
QED

(* Corollary: SND of FOLDL doesn't depend on the map accumulator *)
Triviality eda_foldl_snd_acc_irrel:
  !insts acc1 acc2 et.
    SND (FOLDL eda_fold_step (acc1, et) insts) =
    SND (FOLDL eda_fold_step (acc2, et) insts)
Proof
  Induct >> simp[FOLDL] >>
  rpt gen_tac >>
  `SND (eda_fold_step (acc1,et) h) = SND (eda_fold_step (acc2,et) h)` by
    simp[eda_fold_step_snd] >>
  Cases_on `eda_fold_step (acc1,et) h` >>
  Cases_on `eda_fold_step (acc2,et) h` >>
  fs[]
QED

(* The tracking state (SND of fold) is unchanged by effect-free instructions,
   and the map entry for that instruction is []. *)
Triviality eda_fold_eff_free_snd:
  !insts acc et.
    EVERY ($~ o has_effects) insts ==>
    SND (FOLDL eda_fold_step (acc, et) insts) = et
Proof
  Induct >> simp[FOLDL, eda_fold_step_def, LET_THM] >>
  rpt strip_tac >> fs[has_effects_def] >>
  imp_res_tac compute_effect_deps_eff_free >> simp[]
QED

(* Interleaving effect-free instructions preserves the tracking state
   and produces the same deps for effect-ful instructions.

   Key property: if we partition the instruction list into effect-ful
   and effect-free, the fold's tracking state trajectory depends only
   on the effect-ful subsequence.

   We prove: for any instruction list, the SND of the fold equals
   the SND of the fold over just the effect-ful instructions. *)
Triviality eda_fold_snd_filter:
  !insts acc et.
    SND (FOLDL eda_fold_step (acc, et) insts) =
    SND (FOLDL eda_fold_step (acc, et)
      (FILTER has_effects insts))
Proof
  Induct >- simp[] >>
  rpt gen_tac >>
  ONCE_REWRITE_TAC[rich_listTheory.FOLDL] >>
  ONCE_REWRITE_TAC[FILTER] >>
  BETA_TAC >>
  Cases_on `has_effects h` >> fs[has_effects_def] >| [
    (* h has effects — IH applies directly after splitting the pair *)
    Cases_on `eda_fold_step (acc,et) h` >> simp[],
    (* h is effect-free — eda_fold_step changes only acc, not et *)
    imp_res_tac compute_effect_deps_eff_free >>
    simp[eda_fold_step_def, LET_THM] >>
    metis_tac[eda_foldl_snd_acc_irrel]
  ]
QED

(* ================================================================
   Per-key tracking state factorization
   ================================================================ *)

(* Deps-only locality: FST depends only on effect keys *)
Triviality compute_effect_deps_fst_locality:
  !et1 et2 inst.
    (!e. e IN write_effects inst.inst_opcode \/
         e IN read_effects inst.inst_opcode ==>
      FLOOKUP et1.et_last_write e = FLOOKUP et2.et_last_write e /\
      FLOOKUP et1.et_all_reads e = FLOOKUP et2.et_all_reads e) ==>
    FST (compute_effect_deps et1 inst) = FST (compute_effect_deps et2 inst)
Proof
  rpt strip_tac >>
  `(!e. MEM e (effects_to_list (write_effects inst.inst_opcode)) ==>
    FLOOKUP et1.et_last_write e = FLOOKUP et2.et_last_write e /\
    FLOOKUP et1.et_all_reads e = FLOOKUP et2.et_all_reads e) /\
   (!e. MEM e (effects_to_list (read_effects inst.inst_opcode)) ==>
    FLOOKUP et1.et_last_write e = FLOOKUP et2.et_last_write e /\
    FLOOKUP et1.et_all_reads e = FLOOKUP et2.et_all_reads e)` by (
    conj_tac >> gen_tac >> strip_tac >> first_x_assum match_mp_tac >>
    pop_assum mp_tac >> ONCE_REWRITE_TAC[effects_to_list_def] >>
    simp[MEM_FILTER]) >>
  simp[compute_effect_deps_def, LET_THM, et_get_reads_def] >>
  AP_TERM_TAC >>
  `MAP (\weff.
      (case FLOOKUP et1.et_all_reads weff of NONE => [] | SOME rs => rs) ++
      case FLOOKUP et1.et_last_write weff of NONE => [] | SOME w => [w])
    (effects_to_list (write_effects inst.inst_opcode)) =
   MAP (\weff.
      (case FLOOKUP et2.et_all_reads weff of NONE => [] | SOME rs => rs) ++
      case FLOOKUP et2.et_last_write weff of NONE => [] | SOME w => [w])
    (effects_to_list (write_effects inst.inst_opcode))` by (
    irule MAP_CONG >> simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
  `MAP (\reff. case FLOOKUP et1.et_last_write reff of
      NONE => NONE | SOME writer =>
        if writer.inst_id <> inst.inst_id then SOME writer else NONE)
    (effects_to_list (read_effects inst.inst_opcode)) =
   MAP (\reff. case FLOOKUP et2.et_last_write reff of
      NONE => NONE | SOME writer =>
        if writer.inst_id <> inst.inst_id then SOME writer else NONE)
    (effects_to_list (read_effects inst.inst_opcode))` by (
    irule MAP_CONG >> simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
  simp[]
QED

(* Per-key write FOLDL: at MEM key, result is SOME inst / SOME [] *)
Triviality foldl_write_at_mem_lw:
  !wl et inst e. MEM e wl ==>
    FLOOKUP (FOLDL (\acc weff.
       <| et_last_write := acc.et_last_write |+ (weff, inst);
          et_all_reads := acc.et_all_reads |+ (weff, []) |>) et wl).et_last_write e =
    SOME inst
Proof
  Induct >> simp[FOLDL] >> rpt strip_tac >> gvs[] >>
  Cases_on `MEM e wl`
  >- (first_x_assum irule >> simp[])
  >- simp[foldl_write_preserves_lw, FLOOKUP_UPDATE]
QED

Triviality foldl_write_at_mem_ar:
  !wl et inst e. MEM e wl ==>
    FLOOKUP (FOLDL (\acc weff.
       <| et_last_write := acc.et_last_write |+ (weff, inst);
          et_all_reads := acc.et_all_reads |+ (weff, []) |>) et wl).et_all_reads e =
    SOME []
Proof
  Induct >> simp[FOLDL] >> rpt strip_tac >> gvs[] >>
  Cases_on `MEM e wl`
  >- (first_x_assum irule >> simp[])
  >- simp[foldl_write_preserves_ar, FLOOKUP_UPDATE]
QED


(* ================================================================
   build_eda agreement: same effect-ful subsequence => same result
   ================================================================ *)



(* Effect-free instructions add (id, []) and don't change tracking state *)
Triviality eda_fold_step_eff_free:
  !acc et inst.
    ~has_effects inst ==>
    eda_fold_step (acc, et) inst = (acc |+ (inst.inst_id, []), et)
Proof
  rpt strip_tac >>
  fs[has_effects_def, eda_fold_step_def, LET_THM] >>
  imp_res_tac compute_effect_deps_eff_free >> simp[]
QED

(* FOLDL over effect-free instructions: each adds (id, []) to the map,
   tracking state unchanged *)
Triviality eda_foldl_eff_free:
  !insts acc et.
    EVERY (\i. ~has_effects i) insts ==>
    FOLDL eda_fold_step (acc, et) insts =
    (FOLDL (\m i. m |+ (i.inst_id, [])) acc insts, et)
Proof
  Induct >> simp[FOLDL] >>
  rpt strip_tac >>
  `eda_fold_step (acc, et) h = (acc |+ (h.inst_id, []), et)` by
    metis_tac[eda_fold_step_eff_free] >>
  simp[]
QED

(* Key lemma: if effect-free inst_id doesn't appear in the effect-ful
   subsequence, adding (id,[]) before the fold = adding after *)
Triviality eda_foldl_fst_acc_update:
  !insts acc et k.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    ~MEM k (MAP (\i. i.inst_id) insts) ==>
    FST (FOLDL eda_fold_step (acc |+ (k, ([] : instruction list)), et) insts) =
    FST (FOLDL eda_fold_step (acc, et) insts) |+ (k, [])
Proof
  Induct >- simp[FOLDL] >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC[FOLDL] >>
  simp[eda_fold_step_def, LET_THM] >>
  Cases_on `compute_effect_deps et h` >>
  rename1 `_ = (d, et2)` >> simp[] >>
  `k <> h.inst_id` by (fs[MAP, MEM]) >>
  `~MEM k (MAP (\i. i.inst_id) insts)` by (fs[MAP, MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) insts)` by (fs[MAP, ALL_DISTINCT]) >>
  `(acc |+ (k, ([] : instruction list)) |+ (h.inst_id, d)) =
   (acc |+ (h.inst_id, d) |+ (k, []))` by
    simp[FUPDATE_COMMUTES] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  first_x_assum (qspecl_then [`acc |+ (h.inst_id, d)`, `et2`, `k`] mp_tac) >>
  simp[]
QED

Theorem all_distinct_map_filter:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct_on `l` >> simp[FILTER] >>
  rpt strip_tac >> Cases_on `P h` >> simp[MAP] >> fs[MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

(* Decomposition: FOLDL over full list = FOLDL over effect-ful + empty entries.
   Requires ALL_DISTINCT so effect-free updates commute past effect-ful ones. *)
Triviality eda_foldl_fst_decompose:
  !insts acc et.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    FST (FOLDL eda_fold_step (acc, et) insts) =
    FOLDL (\m id. m |+ (id, ([] : instruction list)))
      (FST (FOLDL eda_fold_step (acc, et) (FILTER has_effects insts)))
      (MAP (\i. i.inst_id) (FILTER ($~ o has_effects) insts))
Proof
  Induct >- simp[FOLDL] >>
  rpt strip_tac >>
  fs[ALL_DISTINCT, MAP] >>
  Cases_on `has_effects h` >|
  [(* h has effects: it stays in both FILTERs *)
   simp[FILTER] >>
   ONCE_REWRITE_TAC[FOLDL] >>
   Cases_on `eda_fold_step (acc, et) h` >>
   rename1 `_ = (acc2, et2)` >> simp[] >>
   (* IH: the fold over tl decomposes *)
   first_x_assum (qspecl_then [`acc2`, `et2`] mp_tac) >> simp[],
   (* h is effect-free: adds (h.inst_id, []) to map, tracking state unchanged *)
   simp[FILTER] >>
   `eda_fold_step (acc, et) h = (acc |+ (h.inst_id, ([] : instruction list)), et)` by
     metis_tac[eda_fold_step_eff_free] >>
   ONCE_REWRITE_TAC[FOLDL] >> simp[] >>
   (* Apply IH to the tail with updated accumulator *)
   first_x_assum (qspecl_then [`acc |+ (h.inst_id, [])`, `et`] mp_tac) >>
   simp[] >> strip_tac >>
   (* Need: FST(FOLDL ... (acc |+ (h.inst_id,[]), et) (FILTER has_effects insts))
            = FST(FOLDL ... (acc, et) (FILTER has_effects insts)) |+ (h.inst_id, []) *)
   `~MEM h.inst_id (MAP (\i. i.inst_id) (FILTER has_effects insts))` by (
     CCONTR_TAC >> fs[] >>
     `MEM h.inst_id (MAP (\i. i.inst_id) insts)` suffices_by fs[] >>
     fs[MEM_MAP, MEM_FILTER] >> metis_tac[]
   ) >>
   `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER has_effects insts))` by
     metis_tac[all_distinct_map_filter] >>
   drule_all eda_foldl_fst_acc_update >> strip_tac >>
   simp[] >>
   (* RHS: FOLDL f base (h.inst_id :: rest) = FOLDL f (base |+ (h.inst_id, [])) rest *)
   ONCE_REWRITE_TAC[FOLDL] >> simp[]]
QED

(* ===== FUPDATE_LIST order independence ===== *)

(* FOLDL of constant-value updates = FUPDATE_LIST *)
Triviality foldl_fupdate_const_to_list:
  !ids base (v : 'b).
    FOLDL (\m id. m |+ (id, v)) base ids =
    base |++ MAP (\id. (id, v)) ids
Proof
  Induct >> simp[FOLDL, FUPDATE_LIST_THM]
QED

(* FUPDATE_LIST with constant value and ALL_DISTINCT keys:
   lookup is determined by set membership *)
Triviality fupdate_list_const_lookup:
  !ids (base : 'a |-> 'b) v k.
    ALL_DISTINCT ids /\ MEM k ids ==>
    (base |++ MAP (\id. (id, v)) ids) ' k = v
Proof
  Induct >> simp[FUPDATE_LIST_THM] >>
  rpt strip_tac >> gvs[ALL_DISTINCT] >>
  `~MEM h (MAP FST (MAP (\id. (id,v)) ids))` by
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
  simp[FUPDATE_LIST_APPLY_NOT_MEM, FAPPLY_FUPDATE_THM]
QED

(* Two ALL_DISTINCT lists with same set give same FUPDATE_LIST result
   when using constant values *)
Triviality fupdate_list_const_set_eq:
  !ids1 ids2 (base : 'a |-> 'b) v.
    ALL_DISTINCT ids1 /\ ALL_DISTINCT ids2 /\
    set ids1 = set ids2 ==>
    base |++ MAP (\id. (id, v)) ids1 =
    base |++ MAP (\id. (id, v)) ids2
Proof
  rpt strip_tac >>
  `!x. MEM x ids1 <=> MEM x ids2` by fs[EXTENSION] >>
  rw[fmap_EXT]
  >- simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, EXTENSION]
  >- (
    rpt strip_tac >>
    Cases_on `MEM x ids1`
    >- (`MEM x ids2` by metis_tac[] >> simp[fupdate_list_const_lookup])
    >- (
      `~MEM x ids2` by metis_tac[] >>
      `~MEM x (MAP FST (MAP (\id. (id,v)) ids1))` by
        simp[MAP_MAP_o, combinTheory.o_DEF] >>
      `~MEM x (MAP FST (MAP (\id. (id,v)) ids2))` by
        simp[MAP_MAP_o, combinTheory.o_DEF] >>
      simp[FUPDATE_LIST_APPLY_NOT_MEM]
    )
  )
QED

(* FOLDL of constant-value updates with same set = same result *)
Triviality foldl_fupdate_const_set_eq:
  !ids1 ids2 (base : 'a |-> 'b) v.
    ALL_DISTINCT ids1 /\ ALL_DISTINCT ids2 /\
    set ids1 = set ids2 ==>
    FOLDL (\m id. m |+ (id, v)) base ids1 =
    FOLDL (\m id. m |+ (id, v)) base ids2
Proof
  metis_tac[foldl_fupdate_const_to_list, fupdate_list_const_set_eq]
QED

(* ===== build_eda agreement ===== *)

(* Membership in MAP f (FILTER (~P) L): need injectivity for reverse direction *)
Triviality mem_map_filter_compl:
  !f (P : 'a -> bool) L x.
    ALL_DISTINCT (MAP f L) ==>
    (MEM x (MAP f (FILTER ($~ o P) L)) <=>
     MEM x (MAP f L) /\ ~MEM x (MAP f (FILTER P L)))
Proof
  gen_tac >> gen_tac >> Induct >> simp[FILTER, MAP] >>
  rpt strip_tac >> fs[ALL_DISTINCT] >>
  Cases_on `P h` >> simp[FILTER, MAP] >> eq_tac >> rpt strip_tac >> gvs[] >>
  `MEM (f h) (MAP f L)` suffices_by fs[] >>
  fs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* Main: two lists with same effect-ful subsequence and same id set
   produce the same eda fold result *)
Triviality build_eda_agree:
  !L1 L2.
    ALL_DISTINCT (MAP (\i. i.inst_id) L1) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) L2) /\
    FILTER has_effects L1 = FILTER has_effects L2 /\
    set (MAP (\i. i.inst_id) L1) = set (MAP (\i. i.inst_id) L2) ==>
    FST (FOLDL eda_fold_step (FEMPTY, empty_effect_track) L1) =
    FST (FOLDL eda_fold_step (FEMPTY, empty_effect_track) L2)
Proof
  rpt strip_tac >>
  (* Decompose both sides via eda_foldl_fst_decompose *)
  `FST (FOLDL eda_fold_step (FEMPTY, empty_effect_track) L1) =
   FOLDL (\m id. m |+ (id, ([] : instruction list)))
     (FST (FOLDL eda_fold_step (FEMPTY, empty_effect_track)
       (FILTER has_effects L1)))
     (MAP (\i. i.inst_id) (FILTER ($~ o has_effects) L1))` by
    metis_tac[eda_foldl_fst_decompose] >>
  `FST (FOLDL eda_fold_step (FEMPTY, empty_effect_track) L2) =
   FOLDL (\m id. m |+ (id, ([] : instruction list)))
     (FST (FOLDL eda_fold_step (FEMPTY, empty_effect_track)
       (FILTER has_effects L2)))
     (MAP (\i. i.inst_id) (FILTER ($~ o has_effects) L2))` by
    metis_tac[eda_foldl_fst_decompose] >>
  (* Effect-ful filters are equal, so bases match *)
  simp[] >>
  (* Effect-free id sets are equal — via membership characterization *)
  `set (MAP (\i. i.inst_id) (FILTER ($~ o has_effects) L1)) =
   set (MAP (\i. i.inst_id) (FILTER ($~ o has_effects) L2))` by (
    simp[EXTENSION] >> gen_tac >>
    simp[mem_map_filter_compl] >> fs[EXTENSION]
  ) >>
  (* Both id lists are ALL_DISTINCT; apply order-independence *)
  metis_tac[all_distinct_map_filter, foldl_fupdate_const_set_eq]
QED

(* ===== build_full_eda pseudo-stripping ===== *)

(* build_full_eda only depends on the non-pseudo sub-list.
   This lets us strip pseudos and reason about the non-pseudo core. *)

(* Helper: FILTER (¬is_pseudo) distributes over phis ++ nonpseudos *)
Triviality filter_nonpseudo_append_pseudo:
  !phis L.
    EVERY (\i. is_pseudo i.inst_opcode) phis /\
    EVERY (\i. ~is_pseudo i.inst_opcode) L ==>
    FILTER (\i. ~is_pseudo i.inst_opcode) (phis ++ L) = L
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  simp[FILTER_EQ_ID]
QED

(* build_full_eda depends only on the non-pseudo sub-list.
   Proof approach: build_full_eda is a composition of functions that each
   begin with FILTER (¬is_pseudo) block_insts. Showing the filter result
   is the same suffices. Use AP_TERM / CONG reasoning rather than expanding. *)
Theorem build_full_eda_pseudo_strip:
  !phis L.
    EVERY (\i. is_pseudo i.inst_opcode) phis /\
    EVERY (\i. ~is_pseudo i.inst_opcode) L ==>
    build_full_eda (phis ++ L) = build_full_eda L
Proof
  rpt strip_tac >>
  drule_all filter_nonpseudo_append_pseudo >> strip_tac >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) L = L` by
    simp[FILTER_EQ_ID] >>
  (* build_full_eda = add_alloca_deps bi (add_barrier_deps bi (add_abort_deps bi (build_eda bi)))
     Each sub-function uses bi only through FILTER (¬is_pseudo) bi.
     Since FILTER (¬is_pseudo) (phis ++ L) = L = FILTER (¬is_pseudo) L,
     every sub-function receives the same filtered list. *)
  `build_eda (phis ++ L) = build_eda L` by
    simp[build_eda_def, LET_THM] >>
  `add_abort_deps (phis ++ L) (build_eda L) =
   add_abort_deps L (build_eda L)` by
    simp[add_abort_deps_def, add_chain_deps_def, LET_THM] >>
  `add_barrier_deps (phis ++ L) (add_abort_deps L (build_eda L)) =
   add_barrier_deps L (add_abort_deps L (build_eda L))` by
    simp[add_barrier_deps_def, add_deps_on_barrier_def,
         add_deps_from_barrier_def, LET_THM] >>
  `add_alloca_deps (phis ++ L)
     (add_barrier_deps L (add_abort_deps L (build_eda L))) =
   add_alloca_deps L
     (add_barrier_deps L (add_abort_deps L (build_eda L)))` by
    simp[add_alloca_deps_def, add_chain_deps_def, LET_THM] >>
  simp[build_full_eda_def, LET_THM]
QED
