Theory evalCompilerBytecodeSimplifyCfgProbe
Ancestors evalCompilerBytecodeStageProbe

open HolKernel Parse boolLib bossLib

Theorem imported_first_simplify_cfg_operation_unfold:
  !fn.
    simplify_cfg_fn_with_labels fn =
      simplify_cfg_iter_with_labels (LENGTH fn.fn_blocks) fn
Proof
  ACCEPT_TAC
    evalCompilerBytecodeStageProbeTheory.first_simplify_cfg_operation_unfold
QED


Theorem first_simplify_cfg_operand_block_count:
  LENGTH first_simplify_cfg_operand.fn_blocks = 3
Proof
  EVAL_TAC
QED

Theorem first_simplify_cfg_operand_entry:
  fn_entry_label first_simplify_cfg_operand = SOME "__entry"
Proof
  EVAL_TAC
QED

(* Evaluate reachability one retained candidate at a time.  Keeping these
   conversions separate prevents the recursive closure computation from being
   duplicated while FILTER is traversed. *)
val first_simplify_cfg_blocks_th =
  computeLib.EVAL_CONV ``first_simplify_cfg_operand.fn_blocks``
val first_simplify_cfg_blocks =
  fst (listSyntax.dest_list (rhs (concl first_simplify_cfg_blocks_th)))

fun eval_first_simplify_cfg_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val reachable_tm =
      list_mk_comb (``reachable``, [``first_simplify_cfg_operand``, label_tm])
  in
    computeLib.EVAL_CONV reachable_tm
  end

val first_simplify_cfg_reachable_ths =
  map eval_first_simplify_cfg_reachable first_simplify_cfg_blocks

val first_remove_unreachable_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     first_simplify_cfg_operand_entry ::
     first_simplify_cfg_blocks_th :: first_simplify_cfg_reachable_ths)
    ``remove_unreachable_blocks first_simplify_cfg_operand``

Theorem exact_first_remove_unreachable:
  ^(concl first_remove_unreachable_th)
Proof
  ACCEPT_TAC first_remove_unreachable_th
QED
val first_removed_tm = rhs (concl first_remove_unreachable_th)
Definition first_simplify_cfg_removed_def:
  first_simplify_cfg_removed = ^first_removed_tm
End

Theorem exact_first_remove_unreachable_named:
  remove_unreachable_blocks first_simplify_cfg_operand =
    first_simplify_cfg_removed
Proof
  simp[first_simplify_cfg_removed_def, exact_first_remove_unreachable]
QED

Theorem first_simplify_cfg_dispatch_edge:
  fn_succ first_simplify_cfg_operand "__entry" "@dispatch_1"
Proof
  simp[cfgTransformTheory.fn_succ_def,
       venomInstTheory.lookup_block_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, first_simplify_cfg_operand_def]
QED

Theorem first_simplify_cfg_fallback_edge:
  fn_succ first_simplify_cfg_operand "__entry" "@fallback_0"
Proof
  simp[cfgTransformTheory.fn_succ_def,
       venomInstTheory.lookup_block_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, first_simplify_cfg_operand_def]
QED

val first_literal_edge_ths =
  map (REWRITE_RULE [first_simplify_cfg_operand_def])
    [first_simplify_cfg_dispatch_edge, first_simplify_cfg_fallback_edge]
val first_removed_normal_th =
  SIMP_CONV (srw_ss ()) first_literal_edge_ths first_removed_tm
val first_removed_eq_operand_th =
  SIMP_RULE (srw_ss ()) [GSYM first_simplify_cfg_operand_def,
    GSYM first_simplify_cfg_blocks_th]
    (TRANS first_simplify_cfg_removed_def first_removed_normal_th)

Theorem first_simplify_cfg_removed_eq_operand:
  first_simplify_cfg_removed = first_simplify_cfg_operand
Proof
  once_rewrite_tac [first_removed_eq_operand_th] >>
  simp[venomInstTheory.ir_function_component_equality]
QED

val first_removed_blocks_eq_operand_th =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (AP_TERM ``\fn : ir_function. fn.fn_blocks``
      first_simplify_cfg_removed_eq_operand)
val first_removed_blocks_th =
  TRANS first_removed_blocks_eq_operand_th first_simplify_cfg_blocks_th
val first_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl first_removed_blocks_th)))

Theorem first_simplify_cfg_removed_blocks:
  ^(concl first_removed_blocks_th)
Proof
  ACCEPT_TAC first_removed_blocks_th
QED

fun eval_first_phi_repair bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val preds_tm =
      list_mk_comb (``pred_labels``, [``first_simplify_cfg_removed``, label_tm])
    val preds_th =
      SIMP_CONV (srw_ss ())
        [first_simplify_cfg_removed_eq_operand,
         first_simplify_cfg_operand_def,
         cfgTransformTheory.pred_labels_def,
         cfgTransformTheory.block_preds_def,
         venomInstTheory.bb_succs_def,
         venomInstTheory.get_successors_def,
         venomInstTheory.is_terminator_def,
         venomStateTheory.get_label_def]
        preds_tm
    val repair_tm =
      list_mk_comb (``fix_phis_in_block``, [rhs (concl preds_th), bb])
    val repair_th = computeLib.EVAL_CONV repair_tm
  in
    [preds_th, repair_th]
  end

val first_phi_repair_ths =
  List.concat (map eval_first_phi_repair first_removed_blocks)
val first_fix_all_phis_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.fix_all_phis_def ::
     first_simplify_cfg_removed_blocks :: first_phi_repair_ths)
    ``fix_all_phis first_simplify_cfg_removed``

val first_phi_fixed_tm = rhs (concl first_fix_all_phis_th)
Definition first_simplify_cfg_phi_fixed_def:
  first_simplify_cfg_phi_fixed = ^first_phi_fixed_tm
End

Theorem exact_first_fix_all_phis:
  fix_all_phis first_simplify_cfg_removed = first_simplify_cfg_phi_fixed
Proof
  simp[first_simplify_cfg_phi_fixed_def] >>
  ACCEPT_TAC first_fix_all_phis_th
QED

val first_phi_fixed_blocks_th =
  computeLib.EVAL_CONV ``first_simplify_cfg_phi_fixed.fn_blocks``
val first_phi_fixed_blocks =
  fst (listSyntax.dest_list (rhs (concl first_phi_fixed_blocks_th)))
val _ =
  if length first_phi_fixed_blocks = 3 then ()
  else raise Fail "stable PHI fix changed the fixture block count"
fun eval_last_opcode bb = computeLib.EVAL_CONV
  ``(LAST (^bb).bb_instructions).inst_opcode``
val first_phi_fixed_last_opcodes = map eval_last_opcode first_phi_fixed_blocks
val _ =
  if ListPair.allEq (fn (x,y) => aconv x y)
       (map (rhs o concl) first_phi_fixed_last_opcodes,
        [``JNZ``, ``JMP``, ``REVERT``])
  then ()
  else raise Fail "stable PHI fix did not preserve fixture terminators at LAST"

Theorem exact_first_fix_all_phis_last_opcodes:
  ^(concl (List.nth (first_phi_fixed_last_opcodes, 0))) /\
  ^(concl (List.nth (first_phi_fixed_last_opcodes, 1))) /\
  ^(concl (List.nth (first_phi_fixed_last_opcodes, 2)))
Proof
  ACCEPT_TAC (LIST_CONJ first_phi_fixed_last_opcodes)
QED

val first_entry_bb_tm = List.nth (first_phi_fixed_blocks, 0)
val first_dispatch_bb_tm = List.nth (first_phi_fixed_blocks, 1)
val first_fallback_bb_tm = List.nth (first_phi_fixed_blocks, 2)

Definition first_simplify_cfg_entry_bb_def:
  first_simplify_cfg_entry_bb = ^first_entry_bb_tm
End

Definition first_simplify_cfg_dispatch_bb_def:
  first_simplify_cfg_dispatch_bb = ^first_dispatch_bb_tm
End

Definition first_simplify_cfg_fallback_bb_def:
  first_simplify_cfg_fallback_bb = ^first_fallback_bb_tm
End

val first_entry_lookup_th = computeLib.EVAL_CONV
  ``lookup_block "__entry" first_simplify_cfg_phi_fixed.fn_blocks``
val first_dispatch_lookup_th = computeLib.EVAL_CONV
  ``lookup_block "@dispatch_1" first_simplify_cfg_phi_fixed.fn_blocks``
val first_fallback_lookup_th = computeLib.EVAL_CONV
  ``lookup_block "@fallback_0" first_simplify_cfg_phi_fixed.fn_blocks``
val first_entry_succs_th = computeLib.EVAL_CONV
  ``bb_succs first_simplify_cfg_entry_bb``
val first_dispatch_succs_th = computeLib.EVAL_CONV
  ``bb_succs first_simplify_cfg_dispatch_bb``
val first_entry_succs_named_th =
  PURE_REWRITE_RULE [GSYM first_simplify_cfg_entry_bb_def]
    first_entry_succs_th
val first_fallback_succs_th = computeLib.EVAL_CONV
  ``bb_succs first_simplify_cfg_fallback_bb``
val first_fallback_preds_th = computeLib.EVAL_CONV
  ``num_preds first_simplify_cfg_phi_fixed "@fallback_0"``
val first_entry_try_bypass_th = computeLib.EVAL_CONV
  ``try_bypass first_simplify_cfg_phi_fixed [] first_simplify_cfg_entry_bb
      ["@fallback_0"; "@dispatch_1"]``
val first_dispatch_merge_fallback_th = computeLib.EVAL_CONV
  ``can_merge_blocks first_simplify_cfg_phi_fixed
      first_simplify_cfg_dispatch_bb first_simplify_cfg_fallback_bb``

Theorem exact_first_simplify_cfg_closed_decisions:
  ^(concl first_entry_lookup_th) /\
  ^(concl first_dispatch_lookup_th) /\
  ^(concl first_fallback_lookup_th) /\
  ^(concl first_entry_succs_th) /\
  ^(concl first_dispatch_succs_th) /\
  ^(concl first_fallback_succs_th) /\
  ^(concl first_fallback_preds_th) /\
  ^(concl first_entry_try_bypass_th) /\
  ^(concl first_dispatch_merge_fallback_th)
Proof
  ACCEPT_TAC (LIST_CONJ
    [first_entry_lookup_th, first_dispatch_lookup_th, first_fallback_lookup_th,
     first_entry_succs_th, first_dispatch_succs_th, first_fallback_succs_th,
     first_fallback_preds_th, first_entry_try_bypass_th,
     first_dispatch_merge_fallback_th])
QED

Theorem exact_first_entry_try_bypass:
  try_bypass first_simplify_cfg_phi_fixed [] first_simplify_cfg_entry_bb
    ["@fallback_0"; "@dispatch_1"] =
  (first_simplify_cfg_phi_fixed, [], F)
Proof
  rewrite_tac [first_entry_try_bypass_th] >>
  simp[first_simplify_cfg_phi_fixed_def,
       first_simplify_cfg_removed_eq_operand,
       first_simplify_cfg_operand_def,
       venomInstTheory.ir_function_component_equality]
QED

Theorem exact_first_entry_succs:
  bb_succs first_simplify_cfg_entry_bb =
    ["@fallback_0"; "@dispatch_1"]
Proof
  simp[first_simplify_cfg_entry_bb_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.nub_def]
QED


Theorem exact_first_collapse_fallback_fresh:
  collapse_dfs first_simplify_cfg_phi_fixed [] ["__entry"] "@fallback_0" =
    (first_simplify_cfg_phi_fixed, [], ["@fallback_0"; "__entry"])
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[first_fallback_lookup_th,
       GSYM first_simplify_cfg_fallback_bb_def,
       first_fallback_succs_th, simplifyCfgDefsTheory.try_bypass_def,
       cj 2 simplifyCfgDefsTheory.collapse_dfs_def]
QED

Theorem exact_first_collapse_fallback_visited:
  collapse_dfs first_simplify_cfg_phi_fixed []
    ["@dispatch_1"; "@fallback_0"; "__entry"] "@fallback_0" =
  (first_simplify_cfg_phi_fixed, [],
    ["@dispatch_1"; "@fallback_0"; "__entry"])
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[first_fallback_lookup_th,
       GSYM first_simplify_cfg_fallback_bb_def,
       first_fallback_succs_th, simplifyCfgDefsTheory.try_bypass_def,
       cj 2 simplifyCfgDefsTheory.collapse_dfs_def]
QED

Theorem exact_first_collapse_dispatch:
  collapse_dfs first_simplify_cfg_phi_fixed []
    ["@fallback_0"; "__entry"] "@dispatch_1" =
  (first_simplify_cfg_phi_fixed, [],
    ["@dispatch_1"; "@fallback_0"; "__entry"])
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[first_dispatch_lookup_th,
       GSYM first_simplify_cfg_dispatch_bb_def,
       first_dispatch_succs_th, first_fallback_lookup_th,
       GSYM first_simplify_cfg_fallback_bb_def,
       first_dispatch_merge_fallback_th,
       exact_first_collapse_fallback_visited]
QED

Theorem exact_first_collapse_entry_succs:
  collapse_dfs_succs first_simplify_cfg_phi_fixed [] ["__entry"]
    ["@fallback_0"; "@dispatch_1"] =
  (first_simplify_cfg_phi_fixed, [],
    ["@dispatch_1"; "@fallback_0"; "__entry"])
Proof
  pure_once_rewrite_tac [cj 3 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[exact_first_collapse_fallback_fresh] >>
  pure_once_rewrite_tac [cj 3 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[exact_first_collapse_dispatch, cj 2 simplifyCfgDefsTheory.collapse_dfs_def]
QED

val first_collapse_result_tm =
  ``(first_simplify_cfg_phi_fixed, ([] : (string # string) list),
     ["@dispatch_1"; "@fallback_0"; "__entry"])``
Definition first_simplify_cfg_collapse_result_def:
  first_simplify_cfg_collapse_result = ^first_collapse_result_tm
End

Theorem exact_first_collapse_dfs:
  collapse_dfs first_simplify_cfg_phi_fixed [] [] "__entry" =
    first_simplify_cfg_collapse_result
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[first_entry_lookup_th, GSYM first_simplify_cfg_entry_bb_def,
       exact_first_entry_succs, exact_first_entry_try_bypass,
       exact_first_collapse_entry_succs,
       first_simplify_cfg_collapse_result_def]
QED

(* The DFS result is already a closed triple.  Project it once here so the
   substitution guard and cleanup phases do not reopen collapse_dfs. *)
val (first_collapsed_fn_tm, first_collapse_tail_tm) =
  pairSyntax.dest_pair first_collapse_result_tm
val (first_collapse_label_map_tm, first_collapse_visited_tm) =
  pairSyntax.dest_pair first_collapse_tail_tm

val first_substitution_tm =
  mk_cond
    (mk_eq (first_collapse_label_map_tm,
            listSyntax.mk_list ([], listSyntax.dest_list_type
              (type_of first_collapse_label_map_tm))),
     first_collapsed_fn_tm,
     list_mk_comb (``subst_block_labels_fn``,
       [first_collapse_label_map_tm, first_collapsed_fn_tm]))
val first_substitution_th = computeLib.EVAL_CONV first_substitution_tm
val first_substituted_tm = rhs (concl first_substitution_th)

Definition first_simplify_cfg_substituted_def:
  first_simplify_cfg_substituted = ^first_substituted_tm
End

Theorem exact_first_collapse_dfs_components:
  collapse_dfs first_simplify_cfg_phi_fixed [] [] "__entry" =
    (^first_collapsed_fn_tm, ^first_collapse_label_map_tm,
     ^first_collapse_visited_tm)
Proof
  simp[exact_first_collapse_dfs, first_simplify_cfg_collapse_result_def]
QED

Theorem exact_first_substitution:
  (if ^first_collapse_label_map_tm = [] then ^first_collapsed_fn_tm
   else subst_block_labels_fn ^first_collapse_label_map_tm ^first_collapsed_fn_tm) =
  first_simplify_cfg_substituted
Proof
  simp[first_simplify_cfg_substituted_def,
       first_simplify_cfg_phi_fixed_def,
       first_simplify_cfg_removed_eq_operand,
       first_simplify_cfg_operand_def,
       venomInstTheory.ir_function_component_equality]
QED


val first_substituted_blocks_th =
  computeLib.EVAL_CONV ``first_simplify_cfg_substituted.fn_blocks``
val first_substituted_blocks =
  fst (listSyntax.dest_list (rhs (concl first_substituted_blocks_th)))

Theorem first_simplify_cfg_substituted_blocks:
  ^(concl first_substituted_blocks_th)
Proof
  ACCEPT_TAC first_substituted_blocks_th
QED

val first_substituted_entry_th =
  computeLib.EVAL_CONV ``fn_entry_label first_simplify_cfg_substituted``

Theorem first_simplify_cfg_substituted_entry:
  ^(concl first_substituted_entry_th)
Proof
  ACCEPT_TAC first_substituted_entry_th
QED

fun eval_first_substituted_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val reachable_tm =
      list_mk_comb (``reachable``,
        [``first_simplify_cfg_substituted``, rhs (concl label_th)])
  in
    computeLib.EVAL_CONV reachable_tm
  end

val first_substituted_reachable_ths =
  map eval_first_substituted_reachable first_substituted_blocks
val first_final_remove_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     first_simplify_cfg_substituted_entry ::
     first_simplify_cfg_substituted_blocks ::
     first_substituted_reachable_ths)
    ``remove_unreachable_blocks first_simplify_cfg_substituted``
val first_final_removed_tm = rhs (concl first_final_remove_th)

Definition first_simplify_cfg_final_removed_def:
  first_simplify_cfg_final_removed = ^first_final_removed_tm
End

Theorem exact_first_final_remove_unreachable:
  remove_unreachable_blocks first_simplify_cfg_substituted =
    first_simplify_cfg_final_removed
Proof
  simp[first_simplify_cfg_final_removed_def] >>
  ACCEPT_TAC first_final_remove_th
QED

Theorem first_simplify_cfg_substituted_dispatch_edge:
  fn_succ first_simplify_cfg_substituted "__entry" "@dispatch_1"
Proof
  simp[cfgTransformTheory.fn_succ_def,
       venomInstTheory.lookup_block_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, first_simplify_cfg_substituted_def,
       first_simplify_cfg_phi_fixed_def,
       first_simplify_cfg_removed_eq_operand,
       first_simplify_cfg_operand_def]
QED

Theorem first_simplify_cfg_substituted_fallback_edge:
  fn_succ first_simplify_cfg_substituted "__entry" "@fallback_0"
Proof
  simp[cfgTransformTheory.fn_succ_def,
       venomInstTheory.lookup_block_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, first_simplify_cfg_substituted_def,
       first_simplify_cfg_phi_fixed_def,
       first_simplify_cfg_removed_eq_operand,
       first_simplify_cfg_operand_def]
QED

Theorem first_simplify_cfg_substituted_entry_reachable:
  reachable first_simplify_cfg_substituted "__entry"
Proof
  simp[cfgTransformTheory.reachable_def,
       first_simplify_cfg_substituted_entry]
QED

Theorem first_simplify_cfg_substituted_dispatch_reachable:
  reachable first_simplify_cfg_substituted "@dispatch_1"
Proof
  simp[cfgTransformTheory.reachable_def,
       first_simplify_cfg_substituted_entry] >>
  metis_tac[relationTheory.RTC_SINGLE,
            first_simplify_cfg_substituted_dispatch_edge]
QED

Theorem first_simplify_cfg_substituted_fallback_reachable:
  reachable first_simplify_cfg_substituted "@fallback_0"
Proof
  simp[cfgTransformTheory.reachable_def,
       first_simplify_cfg_substituted_entry] >>
  metis_tac[relationTheory.RTC_SINGLE,
            first_simplify_cfg_substituted_fallback_edge]
QED

Theorem first_simplify_cfg_final_remove_retains_all:
  remove_unreachable_blocks first_simplify_cfg_substituted =
    first_simplify_cfg_substituted
Proof
  pure_rewrite_tac
    [simplifyCfgDefsTheory.remove_unreachable_blocks_def,
     first_simplify_cfg_substituted_entry,
     first_simplify_cfg_substituted_blocks] >>
  simp[Excl "reachable_def", Excl "fn_succ_def",
       first_simplify_cfg_substituted_entry_reachable,
       first_simplify_cfg_substituted_dispatch_reachable,
       first_simplify_cfg_substituted_fallback_reachable,
       venomInstTheory.ir_function_component_equality,
       first_simplify_cfg_substituted_blocks]
QED

Theorem first_simplify_cfg_final_removed_eq_substituted:
  first_simplify_cfg_final_removed = first_simplify_cfg_substituted
Proof
  metis_tac[exact_first_final_remove_unreachable,
            first_simplify_cfg_final_remove_retains_all]
QED

val first_final_removed_normal_eq =
  first_simplify_cfg_final_removed_eq_substituted
val first_final_removed_blocks_th =
  TRANS
    (CONV_RULE (DEPTH_CONV BETA_CONV)
      (AP_TERM ``\fn : ir_function. fn.fn_blocks``
        first_simplify_cfg_final_removed_eq_substituted))
    first_substituted_blocks_th
val first_final_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl first_final_removed_blocks_th)))

Theorem first_simplify_cfg_final_removed_blocks:
  ^(concl first_final_removed_blocks_th)
Proof
  ACCEPT_TAC first_final_removed_blocks_th
QED

fun eval_first_final_phi_repair bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val preds_tm =
      list_mk_comb (``pred_labels``,
        [``first_simplify_cfg_final_removed``, label_tm])
    val preds_th =
      SIMP_CONV (srw_ss ())
        [first_final_removed_normal_eq,
         cfgTransformTheory.pred_labels_def,
         cfgTransformTheory.block_preds_def,
         venomInstTheory.bb_succs_def,
         venomInstTheory.get_successors_def,
         venomInstTheory.is_terminator_def,
         venomStateTheory.get_label_def]
        preds_tm
    val repair_tm =
      list_mk_comb (``fix_phis_in_block``, [rhs (concl preds_th), bb])
    val repair_th = computeLib.EVAL_CONV repair_tm
  in
    [preds_th, repair_th]
  end

val first_final_phi_repair_ths =
  List.concat (map eval_first_final_phi_repair first_final_removed_blocks)
val first_final_fix_all_phis_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.fix_all_phis_def ::
     first_simplify_cfg_final_removed_blocks :: first_final_phi_repair_ths)
    ``fix_all_phis first_simplify_cfg_final_removed``
val first_round1_fn_tm = rhs (concl first_final_fix_all_phis_th)

Definition first_simplify_cfg_round1_fn_def:
  first_simplify_cfg_round1_fn = ^first_round1_fn_tm
End

Theorem exact_first_final_fix_all_phis:
  fix_all_phis first_simplify_cfg_final_removed =
    first_simplify_cfg_round1_fn
Proof
  simp[first_simplify_cfg_round1_fn_def] >>
  ACCEPT_TAC first_final_fix_all_phis_th
QED

Theorem exact_first_simplify_cfg_round_with_labels:
  simplify_cfg_round_with_labels first_simplify_cfg_operand =
    (first_simplify_cfg_round1_fn, REVERSE ^first_collapse_label_map_tm)
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_round_with_labels_def,
       first_simplify_cfg_operand_entry,
       exact_first_remove_unreachable_named,
       exact_first_fix_all_phis,
       exact_first_collapse_dfs_components,
       exact_first_substitution,
       exact_first_final_remove_unreachable,
       exact_first_final_fix_all_phis]
QED

val first_round_fixpoint_guard_th =
  computeLib.EVAL_CONV
    ``first_simplify_cfg_round1_fn.fn_blocks =
      first_simplify_cfg_operand.fn_blocks``

Theorem exact_first_round_fixpoint_guard:
  ^(concl first_round_fixpoint_guard_th)
Proof
  ACCEPT_TAC first_round_fixpoint_guard_th
QED

val _ = export_theory()
