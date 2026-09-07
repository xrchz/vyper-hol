Theory evalCompilerBytecodeSecondSimplifyCfgCollapseDecisions
Ancestors evalCompilerBytecodeSecondSimplifyCfgInitialPhi
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)
fun assert_reduced label query_head th =
  let
    val (l, r) = dest_eq (concl th)
  in
    if aconv l r then raise Fail (label ^ " produced a reflexive equation")
    else if has_head query_head r then
      raise Fail (label ^ " left its query head on the RHS")
    else assert_closed label (concl th)
  end

val operand_def =
  evalCompilerBytecodeSecondSimplifyCfgResultTheory.second_simplify_cfg_operand_def
val removed_def =
  evalCompilerBytecodeSecondSimplifyCfgInitialRemoveTheory.second_simplify_cfg_removed_def
val phi_fixed_def =
  evalCompilerBytecodeSecondSimplifyCfgInitialPhiTheory.second_simplify_cfg_phi_fixed_def
val second_literal_edge_ths =
  map (REWRITE_RULE [operand_def])
    [second_simplify_cfg_dispatch_edge, second_simplify_cfg_fallback_edge]
val second_removed_normal_th =
  SIMP_RULE (srw_ss ()) second_literal_edge_ths removed_def
val second_phi_fixed_normal_th =
  SIMP_RULE (srw_ss ())
    (second_removed_normal_th :: second_literal_edge_ths) phi_fixed_def
val second_phi_fixed_tm = rhs (concl second_phi_fixed_normal_th)
val _ = assert_closed "literal second PHI-fixed function" second_phi_fixed_tm
val second_phi_fixed_blocks_projection_th =
  computeLib.EVAL_CONV
    (mk_comb (``\fn : ir_function. fn.fn_blocks``, second_phi_fixed_tm))
val second_phi_fixed_blocks_tm =
  rhs (concl second_phi_fixed_blocks_projection_th)
val second_phi_fixed_blocks =
  fst (listSyntax.dest_list second_phi_fixed_blocks_tm)
val _ =
  if length second_phi_fixed_blocks = 3 then ()
  else raise Fail "second PHI-fixed function changed fixture block count"
val second_entry_bb_tm = List.nth (second_phi_fixed_blocks, 0)
val second_dispatch_bb_tm = List.nth (second_phi_fixed_blocks, 1)
val second_fallback_bb_tm = List.nth (second_phi_fixed_blocks, 2)
val _ = map (assert_closed "second PHI-fixed block") second_phi_fixed_blocks

Definition second_simplify_cfg_entry_bb_def:
  second_simplify_cfg_entry_bb = ^second_entry_bb_tm
End

Definition second_simplify_cfg_dispatch_bb_def:
  second_simplify_cfg_dispatch_bb = ^second_dispatch_bb_tm
End

Definition second_simplify_cfg_fallback_bb_def:
  second_simplify_cfg_fallback_bb = ^second_fallback_bb_tm
End
val second_phi_fixed_blocks_named_th =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (PURE_REWRITE_RULE
      [GSYM second_simplify_cfg_entry_bb_def,
       GSYM second_simplify_cfg_dispatch_bb_def,
       GSYM second_simplify_cfg_fallback_bb_def]
      (TRANS
        (AP_TERM ``\fn : ir_function. fn.fn_blocks`` second_phi_fixed_normal_th)
        second_phi_fixed_blocks_projection_th))

fun literal_query c args = list_mk_comb (c, args)
fun eval_literal label query_head tm =
  let
    val th = computeLib.EVAL_CONV tm
    val _ = assert_reduced label query_head th
  in
    th
  end

val second_entry_lookup_raw = eval_literal "entry lookup" ``lookup_block``
  (literal_query ``lookup_block`` [``"__entry"``, second_phi_fixed_blocks_tm])
val second_dispatch_lookup_raw = eval_literal "dispatch lookup" ``lookup_block``
  (literal_query ``lookup_block`` [``"@dispatch_1"``, second_phi_fixed_blocks_tm])
val second_fallback_lookup_raw = eval_literal "fallback lookup" ``lookup_block``
  (literal_query ``lookup_block`` [``"@fallback_0"``, second_phi_fixed_blocks_tm])
val second_entry_succs_raw = eval_literal "entry successors" ``bb_succs``
  (mk_comb (``bb_succs``, second_entry_bb_tm))
val second_dispatch_succs_raw = eval_literal "dispatch successors" ``bb_succs``
  (mk_comb (``bb_succs``, second_dispatch_bb_tm))
val second_fallback_succs_raw = eval_literal "fallback successors" ``bb_succs``
  (mk_comb (``bb_succs``, second_fallback_bb_tm))
val second_fallback_preds_raw = eval_literal "fallback predecessor count" ``num_preds``
  (literal_query ``num_preds`` [second_phi_fixed_tm, ``"@fallback_0"``])
val second_entry_try_bypass_raw = eval_literal "entry try_bypass" ``try_bypass``
  (literal_query ``try_bypass``
    [second_phi_fixed_tm, ``[] : (string # string) list``, second_entry_bb_tm,
     ``["@fallback_0"; "@dispatch_1"]``])
val second_dispatch_merge_fallback_raw = eval_literal "dispatch/fallback merge" ``can_merge_blocks``
  (literal_query ``can_merge_blocks``
    [second_phi_fixed_tm, second_dispatch_bb_tm, second_fallback_bb_tm])

val naming_rewrites =
  [GSYM second_phi_fixed_normal_th,
   GSYM second_simplify_cfg_entry_bb_def,
   GSYM second_simplify_cfg_dispatch_bb_def,
   GSYM second_simplify_cfg_fallback_bb_def,
   GSYM second_phi_fixed_blocks_named_th]
fun name_decision th = PURE_REWRITE_RULE naming_rewrites th
val second_entry_lookup_th = name_decision second_entry_lookup_raw
val second_dispatch_lookup_th = name_decision second_dispatch_lookup_raw
val second_fallback_lookup_th = name_decision second_fallback_lookup_raw
val second_entry_succs_th = name_decision second_entry_succs_raw
val second_dispatch_succs_th = name_decision second_dispatch_succs_raw
val second_fallback_succs_th = name_decision second_fallback_succs_raw
val second_fallback_preds_th = name_decision second_fallback_preds_raw
val second_entry_try_bypass_th = name_decision second_entry_try_bypass_raw
val second_dispatch_merge_fallback_th =
  name_decision second_dispatch_merge_fallback_raw

Theorem exact_second_entry_lookup:
  lookup_block "__entry" second_simplify_cfg_phi_fixed.fn_blocks =
    SOME second_simplify_cfg_entry_bb
Proof
  ACCEPT_TAC second_entry_lookup_th
QED

Theorem exact_second_dispatch_lookup:
  lookup_block "@dispatch_1" second_simplify_cfg_phi_fixed.fn_blocks =
    SOME second_simplify_cfg_dispatch_bb
Proof
  ACCEPT_TAC second_dispatch_lookup_th
QED

Theorem exact_second_fallback_lookup:
  lookup_block "@fallback_0" second_simplify_cfg_phi_fixed.fn_blocks =
    SOME second_simplify_cfg_fallback_bb
Proof
  ACCEPT_TAC second_fallback_lookup_th
QED

Theorem exact_second_entry_succs:
  bb_succs second_simplify_cfg_entry_bb =
    ["@fallback_0"; "@dispatch_1"]
Proof
  ACCEPT_TAC second_entry_succs_th
QED

Theorem exact_second_dispatch_succs:
  bb_succs second_simplify_cfg_dispatch_bb = ["@fallback_0"]
Proof
  ACCEPT_TAC second_dispatch_succs_th
QED

Theorem exact_second_fallback_succs:
  bb_succs second_simplify_cfg_fallback_bb = []
Proof
  ACCEPT_TAC second_fallback_succs_th
QED

Theorem exact_second_fallback_preds:
  num_preds second_simplify_cfg_phi_fixed "@fallback_0" = 2
Proof
  ACCEPT_TAC second_fallback_preds_th
QED

Theorem exact_second_entry_try_bypass:
  try_bypass second_simplify_cfg_phi_fixed [] second_simplify_cfg_entry_bb
    ["@fallback_0"; "@dispatch_1"] =
  (second_simplify_cfg_phi_fixed, [], F)
Proof
  rewrite_tac [second_entry_try_bypass_th] >>
  pure_rewrite_tac [second_phi_fixed_normal_th, operand_def] >>
  simp[venomInstTheory.ir_function_component_equality]
QED

Theorem exact_second_dispatch_merge_fallback:
  can_merge_blocks second_simplify_cfg_phi_fixed
    second_simplify_cfg_dispatch_bb second_simplify_cfg_fallback_bb = F
Proof
  ACCEPT_TAC second_dispatch_merge_fallback_th
QED

val _ = export_theory()
