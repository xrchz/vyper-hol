Theory evalCompilerBytecodeRound2Result
Ancestors evalCompilerBytecodeRound2FinalPhi

open HolKernel Parse boolLib bossLib

val round2_fixpoint_guard_th =
  computeLib.EVAL_CONV
    ``first_simplify_cfg_round2_fn.fn_blocks =
      first_simplify_cfg_round1_fn.fn_blocks``

Theorem exact_second_round_fixpoint_guard:
  ^(concl round2_fixpoint_guard_th)
Proof
  ACCEPT_TAC round2_fixpoint_guard_th
QED


val first_round_rhs =
  rhs (concl
    evalCompilerBytecodeSimplifyCfgProbeTheory.exact_first_simplify_cfg_round_with_labels)
val (_, first_round_map_tm) = pairSyntax.dest_pair first_round_rhs
val second_round_rhs =
  rhs (concl
    evalCompilerBytecodeRound2FinalPhiTheory.exact_second_simplify_cfg_round_with_labels)
val (_, second_round_map_tm) = pairSyntax.dest_pair second_round_rhs
val combined_round_map_th =
  computeLib.EVAL_CONV ``^first_round_map_tm ++ ^second_round_map_tm``
val combined_round_map_tm = rhs (concl combined_round_map_th)

val second_iter_unfold_th =
  SIMP_RULE (srw_ss ()) []
    (Q.SPECL [`1`, `first_simplify_cfg_round1_fn`]
      (cj 2 simplifyCfgDefsTheory.simplify_cfg_iter_with_labels_def))

Theorem exact_second_simplify_cfg_iter_unfold:
  ^(concl second_iter_unfold_th)
Proof
  ACCEPT_TAC second_iter_unfold_th
QED
Theorem exact_first_simplify_cfg_iter_with_labels:
  simplify_cfg_iter_with_labels
      (LENGTH first_simplify_cfg_operand.fn_blocks)
      first_simplify_cfg_operand =
    (first_simplify_cfg_round1_fn, ^combined_round_map_tm)
Proof
  simp[evalCompilerBytecodeSimplifyCfgProbeTheory.first_simplify_cfg_operand_block_count] >>
  simp[evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_named_iter_one,
       exact_second_simplify_cfg_iter_unfold,
       evalCompilerBytecodeSimplifyCfgProbeTheory.exact_first_simplify_cfg_round_with_labels,
       evalCompilerBytecodeSimplifyCfgProbeTheory.exact_first_round_fixpoint_guard,
       evalCompilerBytecodeRound2FinalPhiTheory.exact_second_simplify_cfg_round_with_labels,
       exact_second_round_fixpoint_guard]
QED

Theorem exact_first_simplify_cfg_fn_with_labels:
  simplify_cfg_fn_with_labels first_simplify_cfg_operand =
    (first_simplify_cfg_round1_fn, ^combined_round_map_tm)
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def,
       exact_first_simplify_cfg_iter_with_labels]
QED

Theorem exact_first_simplify_cfg_fn_with_labels_fst:
  FST (simplify_cfg_fn_with_labels first_simplify_cfg_operand) =
    first_simplify_cfg_round1_fn
Proof
  simp[exact_first_simplify_cfg_fn_with_labels]
QED

Theorem exact_first_simplify_cfg_fn:
  simplify_cfg_fn first_simplify_cfg_operand =
    first_simplify_cfg_round1_fn
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_def,
       exact_first_simplify_cfg_fn_with_labels]
QED
val _ = export_theory()
