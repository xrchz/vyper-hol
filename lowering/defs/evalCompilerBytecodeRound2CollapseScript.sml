Theory evalCompilerBytecodeRound2Collapse
Ancestors evalCompilerBytecodeRound2Phi

open HolKernel Parse boolLib bossLib

val round2_collapse_entry_th =
  computeLib.EVAL_CONV
    ``fn_entry_label first_simplify_cfg_round2_phi_fixed``
val round2_collapse_entry_tm =
  optionSyntax.dest_some (rhs (concl round2_collapse_entry_th))

Theorem first_simplify_cfg_round2_phi_fixed_entry:
  ^(concl round2_collapse_entry_th)
Proof
  ACCEPT_TAC round2_collapse_entry_th
QED

fun rew_round2_collapse tm = FIRST_CONV
  [REWR_CONV (cj 1 simplifyCfgDefsTheory.collapse_dfs_def),
   REWR_CONV (cj 2 simplifyCfgDefsTheory.collapse_dfs_def),
   REWR_CONV (cj 3 simplifyCfgDefsTheory.collapse_dfs_def)] tm

val round2_collapse_start_tm =
  ``collapse_dfs first_simplify_cfg_round2_phi_fixed [] []
      ^round2_collapse_entry_tm``
val round2_collapse_step_1_raw =
  rew_round2_collapse round2_collapse_start_tm
val round2_collapse_step_1 =
  CONV_RULE
    (RAND_CONV (computeLib.RESTR_EVAL_CONV
      [``collapse_dfs``, ``collapse_dfs_succs``]))
    round2_collapse_step_1_raw

Theorem exact_round2_collapse_step_1:
  ^(concl round2_collapse_step_1)
Proof
  ACCEPT_TAC round2_collapse_step_1
QED

val round2_collapse_step_2_local =
  rew_round2_collapse (rhs (concl round2_collapse_step_1))
val round2_collapse_final =
  TRANS round2_collapse_step_1 round2_collapse_step_2_local
val round2_collapse_result_tm = rhs (concl round2_collapse_final)

Definition first_simplify_cfg_round2_collapse_result_def:
  first_simplify_cfg_round2_collapse_result = ^round2_collapse_result_tm
End

Theorem exact_round2_collapse_dfs:
  collapse_dfs first_simplify_cfg_round2_phi_fixed [] []
    ^round2_collapse_entry_tm = first_simplify_cfg_round2_collapse_result
Proof
  simp[first_simplify_cfg_round2_collapse_result_def] >>
  ACCEPT_TAC round2_collapse_final
QED

val (collapsed_fn2, round2_collapse_tail_tm) =
  pairSyntax.dest_pair round2_collapse_result_tm
val (label_map2, visited2) =
  pairSyntax.dest_pair round2_collapse_tail_tm

Theorem exact_round2_collapse_dfs_components:
  collapse_dfs first_simplify_cfg_round2_phi_fixed [] []
    ^round2_collapse_entry_tm = (^collapsed_fn2, ^label_map2, ^visited2)
Proof
  simp[first_simplify_cfg_round2_collapse_result_def] >>
  ACCEPT_TAC round2_collapse_final
QED

val _ = export_theory()
