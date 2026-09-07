Theory evalCompilerBytecodeRound2Subst
Ancestors evalCompilerBytecodeRound2Collapse

open HolKernel Parse boolLib bossLib

val round2_collapse_components_th =
  evalCompilerBytecodeRound2CollapseTheory.exact_round2_collapse_dfs_components
val round2_collapse_components_tm = rhs (concl round2_collapse_components_th)
val (collapsed_fn2, round2_collapse_tail_tm) =
  pairSyntax.dest_pair round2_collapse_components_tm
val (label_map2, visited2) =
  pairSyntax.dest_pair round2_collapse_tail_tm

val round2_substitution_tm =
  mk_cond
    (mk_eq (label_map2,
            listSyntax.mk_list ([], listSyntax.dest_list_type
              (type_of label_map2))),
     collapsed_fn2,
     list_mk_comb (``subst_block_labels_fn``, [label_map2, collapsed_fn2]))
val round2_substitution_th = computeLib.EVAL_CONV round2_substitution_tm
val round2_substituted_tm = rhs (concl round2_substitution_th)

Definition first_simplify_cfg_round2_substituted_def:
  first_simplify_cfg_round2_substituted = ^round2_substituted_tm
End

Theorem exact_round2_substitution:
  (if ^label_map2 = [] then ^collapsed_fn2
   else subst_block_labels_fn ^label_map2 ^collapsed_fn2) =
    first_simplify_cfg_round2_substituted
Proof
  simp[first_simplify_cfg_round2_substituted_def] >>
  ACCEPT_TAC round2_substitution_th
QED

val _ = export_theory()
