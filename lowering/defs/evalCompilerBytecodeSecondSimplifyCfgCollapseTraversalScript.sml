Theory evalCompilerBytecodeSecondSimplifyCfgCollapseTraversal
Ancestors evalCompilerBytecodeSecondSimplifyCfgCollapseDecisions

open HolKernel Parse boolLib bossLib


Theorem exact_second_collapse_fallback_fresh:
  collapse_dfs second_simplify_cfg_phi_fixed [] ["__entry"] "@fallback_0" =
    (second_simplify_cfg_phi_fixed, [], ["@fallback_0"; "__entry"])
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[exact_second_fallback_lookup,
       GSYM second_simplify_cfg_fallback_bb_def,
       exact_second_fallback_succs, simplifyCfgDefsTheory.try_bypass_def,
       cj 2 simplifyCfgDefsTheory.collapse_dfs_def]
QED

Theorem exact_second_collapse_fallback_visited:
  collapse_dfs second_simplify_cfg_phi_fixed []
    ["@dispatch_1"; "@fallback_0"; "__entry"] "@fallback_0" =
  (second_simplify_cfg_phi_fixed, [],
    ["@dispatch_1"; "@fallback_0"; "__entry"])
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[exact_second_fallback_lookup,
       GSYM second_simplify_cfg_fallback_bb_def,
       exact_second_fallback_succs, simplifyCfgDefsTheory.try_bypass_def,
       cj 2 simplifyCfgDefsTheory.collapse_dfs_def]
QED

Theorem exact_second_collapse_dispatch:
  collapse_dfs second_simplify_cfg_phi_fixed []
    ["@fallback_0"; "__entry"] "@dispatch_1" =
  (second_simplify_cfg_phi_fixed, [],
    ["@dispatch_1"; "@fallback_0"; "__entry"])
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[exact_second_dispatch_lookup,
       GSYM second_simplify_cfg_dispatch_bb_def,
       exact_second_dispatch_succs, exact_second_fallback_lookup,
       GSYM second_simplify_cfg_fallback_bb_def,
       exact_second_dispatch_merge_fallback,
       exact_second_collapse_fallback_visited]
QED

Theorem exact_second_collapse_entry_succs:
  collapse_dfs_succs second_simplify_cfg_phi_fixed [] ["__entry"]
    ["@fallback_0"; "@dispatch_1"] =
  (second_simplify_cfg_phi_fixed, [],
    ["@dispatch_1"; "@fallback_0"; "__entry"])
Proof
  pure_once_rewrite_tac [cj 3 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[exact_second_collapse_fallback_fresh] >>
  pure_once_rewrite_tac [cj 3 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[exact_second_collapse_dispatch,
       cj 2 simplifyCfgDefsTheory.collapse_dfs_def]
QED

Definition second_simplify_cfg_collapse_result_def:
  second_simplify_cfg_collapse_result =
    (second_simplify_cfg_phi_fixed, ([] : (string # string) list),
     ["@dispatch_1"; "@fallback_0"; "__entry"])
End

Theorem exact_second_collapse_dfs:
  collapse_dfs second_simplify_cfg_phi_fixed [] [] "__entry" =
    second_simplify_cfg_collapse_result
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[exact_second_entry_lookup, GSYM second_simplify_cfg_entry_bb_def,
       exact_second_entry_succs, exact_second_entry_try_bypass,
       exact_second_collapse_entry_succs,
       second_simplify_cfg_collapse_result_def]
QED

Theorem second_simplify_cfg_collapse_result_components:
  FST second_simplify_cfg_collapse_result = second_simplify_cfg_phi_fixed /\
  FST (SND second_simplify_cfg_collapse_result) =
    ([] : (string # string) list) /\
  SND (SND second_simplify_cfg_collapse_result) =
    ["@dispatch_1"; "@fallback_0"; "__entry"]
Proof
  simp[second_simplify_cfg_collapse_result_def]
QED

val _ = export_theory()
