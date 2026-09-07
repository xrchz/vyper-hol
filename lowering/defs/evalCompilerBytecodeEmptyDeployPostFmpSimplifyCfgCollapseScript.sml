Theory evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgCollapse
Ancestors evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgInitial
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

val phi_blocks_th =
  evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgInitialTheory.exact_empty_deploy_post_fmp_simplify_cfg_phi_fixed_blocks
val phi_blocks = fst (listSyntax.dest_list (rhs (concl phi_blocks_th)))
val _ =
  if length phi_blocks = 1 then ()
  else raise Fail "post-FMP deploy PHI-fixed function is not a singleton"
val phi_block_tm = hd phi_blocks

Definition empty_deploy_post_fmp_simplify_cfg_phi_block_def:
  empty_deploy_post_fmp_simplify_cfg_phi_block = ^phi_block_tm
End

val collapse_entry_th =
  computeLib.EVAL_CONV
    ``fn_entry_label empty_deploy_post_fmp_simplify_cfg_phi_fixed``
val collapse_entry_tm = optionSyntax.dest_some (rhs (concl collapse_entry_th))
val collapse_lookup_th = computeLib.EVAL_CONV
  ``lookup_block ^collapse_entry_tm
      empty_deploy_post_fmp_simplify_cfg_phi_fixed.fn_blocks``
val collapse_succs_th = computeLib.EVAL_CONV
  ``bb_succs empty_deploy_post_fmp_simplify_cfg_phi_block``
val collapse_succs_tm = rhs (concl collapse_succs_th)
val collapse_try_bypass_th = computeLib.EVAL_CONV
  ``try_bypass empty_deploy_post_fmp_simplify_cfg_phi_fixed []
      empty_deploy_post_fmp_simplify_cfg_phi_block ^collapse_succs_tm``

Theorem exact_empty_deploy_post_fmp_simplify_cfg_collapse_decisions:
  ^(concl collapse_entry_th) /\
  ^(concl collapse_lookup_th) /\
  ^(concl collapse_succs_th) /\
  ^(concl collapse_try_bypass_th)
Proof
  ACCEPT_TAC (LIST_CONJ
    [collapse_entry_th, collapse_lookup_th, collapse_succs_th,
     collapse_try_bypass_th])
QED

val collapse_result_tm =
  ``(empty_deploy_post_fmp_simplify_cfg_phi_fixed,
      ([] : (string # string) list), [^collapse_entry_tm])``

Definition empty_deploy_post_fmp_simplify_cfg_collapse_result_def:
  empty_deploy_post_fmp_simplify_cfg_collapse_result = ^collapse_result_tm
End

Theorem exact_empty_deploy_post_fmp_collapse_dfs:
  collapse_dfs empty_deploy_post_fmp_simplify_cfg_phi_fixed [] []
    ^collapse_entry_tm = empty_deploy_post_fmp_simplify_cfg_collapse_result
Proof
  pure_once_rewrite_tac [cj 1 simplifyCfgDefsTheory.collapse_dfs_def] >>
  rewrite_tac [phi_blocks_th, collapse_lookup_th] >>
  simp[] >>
  rewrite_tac [GSYM empty_deploy_post_fmp_simplify_cfg_phi_block_def,
               collapse_succs_th] >>
  simp[] >>
  rewrite_tac [collapse_try_bypass_th] >>
  simp[empty_deploy_post_fmp_simplify_cfg_collapse_result_def,
       cj 2 simplifyCfgDefsTheory.collapse_dfs_def,
       cj 3 simplifyCfgDefsTheory.collapse_dfs_def] >>
  simp[venomInstTheory.ir_function_component_equality, phi_blocks_th,
       evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgInitialTheory.empty_deploy_post_fmp_simplify_cfg_phi_fixed_def,
       evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgInitialTheory.empty_deploy_post_fmp_simplify_cfg_removed_def,
       evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.empty_deploy_post_fmp_simplify_cfg_operand_def]
QED

Theorem exact_empty_deploy_post_fmp_collapse_dfs_components:
  collapse_dfs empty_deploy_post_fmp_simplify_cfg_phi_fixed [] []
    ^collapse_entry_tm =
    (empty_deploy_post_fmp_simplify_cfg_phi_fixed,
     ([] : (string # string) list), [^collapse_entry_tm])
Proof
  simp[exact_empty_deploy_post_fmp_collapse_dfs,
       empty_deploy_post_fmp_simplify_cfg_collapse_result_def]
QED

val _ = export_theory()
