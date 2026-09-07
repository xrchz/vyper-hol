Theory evalCompilerBytecodeEmptySafetyPredicates
Ancestors evalCompilerBytecodeEmptySafetyStructural
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

Theorem empty_runtime_final_target_safe:
  context_target_safe prague_capabilities
    empty_runtime_final_unit.cu_context
Proof
  simp[venomTargetSafetyTheory.context_target_safe_def,
       venomTargetSafetyTheory.function_target_safe_def,
       venomTargetSafetyTheory.basic_block_target_safe_def,
       venomTargetSafetyTheory.instruction_target_safe_def,
       venomTargetSafetyTheory.opcode_target_supported_def,
       venomPolicyTypesTheory.prague_capabilities_def,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_functions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact]
QED

Theorem empty_runtime_final_concretized_layouts_wf:
  concretized_static_layouts_wf empty_runtime_final_unit.cu_context
Proof
  simp[staticLayoutWfTheory.concretized_static_layouts_wf_def,
       staticLayoutDefsTheory.reserved_intervals_wf_def,
       venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_global_reserved_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_functions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_forced_positions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_eom_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact] >>
  rpt strip_tac >> gvs[]
QED

Theorem empty_runtime_final_eom_and_no_raw_fmp[local]:
  IS_SOME empty_runtime_final_fn.fn_eom /\
  no_raw_fmp_ops empty_runtime_final_fn
Proof
  simp[venomInstTheory.no_raw_fmp_ops_def,
       venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_eom_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact] >>
  rpt strip_tac >> gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem empty_runtime_final_call_abi_matches[local]:
  call_abi_matches_fn empty_runtime_final_fn
Proof
  rewrite_tac[fmpWfDefsTheory.call_abi_matches_fn_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_fmp_signature_exact] >>
  simp[] >>
  rewrite_tac[fmpWfDefsTheory.fmp_return_abi_matches_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_call_abi_exact] >>
  conj_tac >-
    (simp[callLayoutDefsTheory.canonical_param_prefix_def,
          callLayoutDefsTheory.canonical_entry_params_from_def,
          callLayoutDefsTheory.canonical_after_fmp_def,
          callLayoutDefsTheory.no_param_insts_def,
          callLayoutDefsTheory.param_inst_at_def,
          venomInstTheory.is_param_opcode_def,
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact]) >>
  `fn_return_insts empty_runtime_final_fn = []` by
    (rewrite_tac[callLayoutDefsTheory.fn_return_insts_def] >>
     rewrite_tac[
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact] >>
     simp[] >>
     rewrite_tac[
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact] >>
     EVAL_TAC) >>
  simp[]
QED

Theorem empty_runtime_final_fmp_signature_matches[local]:
  fmp_signature_matches_fn empty_runtime_final_unit.cu_context
    empty_runtime_final_fn
Proof
  rewrite_tac[fmpWfDefsTheory.fmp_signature_matches_fn_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_fmp_signature_exact] >>
  simp[] >>
  conj_tac >-
    (rewrite_tac[fmpWfDefsTheory.fmp_signature_syntax_wf_def] >>
     mp_tac empty_runtime_final_call_abi_matches >>
     rewrite_tac[fmpWfDefsTheory.call_abi_matches_fn_def] >>
     rewrite_tac[
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_fmp_signature_exact] >>
     simp[] >> strip_tac >>
     conj_tac >-
       (rewrite_tac[callLayoutDefsTheory.fn_hidden_fmp_param_def,
                     callLayoutDefsTheory.fn_entry_insts_def,
                     venomInstTheory.entry_block_def] >>
        rewrite_tac[
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact] >>
        simp[] >>
        rewrite_tac[
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact] >>
        EVAL_TAC) >>
     rewrite_tac[fmpWfDefsTheory.fmp_lowered_return_layout_wf_def] >>
     `fn_return_insts empty_runtime_final_fn = []` by
       (rewrite_tac[callLayoutDefsTheory.fn_return_insts_def] >>
        rewrite_tac[
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact] >>
        simp[] >>
        rewrite_tac[
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
          evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact] >>
        EVAL_TAC) >>
     simp[]) >>
  rewrite_tac[fmpWfDefsTheory.fmp_runner_rooted_wf_def,
              venomInstTheory.fn_insts_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact] >>
  rewrite_tac[venomInstTheory.fn_insts_blocks_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact] >>
  simp[fmpWfDefsTheory.fmp_runner_inst_wf_def,
       fmpWfDefsTheory.fmp_bump_consumer_wf_def,
       fmpWfDefsTheory.fmp_invoke_consumer_wf_def,
       fmpWfDefsTheory.fmp_return_consumer_wf_def]
QED

Theorem empty_runtime_final_invoke_layout[local]:
  !inst. MEM inst (fn_insts empty_runtime_final_fn) ==>
    invoke_layout_wf empty_runtime_final_unit.cu_context inst
Proof
  rpt strip_tac >>
  rewrite_tac[fmpWfDefsTheory.invoke_layout_wf_def] >>
  strip_tac >>
  qpat_x_assum `MEM inst (fn_insts empty_runtime_final_fn)` mp_tac >>
  rewrite_tac[venomInstTheory.fn_insts_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact] >>
  rewrite_tac[venomInstTheory.fn_insts_blocks_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact] >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem empty_runtime_final_fmp_lowered_wf:
  fmp_lowered_context_wf empty_runtime_final_unit.cu_context
Proof
  rewrite_tac[fmpWfDefsTheory.fmp_lowered_context_wf_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_functions_exact] >>
  simp[empty_runtime_final_concretized_layouts_wf,
       empty_runtime_final_eom_and_no_raw_fmp,
       empty_runtime_final_call_abi_matches,
       empty_runtime_final_fmp_signature_matches,
       empty_runtime_final_invoke_layout]
QED

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t

val exact_empty_runtime_final_fcg = computeLib.EVAL_CONV
  ``fcg_analyze empty_runtime_final_unit.cu_context``
val empty_runtime_final_fcg_tm = rhs (concl exact_empty_runtime_final_fcg)
val _ =
  if null (free_vars empty_runtime_final_fcg_tm) then ()
  else raise Fail "empty runtime final call graph is not closed"
val _ =
  if has_head ``fcg_dfs`` empty_runtime_final_fcg_tm orelse
     has_head ``fcg_visit`` empty_runtime_final_fcg_tm
  then raise Fail "empty runtime final call graph has residual traversal"
  else ()

Theorem empty_runtime_final_fcg_exact[local]:
  ^(concl exact_empty_runtime_final_fcg)
Proof
  ACCEPT_TAC exact_empty_runtime_final_fcg
QED

Theorem empty_runtime_final_reachable_fcg_acyclic:
  reachable_fcg_acyclic empty_runtime_final_unit.cu_context
    (fcg_analyze empty_runtime_final_unit.cu_context)
Proof
  rewrite_tac[empty_runtime_final_fcg_exact] >>
  rewrite_tac[fcgDefsTheory.reachable_fcg_acyclic_def] >>
  rewrite_tac[
    evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_context_entry_exact] >>
  simp[fcgDefsTheory.fcg_postorder_def,
       fcgDefsTheory.fcg_get_callees_def,
       fcgDefsTheory.list_precedes_def]
QED

Theorem empty_runtime_final_canonical_params[local]:
  canonical_param_prefix empty_runtime_final_fn
Proof
  simp[callLayoutDefsTheory.canonical_param_prefix_def,
       callLayoutDefsTheory.canonical_entry_params_from_def,
       callLayoutDefsTheory.canonical_after_fmp_def,
       callLayoutDefsTheory.no_param_insts_def,
       callLayoutDefsTheory.param_inst_at_def,
       venomInstTheory.is_param_opcode_def,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact]
QED

Theorem empty_runtime_final_ssa_form[local]:
  ssa_form empty_runtime_final_fn
Proof
  simp[venomWfTheory.ssa_form_def,
       venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block0_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block1_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block2_instructions_exact,
       evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_block3_instructions_exact]
QED

Definition block_defs_before_uses_def[local]:
  block_defs_before_uses bb <=>
    !inst v.
      MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands ==>
      ?def_inst i j.
        MEM def_inst bb.bb_instructions /\
        MEM v def_inst.inst_outputs /\
        i < j /\
        j < LENGTH bb.bb_instructions /\
        EL i bb.bb_instructions = def_inst /\
        EL j bb.bb_instructions = inst
End

val empty_runtime_final_entry_label = computeLib.EVAL_CONV
  ``fn_entry_label empty_runtime_final_fn``
val empty_runtime_final_block0_label = computeLib.EVAL_CONV
  ``empty_runtime_final_block0.bb_label``
val empty_runtime_final_block1_label = computeLib.EVAL_CONV
  ``empty_runtime_final_block1.bb_label``
val empty_runtime_final_block2_label = computeLib.EVAL_CONV
  ``empty_runtime_final_block2.bb_label``
val empty_runtime_final_block3_label = computeLib.EVAL_CONV
  ``empty_runtime_final_block3.bb_label``
val empty_runtime_final_block0_succs = computeLib.EVAL_CONV
  ``bb_succs empty_runtime_final_block0``
val empty_runtime_final_block1_succs = computeLib.EVAL_CONV
  ``bb_succs empty_runtime_final_block1``

Theorem empty_runtime_final_member_self_dominates[local]:
  !bb. MEM bb empty_runtime_final_fn.fn_blocks ==>
    fn_dominates empty_runtime_final_fn bb.bb_label bb.bb_label
Proof
  `fn_cfg_edge empty_runtime_final_fn "__entry" "@dispatch_1"` by
    (rewrite_tac[venomWfTheory.fn_cfg_edge_def] >>
     qexists `empty_runtime_final_block0` >>
     simp[evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
          empty_runtime_final_block0_label,
          empty_runtime_final_block0_succs]) >>
  `fn_cfg_edge empty_runtime_final_fn "__entry" "formal_label_0"` by
    (rewrite_tac[venomWfTheory.fn_cfg_edge_def] >>
     qexists `empty_runtime_final_block0` >>
     simp[evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
          empty_runtime_final_block0_label,
          empty_runtime_final_block0_succs]) >>
  `fn_cfg_edge empty_runtime_final_fn "@dispatch_1" "@fallback_0"` by
    (rewrite_tac[venomWfTheory.fn_cfg_edge_def] >>
     qexists `empty_runtime_final_block1` >>
     simp[evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact,
          empty_runtime_final_block1_label,
          empty_runtime_final_block1_succs]) >>
  `!bb. MEM bb empty_runtime_final_fn.fn_blocks ==>
      fn_reachable empty_runtime_final_fn bb.bb_label` by
    (simp[evalCompilerBytecodeEmptyResultTheory.empty_runtime_final_blocks_exact] >>
     rpt strip_tac >> gvs[] >>
     simp[venomWfTheory.fn_reachable_def,
          empty_runtime_final_entry_label,
          empty_runtime_final_block0_label,
          empty_runtime_final_block1_label,
          empty_runtime_final_block2_label,
          empty_runtime_final_block3_label] >>
     irule relationTheory.RTC_RTC >>
     qexists `"@dispatch_1"` >>
     conj_tac >-
       (irule relationTheory.RTC_SINGLE >> simp[]) >>
     irule relationTheory.RTC_SINGLE >> simp[]) >>
  rpt strip_tac >>
  rewrite_tac[venomWfTheory.fn_dominates_def] >>
  conj_tac >- (first_x_assum irule >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `LAST path = bb.bb_label` (fn th => rewrite_tac[GSYM th]) >>
  irule rich_listTheory.LAST_MEM >> simp[]
QED

Theorem empty_runtime_final_codegen_ready:
  codegen_ready empty_runtime_final_unit.cu_context
Proof
  cheat
QED

Theorem empty_runtime_final_mem_ok:
  (K T) empty_runtime_final_unit.cu_context
Proof
  simp[]
QED

Theorem empty_runtime_final_calling_ok:
  (K T) empty_runtime_final_unit.cu_context
Proof
  simp[]
QED

Theorem empty_runtime_final_post_ok:
  (K T) empty_runtime_final_unit.cu_context
Proof
  simp[]
QED

val _ = export_theory()
