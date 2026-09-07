Theory evalCompilerBytecodeEmptyDeploySafetyPredicates
Ancestors evalCompilerBytecodeEmptyDeployStandaloneWalk
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t

val functions_th = computeLib.EVAL_CONV
  ``empty_deploy_final_compilation_unit.cu_context.ctx_functions``
val functions = fst (listSyntax.dest_list (rhs (concl functions_th)))
val _ = if length functions = 1 then ()
  else raise Fail "exact final deploy unit is not singleton-function"
val final_fn_tm = hd functions

Definition empty_deploy_final_fn_def:
  empty_deploy_final_fn = ^final_fn_tm
End

val functions_named =
  REWRITE_RULE [GSYM empty_deploy_final_fn_def] functions_th

Theorem empty_deploy_final_functions_exact:
  ^(concl functions_named)
Proof
  ACCEPT_TAC functions_named
QED

val blocks_th = computeLib.EVAL_CONV ``empty_deploy_final_fn.fn_blocks``
val blocks = fst (listSyntax.dest_list (rhs (concl blocks_th)))
val _ = if length blocks = 1 then ()
  else raise Fail "exact final deploy function is not singleton-block"
val block_tm = hd blocks

Definition empty_deploy_final_block_def:
  empty_deploy_final_block = ^block_tm
End

val blocks_named = REWRITE_RULE [GSYM empty_deploy_final_block_def] blocks_th

Theorem empty_deploy_final_blocks_exact:
  ^(concl blocks_named)
Proof
  ACCEPT_TAC blocks_named
QED

val block_insts = computeLib.EVAL_CONV
  ``empty_deploy_final_block.bb_instructions``
val context_entry = computeLib.EVAL_CONV
  ``empty_deploy_final_compilation_unit.cu_context.ctx_entry``

Theorem empty_deploy_final_block_instructions_exact:
  ^(concl block_insts)
Proof
  ACCEPT_TAC block_insts
QED

Theorem empty_deploy_final_context_entry_exact:
  ^(concl context_entry)
Proof
  ACCEPT_TAC context_entry
QED

val exact_empty_deploy_final_fcg = computeLib.EVAL_CONV
  ``fcg_analyze empty_deploy_final_compilation_unit.cu_context``
val empty_deploy_final_fcg_tm = rhs (concl exact_empty_deploy_final_fcg)
val _ =
  if null (free_vars empty_deploy_final_fcg_tm) andalso
     not (has_head ``fcg_dfs`` empty_deploy_final_fcg_tm) andalso
     not (has_head ``fcg_visit`` empty_deploy_final_fcg_tm)
  then () else raise Fail "empty deploy final call graph is malformed"

Theorem empty_deploy_final_fcg_exact[local]:
  ^(concl exact_empty_deploy_final_fcg)
Proof
  ACCEPT_TAC exact_empty_deploy_final_fcg
QED

Theorem empty_deploy_final_reachable_fcg_acyclic:
  reachable_fcg_acyclic empty_deploy_final_compilation_unit.cu_context
    (fcg_analyze empty_deploy_final_compilation_unit.cu_context)
Proof
  rewrite_tac[empty_deploy_final_fcg_exact] >>
  rewrite_tac[fcgDefsTheory.reachable_fcg_acyclic_def] >>
  rewrite_tac[empty_deploy_final_context_entry_exact] >>
  simp[fcgDefsTheory.fcg_postorder_def,
       fcgDefsTheory.fcg_get_callees_def,
       fcgDefsTheory.list_precedes_def]
QED

Theorem final_bb_well_formed_snoc[local]:
  is_terminator term.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
  EVERY (\i. i.inst_opcode <> PHI) (prefix ++ [term]) ==>
  bb_well_formed
    <| bb_label := lbl; bb_instructions := prefix ++ [term] |>
Proof
  rw[venomWfTheory.bb_well_formed_def] >>
  rpt strip_tac >> simp[]
  >- (Cases_on `i < LENGTH prefix`
      >- gvs[listTheory.EVERY_EL, listTheory.EL_APPEND_EQN]
      >> `i = LENGTH prefix` by decide_tac
      >> simp[listTheory.EL_APPEND_EQN])
  >> Cases_on `j < LENGTH prefix`
  >- gvs[listTheory.EVERY_EL, listTheory.EL_APPEND_EQN]
  >> `j = LENGTH prefix` by decide_tac
  >> gvs[listTheory.EL_APPEND_EQN]
QED

Theorem empty_deploy_final_block_snoc[local]:
  empty_deploy_final_block =
    <| bb_label := empty_deploy_final_block.bb_label;
       bb_instructions := FRONT empty_deploy_final_block.bb_instructions ++
                          [LAST empty_deploy_final_block.bb_instructions] |>
Proof
  EVAL_TAC
QED

Theorem empty_deploy_final_block_wf[local]:
  bb_well_formed empty_deploy_final_block
Proof
  once_rewrite_tac[empty_deploy_final_block_snoc] >>
  irule final_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem empty_deploy_final_block_insts_wf[local]:
  EVERY inst_wf empty_deploy_final_block.bb_instructions
Proof
  EVAL_TAC >> simp[venomWfTheory.inst_wf_def]
QED

val final_block_label = computeLib.EVAL_CONV
  ``empty_deploy_final_block.bb_label``
val final_block_succs = computeLib.EVAL_CONV
  ``bb_succs empty_deploy_final_block``
val final_fn_name = computeLib.EVAL_CONV ``empty_deploy_final_fn.fn_name``
val final_entry_label = computeLib.EVAL_CONV
  ``fn_entry_label empty_deploy_final_fn``

Theorem empty_deploy_final_fn_wf[local]:
  wf_function empty_deploy_final_fn
Proof
  simp[venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def,
       venomWfTheory.fn_succs_closed_def,
       venomWfTheory.fn_inst_ids_distinct_def,
       venomInstTheory.fn_labels_def,
       empty_deploy_final_blocks_exact,
       empty_deploy_final_block_wf,
       final_block_label, final_block_succs] >>
  rpt strip_tac >>
  gvs[empty_deploy_final_block_wf,
      empty_deploy_final_block_instructions_exact]
QED

Theorem final_fn_inst_wf_from_blocks[local]:
  (!bb. MEM bb fn.fn_blocks ==> EVERY inst_wf bb.bb_instructions) ==>
  fn_inst_wf fn
Proof
  rw[venomWfTheory.fn_inst_wf_def] >>
  first_x_assum drule >> simp[listTheory.EVERY_MEM]
QED

Theorem empty_deploy_final_fn_inst_wf[local]:
  fn_inst_wf empty_deploy_final_fn
Proof
  irule final_fn_inst_wf_from_blocks >>
  simp[empty_deploy_final_blocks_exact] >> rpt strip_tac >>
  gvs[empty_deploy_final_block_insts_wf]
QED

Theorem empty_deploy_final_canonical_params[local]:
  canonical_param_prefix empty_deploy_final_fn
Proof
  simp[callLayoutDefsTheory.canonical_param_prefix_def,
       callLayoutDefsTheory.canonical_entry_params_from_def,
       callLayoutDefsTheory.canonical_after_fmp_def,
       callLayoutDefsTheory.no_param_insts_def,
       callLayoutDefsTheory.param_inst_at_def,
       venomInstTheory.is_param_opcode_def,
       empty_deploy_final_blocks_exact,
       empty_deploy_final_block_instructions_exact]
QED

Theorem empty_deploy_final_ssa_form[local]:
  ssa_form empty_deploy_final_fn
Proof
  simp[venomWfTheory.ssa_form_def,
       venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def,
       empty_deploy_final_blocks_exact,
       empty_deploy_final_block_instructions_exact]
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

Theorem empty_deploy_final_member_self_dominates[local]:
  !bb. MEM bb empty_deploy_final_fn.fn_blocks ==>
    fn_dominates empty_deploy_final_fn bb.bb_label bb.bb_label
Proof
  rpt strip_tac >>
  gvs[empty_deploy_final_blocks_exact] >>
  rewrite_tac[venomWfTheory.fn_dominates_def] >>
  conj_tac
  >- simp[venomWfTheory.fn_reachable_def, final_entry_label, final_block_label] >>
  rpt strip_tac >>
  qpat_x_assum `LAST path = empty_deploy_final_block.bb_label`
    (fn th => rewrite_tac[GSYM th]) >>
  irule rich_listTheory.LAST_MEM >> simp[]
QED


Definition defs_in_prefix_def[local]:
  defs_in_prefix j insts =
    FLAT (MAP (\inst. inst.inst_outputs) (TAKE j insts))
End

Definition indexed_defs_before_uses_def[local]:
  indexed_defs_before_uses insts <=>
    EVERY
      (\j. !v. MEM (Var v) (EL j insts).inst_operands ==>
                MEM v (defs_in_prefix j insts))
      (GENLIST I (LENGTH insts))
End

Theorem empty_deploy_final_indexed_defs_before_uses[local]:
  indexed_defs_before_uses empty_deploy_final_block.bb_instructions
Proof
  simp[indexed_defs_before_uses_def, defs_in_prefix_def,
       empty_deploy_final_block_instructions_exact] >>
  metis_tac[]
QED

val _ = export_theory()
