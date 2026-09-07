Theory evalCompilerBytecodeEmptyResult
Ancestors evalCompilerBytecodeFinalPasses
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val walk = evalCompilerBytecodeFinalPassesTheory.exact_empty_runtime_configured_walk
val walk_tail_tm = rhs (concl walk)
val _ = assert_closed "post-configured-walk runtime tail" walk_tail_tm
val walk_tail = computeLib.EVAL_CONV walk_tail_tm
val walk_result_tm = rhs (concl walk_tail)
val _ =
  if head_is ``SOME`` walk_result_tm then ()
  else raise Fail "post-configured-walk runtime tail is not literal SOME"
val walked_pair_tm = optionSyntax.dest_some walk_result_tm
val (final_unit_tm, final_supply_tm) = pairSyntax.dest_pair walked_pair_tm
val _ = assert_closed "exact final runtime unit" final_unit_tm
val _ = assert_closed "exact final runtime supply" final_supply_tm
val runtime_callee_first_result = TRANS walk walk_tail

Definition empty_runtime_final_unit_def:
  empty_runtime_final_unit = ^final_unit_tm
End

Definition empty_runtime_final_supply_def:
  empty_runtime_final_supply = ^final_supply_tm
End

val runtime_callee_first_named =
  REWRITE_RULE [GSYM empty_runtime_final_unit_def,
                GSYM empty_runtime_final_supply_def]
    runtime_callee_first_result

Theorem exact_empty_runtime_callee_first_result:
  ^(concl runtime_callee_first_named)
Proof
  ACCEPT_TAC runtime_callee_first_named
QED

val functions_th = computeLib.EVAL_CONV
  ``empty_runtime_final_unit.cu_context.ctx_functions``
val functions = fst (listSyntax.dest_list (rhs (concl functions_th)))
val _ = if length functions = 1 then ()
  else raise Fail "exact final runtime unit is not singleton-function"
val final_fn_tm = hd functions

Definition empty_runtime_final_fn_def:
  empty_runtime_final_fn = ^final_fn_tm
End

val functions_named =
  REWRITE_RULE [GSYM empty_runtime_final_fn_def] functions_th

Theorem empty_runtime_final_functions_exact:
  ^(concl functions_named)
Proof
  ACCEPT_TAC functions_named
QED

val blocks_th = computeLib.EVAL_CONV ``empty_runtime_final_fn.fn_blocks``
val blocks = fst (listSyntax.dest_list (rhs (concl blocks_th)))
val _ = if length blocks = 4 then ()
  else raise Fail "exact final runtime function does not have four blocks"
val block0_tm = List.nth (blocks, 0)
val block1_tm = List.nth (blocks, 1)
val block2_tm = List.nth (blocks, 2)
val block3_tm = List.nth (blocks, 3)

Definition empty_runtime_final_block0_def:
  empty_runtime_final_block0 = ^block0_tm
End
Definition empty_runtime_final_block1_def:
  empty_runtime_final_block1 = ^block1_tm
End
Definition empty_runtime_final_block2_def:
  empty_runtime_final_block2 = ^block2_tm
End
Definition empty_runtime_final_block3_def:
  empty_runtime_final_block3 = ^block3_tm
End

val blocks_named = REWRITE_RULE
  [GSYM empty_runtime_final_block0_def, GSYM empty_runtime_final_block1_def,
   GSYM empty_runtime_final_block2_def, GSYM empty_runtime_final_block3_def]
  blocks_th

Theorem empty_runtime_final_blocks_exact:
  ^(concl blocks_named)
Proof
  ACCEPT_TAC blocks_named
QED

fun eval_projection tm = computeLib.EVAL_CONV tm
val block0_insts = eval_projection ``empty_runtime_final_block0.bb_instructions``
val block1_insts = eval_projection ``empty_runtime_final_block1.bb_instructions``
val block2_insts = eval_projection ``empty_runtime_final_block2.bb_instructions``
val block3_insts = eval_projection ``empty_runtime_final_block3.bb_instructions``
val data_segment = eval_projection ``empty_runtime_final_unit.cu_data_segment``
val context_entry = eval_projection ``empty_runtime_final_unit.cu_context.ctx_entry``
val global_reserved = eval_projection
  ``empty_runtime_final_unit.cu_context.ctx_global_reserved``
val final_call_abi = eval_projection ``empty_runtime_final_fn.fn_call_abi``
val final_forced_positions = eval_projection
  ``empty_runtime_final_fn.fn_forced_alloc_positions``
val final_eom = eval_projection ``empty_runtime_final_fn.fn_eom``
val final_fmp_signature = eval_projection ``empty_runtime_final_fn.fn_fmp_signature``

Theorem empty_runtime_final_block0_instructions_exact:
  ^(concl block0_insts)
Proof
  ACCEPT_TAC block0_insts
QED
Theorem empty_runtime_final_block1_instructions_exact:
  ^(concl block1_insts)
Proof
  ACCEPT_TAC block1_insts
QED
Theorem empty_runtime_final_block2_instructions_exact:
  ^(concl block2_insts)
Proof
  ACCEPT_TAC block2_insts
QED
Theorem empty_runtime_final_block3_instructions_exact:
  ^(concl block3_insts)
Proof
  ACCEPT_TAC block3_insts
QED
Theorem empty_runtime_final_data_segment_exact:
  ^(concl data_segment)
Proof
  ACCEPT_TAC data_segment
QED
Theorem empty_runtime_final_context_entry_exact:
  ^(concl context_entry)
Proof
  ACCEPT_TAC context_entry
QED
Theorem empty_runtime_final_global_reserved_exact:
  ^(concl global_reserved)
Proof
  ACCEPT_TAC global_reserved
QED
Theorem empty_runtime_final_call_abi_exact:
  ^(concl final_call_abi)
Proof
  ACCEPT_TAC final_call_abi
QED
Theorem empty_runtime_final_forced_positions_exact:
  ^(concl final_forced_positions)
Proof
  ACCEPT_TAC final_forced_positions
QED
Theorem empty_runtime_final_eom_exact:
  ^(concl final_eom)
Proof
  ACCEPT_TAC final_eom
QED
Theorem empty_runtime_final_fmp_signature_exact:
  ^(concl final_fmp_signature)
Proof
  ACCEPT_TAC final_fmp_signature
QED

val _ = export_theory()
