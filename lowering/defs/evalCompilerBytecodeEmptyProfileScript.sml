Theory evalCompilerBytecodeEmptyProfile
Ancestors evalCompilerBytecodeEmptySafetyPredicates
          evalCompilerBytecodeEmptyDeploySafetyPredicates
          evalCompilerBytecodeDefs
Libs finite_mapLib computeLib evalCompilerBytecodeLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t

val empty_profile_tm =
  ``formal_o1_ir_no_asm_opt 100000 ([] : toplevel list)``
val empty_profile_outer = computeLib.RESTR_EVAL_CONV
  [``lower_vyper_runtime_unit``,
   ``checked_unit_pipeline_fuel_for_testing``,
   ``lower_vyper_deploy_unit``] empty_profile_tm
val empty_profile_after_runtime_lowering =
  PURE_REWRITE_RULE
    [GSYM evalCompilerBytecodeTheory.empty_prague_rpolicy_def,
     evalCompilerBytecodeTheory.empty_runtime_lowering_exact]
    empty_profile_outer

val _ =
  if has_head ``checked_unit_pipeline_fuel_for_testing``
       (rhs (concl empty_profile_after_runtime_lowering))
  then () else raise Fail "empty profile did not reach checked runtime pipeline"

Theorem exact_empty_profile_after_runtime_lowering[local]:
  ^(concl empty_profile_after_runtime_lowering)
Proof
  ACCEPT_TAC empty_profile_after_runtime_lowering
QED

val runtime_driver =
  evalCompilerBytecodeEmptySafetyPredicatesTheory.exact_empty_runtime_driver_result
val runtime_driver_rhs = rhs (concl runtime_driver)
val _ =
  if head_is ``SOME`` runtime_driver_rhs andalso null (free_vars runtime_driver_rhs)
  then () else raise Fail "exact runtime driver RHS is not closed literal SOME"
val runtime_out_tm = optionSyntax.dest_some runtime_driver_rhs
val _ =
  if null (free_vars runtime_out_tm) then ()
  else raise Fail "exact runtime pipeline output is not closed"
val runtime_unit_projection = computeLib.EVAL_CONV ``(^runtime_out_tm).po_unit``
val runtime_unit_tm = rhs (concl runtime_unit_projection)
val _ =
  if null (free_vars runtime_unit_tm) then ()
  else raise Fail "projected exact runtime unit is not closed"

Theorem exact_empty_runtime_pipeline_output[local]:
  ^(concl runtime_driver)
Proof
  ACCEPT_TAC runtime_driver
QED

Theorem exact_empty_runtime_output_unit[local]:
  ^(concl runtime_unit_projection)
Proof
  ACCEPT_TAC runtime_unit_projection
QED

val runtime_codegen_tm =
  ``codegen_assembly_fuel 100000 empty_prague_rpolicy ^runtime_unit_tm``
val runtime_codegen_partial =
  computeLib.RESTR_EVAL_CONV [``generate_fn_plan_aux_fuel``]
    runtime_codegen_tm
fun is_runtime_planner_redex tm =
  let val (head, args) = strip_comb tm
  in same_const head ``generate_fn_plan_aux_fuel`` andalso length args = 8 end
  handle HOL_ERR _ => false
val runtime_planner_tms =
  find_terms is_runtime_planner_redex
    (rhs (concl runtime_codegen_partial))
val _ =
  if null runtime_planner_tms then
    raise Fail "runtime codegen exposed no planner redexes"
  else if List.all (fn tm => null (free_vars tm)) runtime_planner_tms then ()
  else raise Fail "runtime codegen exposed an open planner redex"
val runtime_planner_eqs =
  map
    (evalCompilerBytecodeLib.closed_fn_plan_aux_success_conv_with_fuels
       [16, 32, 64, 128, 256])
    runtime_planner_tms
val _ =
  if List.all
       (fn th =>
          optionSyntax.is_some (rhs (concl th)) andalso
          null (free_vars (rhs (concl th))))
       runtime_planner_eqs
  then () else raise Fail "lifted runtime planner result is not closed SOME"

Theorem exact_empty_runtime_planners_closed[local]:
  ^(list_mk_conj (map concl runtime_planner_eqs))
Proof
  ACCEPT_TAC (LIST_CONJ runtime_planner_eqs)
QED

val runtime_codegen_planned =
  PURE_REWRITE_RULE runtime_planner_eqs runtime_codegen_partial
val runtime_plan_eq =
  case runtime_planner_eqs of
    [th] => th
  | _ => raise Fail "expected exactly one runtime planner result"
val runtime_plan_tm = optionSyntax.dest_some (rhs (concl runtime_plan_eq))
val _ =
  if null (free_vars runtime_plan_tm) then ()
  else raise Fail "runtime codegen plan is not closed"

Theorem exact_empty_runtime_codegen_plan[local]:
  ^(concl runtime_plan_eq)
Proof
  ACCEPT_TAC runtime_plan_eq
QED

val runtime_context_plan_call =
  ``generate_context_plan_fuel 100000 (^runtime_unit_tm).cu_context``
val runtime_context_plan_partial =
  computeLib.RESTR_EVAL_CONV
    [``generate_fn_plan_aux_fuel``]
    runtime_context_plan_call
val runtime_context_plan_rewritten =
  PURE_REWRITE_RULE runtime_planner_eqs runtime_context_plan_partial
val runtime_context_plan_exact =
  CONV_RULE
    (RAND_CONV
      (SCONV
        [wordsTheory.dimword_def,
         stackPlanTypesTheory.stack_op_in_spill_region_def,
         stackPlanTypesTheory.spill_plan_in_region_def]))
    runtime_context_plan_rewritten
val runtime_context_plan_rhs = rhs (concl runtime_context_plan_exact)
val _ =
  if optionSyntax.is_some runtime_context_plan_rhs andalso
     null (free_vars runtime_context_plan_rhs)
  then () else raise Fail ("runtime context planner result is not closed SOME: " ^
                           term_to_string runtime_context_plan_rhs)
val runtime_context_plan_tm = optionSyntax.dest_some runtime_context_plan_rhs
val _ =
  if null (free_vars runtime_context_plan_tm) andalso
     type_of runtime_context_plan_tm = ``:context_plan``
  then () else raise Fail "runtime context plan payload is not closed context_plan"

Theorem exact_empty_runtime_context_plan[local]:
  generate_context_plan_fuel 100000 (^runtime_unit_tm).cu_context =
    SOME ^runtime_context_plan_tm
Proof
  ACCEPT_TAC runtime_context_plan_exact
QED

val runtime_plan_ops_call =
  ``context_plan_ops ^runtime_context_plan_tm``
val runtime_plan_ops_exact = computeLib.EVAL_CONV runtime_plan_ops_call
val runtime_plan_ops_tm = rhs (concl runtime_plan_ops_exact)
val _ =
  if null (free_vars runtime_plan_ops_tm) andalso
     listSyntax.is_list runtime_plan_ops_tm
  then () else raise Fail "runtime context plan operations are not a closed literal list"

Theorem exact_empty_runtime_context_plan_ops[local]:
  ^runtime_plan_ops_call = ^runtime_plan_ops_tm
Proof
  ACCEPT_TAC runtime_plan_ops_exact
QED

val runtime_assembly_call =
  ``execute_plan (^runtime_context_plan_tm).cp_initial_fmp
      (context_plan_ops ^runtime_context_plan_tm) ++
    data_segment_asm (^runtime_unit_tm).cu_data_segment``
val runtime_data_assembly_exact =
  computeLib.EVAL_CONV
    ``data_segment_asm (^runtime_unit_tm).cu_data_segment``
val runtime_initial_fmp_exact =
  computeLib.EVAL_CONV ``(^runtime_context_plan_tm).cp_initial_fmp``
val runtime_initial_fmp_tm = rhs (concl runtime_initial_fmp_exact)

val (runtime_ops, runtime_op_ty) = listSyntax.dest_list runtime_plan_ops_tm
val _ =
  if length runtime_ops = 29 then ()
  else raise Fail ("expected 29 runtime operations, found " ^
                   Int.toString (length runtime_ops))
fun runtime_ops_slice start count =
  List.take (List.drop (runtime_ops, start), count)
val runtime_ops_chunk1 = runtime_ops_slice 0 6
val runtime_ops_chunk2 = runtime_ops_slice 6 6
val runtime_ops_chunk3 = runtime_ops_slice 12 6
val runtime_ops_chunk4 = runtime_ops_slice 18 6
val runtime_ops_chunk5 = runtime_ops_slice 24 5
val runtime_ops_chunks =
  [runtime_ops_chunk1, runtime_ops_chunk2, runtime_ops_chunk3,
   runtime_ops_chunk4, runtime_ops_chunk5]
val runtime_ops_reconstructed = List.concat runtime_ops_chunks
val _ =
  if map length runtime_ops_chunks = [6, 6, 6, 6, 5] andalso
     length runtime_ops_reconstructed = length runtime_ops andalso
     ListPair.allEq (fn (x, y) => aconv x y)
       (runtime_ops_reconstructed, runtime_ops)
  then () else raise Fail "runtime operation chunk partition is invalid"
val runtime_ops_chunk1_tm = listSyntax.mk_list (runtime_ops_chunk1, runtime_op_ty)
val runtime_ops_chunk2_tm = listSyntax.mk_list (runtime_ops_chunk2, runtime_op_ty)
val runtime_ops_chunk3_tm = listSyntax.mk_list (runtime_ops_chunk3, runtime_op_ty)
val runtime_ops_chunk4_tm = listSyntax.mk_list (runtime_ops_chunk4, runtime_op_ty)
val runtime_ops_chunk5_tm = listSyntax.mk_list (runtime_ops_chunk5, runtime_op_ty)
val runtime_ops_chunk_tms =
  [runtime_ops_chunk1_tm, runtime_ops_chunk2_tm, runtime_ops_chunk3_tm,
   runtime_ops_chunk4_tm, runtime_ops_chunk5_tm]
val _ =
  if List.all (fn tm => null (free_vars tm) andalso
                        type_of tm = type_of runtime_plan_ops_tm)
       runtime_ops_chunk_tms
  then () else raise Fail "runtime operation chunk is not a closed typed list"
val runtime_ops_partition_rhs =
  ``^runtime_ops_chunk1_tm ++ ^runtime_ops_chunk2_tm ++
    ^runtime_ops_chunk3_tm ++ ^runtime_ops_chunk4_tm ++
    ^runtime_ops_chunk5_tm``
val runtime_ops_partition_reduce =
  PURE_REWRITE_CONV [listTheory.APPEND] runtime_ops_partition_rhs
val _ =
  if aconv (rhs (concl runtime_ops_partition_reduce)) runtime_plan_ops_tm
  then () else raise Fail "runtime operation partition does not reconstruct source list"
val runtime_ops_partition_exact = SYM runtime_ops_partition_reduce

Theorem exact_empty_runtime_ops_partition[local]:
  ^runtime_plan_ops_tm = ^runtime_ops_partition_rhs
Proof
  ACCEPT_TAC runtime_ops_partition_exact
QED

val runtime_ops_chunk1_pair01 = List.take (runtime_ops_chunk1, 2)
val runtime_ops_chunk1_pair01_tm =
  listSyntax.mk_list (runtime_ops_chunk1_pair01, runtime_op_ty)
val _ =
  if length runtime_ops_chunk1_pair01 = 2 andalso
     null (free_vars runtime_ops_chunk1_pair01_tm)
  then () else raise Fail "runtime chunk 1 pair 0-1 is not a closed pair"
val runtime_ops_chunk1_pair01_call =
  ``FLAT
      (MAP (exec_stack_op ^runtime_initial_fmp_tm)
        ^runtime_ops_chunk1_pair01_tm)``
val runtime_ops_chunk1_pair01_calls =
  map (fn op_tm => ``exec_stack_op ^runtime_initial_fmp_tm ^op_tm``)
    runtime_ops_chunk1_pair01
val runtime_ops_chunk1_pair01_op_exacts =
  map computeLib.EVAL_CONV runtime_ops_chunk1_pair01_calls
val runtime_ops_chunk1_pair01_exact =
  PURE_REWRITE_CONV
    (runtime_ops_chunk1_pair01_op_exacts @
     [listTheory.MAP, listTheory.FLAT, listTheory.APPEND])
    runtime_ops_chunk1_pair01_call
val runtime_ops_chunk1_pair01_asm_tm =
  rhs (concl runtime_ops_chunk1_pair01_exact)
val _ =
  if null (free_vars runtime_ops_chunk1_pair01_asm_tm) andalso
     listSyntax.is_list runtime_ops_chunk1_pair01_asm_tm andalso
     type_of runtime_ops_chunk1_pair01_asm_tm = ``:asm_inst list``
  then () else raise Fail "runtime chunk 1 pair 0-1 is not closed literal assembly"

Theorem exact_empty_runtime_ops_chunk1_pair01[local]:
  ^runtime_ops_chunk1_pair01_call = ^runtime_ops_chunk1_pair01_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk1_pair01_exact
QED

val runtime_ops_chunk1_op2_tm = List.nth (runtime_ops_chunk1, 2)
val runtime_ops_chunk1_op2_call =
  ``exec_stack_op ^runtime_initial_fmp_tm ^runtime_ops_chunk1_op2_tm``
val runtime_ops_chunk1_op2_shallow =
  ONCE_REWRITE_CONV [planExecTheory.exec_stack_op_def]
    runtime_ops_chunk1_op2_call
val runtime_ops_chunk1_op2_shallow_rhs =
  rhs (concl runtime_ops_chunk1_op2_shallow)
val _ =
  if null (free_vars runtime_ops_chunk1_op2_tm) andalso
     null (free_vars runtime_ops_chunk1_op2_shallow_rhs) andalso
     not (has_head ``exec_stack_op`` runtime_ops_chunk1_op2_shallow_rhs)
  then () else raise Fail "runtime chunk 1 operation 2 shallow result is not closed"
val _ = print
  ("runtime chunk 1 operation 2: " ^
   term_to_string runtime_ops_chunk1_op2_tm ^ "\nshallow RHS: " ^
   term_to_string runtime_ops_chunk1_op2_shallow_rhs ^ "\n")

Theorem exact_empty_runtime_ops_chunk1_op2_shallow[local]:
  ^runtime_ops_chunk1_op2_call = ^runtime_ops_chunk1_op2_shallow_rhs
Proof
  ACCEPT_TAC runtime_ops_chunk1_op2_shallow
QED

val runtime_ops_chunk1_op2_w2n_call =
  find_head ``w2n`` runtime_ops_chunk1_op2_shallow_rhs

Theorem runtime_ops_chunk1_op2_w2n_exact[local]:
  ^runtime_ops_chunk1_op2_w2n_call = 4
Proof
  simp[wordsTheory.dimword_def]
QED

val runtime_ops_chunk1_op2_after_w2n =
  rhs (concl
    (PURE_REWRITE_CONV [runtime_ops_chunk1_op2_w2n_exact]
      runtime_ops_chunk1_op2_shallow_rhs))
val runtime_ops_chunk1_op2_encode_call =
  find_head ``encode_num_bytes`` runtime_ops_chunk1_op2_after_w2n

Theorem exact_empty_runtime_ops_chunk1_op2_encode[local]:
  ^runtime_ops_chunk1_op2_encode_call = [4w]
Proof
  once_rewrite_tac[asmIRTheory.encode_num_bytes_def] >> simp[] >>
  once_rewrite_tac[asmIRTheory.encode_num_bytes_def] >> simp[]
QED

val runtime_ops_chunk1_op2_residual_exact_th =
  PURE_REWRITE_CONV
    [runtime_ops_chunk1_op2_w2n_exact,
     exact_empty_runtime_ops_chunk1_op2_encode]
    runtime_ops_chunk1_op2_shallow_rhs
val runtime_ops_chunk1_op2_asm_tm =
  rhs (concl runtime_ops_chunk1_op2_residual_exact_th)
val _ =
  if null (free_vars runtime_ops_chunk1_op2_asm_tm) andalso
     listSyntax.is_list runtime_ops_chunk1_op2_asm_tm andalso
     type_of runtime_ops_chunk1_op2_asm_tm = ``:asm_inst list``
  then () else raise Fail "runtime operation 2 residual is not literal assembly"

Theorem runtime_ops_chunk1_op2_residual_exact[local]:
  ^runtime_ops_chunk1_op2_shallow_rhs = ^runtime_ops_chunk1_op2_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk1_op2_residual_exact_th
QED

val runtime_ops_chunk1_op2_exact =
  PURE_REWRITE_RULE [runtime_ops_chunk1_op2_residual_exact]
    runtime_ops_chunk1_op2_shallow
val _ =
  if aconv (lhs (concl runtime_ops_chunk1_op2_exact))
       runtime_ops_chunk1_op2_call andalso
     aconv (rhs (concl runtime_ops_chunk1_op2_exact))
       runtime_ops_chunk1_op2_asm_tm andalso
     null (free_vars (concl runtime_ops_chunk1_op2_exact))
  then () else raise Fail "runtime operation 2 exact theorem has wrong shape"

Theorem exact_empty_runtime_ops_chunk1_op2[local]:
  ^runtime_ops_chunk1_op2_call = ^runtime_ops_chunk1_op2_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk1_op2_exact
QED

val runtime_ops_chunk1_op3_tm = List.nth (runtime_ops_chunk1, 3)
val runtime_ops_chunk1_op3_call =
  ``exec_stack_op ^runtime_initial_fmp_tm ^runtime_ops_chunk1_op3_tm``
val runtime_ops_chunk1_op3_exact =
  computeLib.EVAL_CONV runtime_ops_chunk1_op3_call
val runtime_ops_chunk1_op3_asm_tm = rhs (concl runtime_ops_chunk1_op3_exact)
val _ =
  if null (free_vars runtime_ops_chunk1_op3_tm) andalso
     null (free_vars runtime_ops_chunk1_op3_asm_tm) andalso
     listSyntax.is_list runtime_ops_chunk1_op3_asm_tm andalso
     type_of runtime_ops_chunk1_op3_asm_tm = ``:asm_inst list``
  then () else raise Fail "runtime chunk 1 operation 3 is not closed literal assembly"

Theorem exact_empty_runtime_ops_chunk1_op3[local]:
  ^runtime_ops_chunk1_op3_call = ^runtime_ops_chunk1_op3_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk1_op3_exact
QED

val runtime_ops_chunk1_pair23 =
  List.take (List.drop (runtime_ops_chunk1, 2), 2)
val runtime_ops_chunk1_pair23_tm =
  listSyntax.mk_list (runtime_ops_chunk1_pair23, runtime_op_ty)
val _ =
  if length runtime_ops_chunk1_pair23 = 2 andalso
     aconv (List.nth (runtime_ops_chunk1_pair23, 0))
       runtime_ops_chunk1_op2_tm andalso
     aconv (List.nth (runtime_ops_chunk1_pair23, 1))
       runtime_ops_chunk1_op3_tm andalso
     null (free_vars runtime_ops_chunk1_pair23_tm)
  then () else raise Fail "runtime chunk 1 pair 2-3 is not the expected closed pair"
val runtime_ops_chunk1_pair23_call =
  ``FLAT
      (MAP (exec_stack_op ^runtime_initial_fmp_tm)
        ^runtime_ops_chunk1_pair23_tm)``
val runtime_ops_chunk1_pair23_exact =
  PURE_REWRITE_CONV
    [exact_empty_runtime_ops_chunk1_op2,
     exact_empty_runtime_ops_chunk1_op3,
     listTheory.MAP, listTheory.FLAT, listTheory.APPEND]
    runtime_ops_chunk1_pair23_call
val runtime_ops_chunk1_pair23_asm_tm =
  rhs (concl runtime_ops_chunk1_pair23_exact)
val _ =
  if null (free_vars runtime_ops_chunk1_pair23_asm_tm) andalso
     listSyntax.is_list runtime_ops_chunk1_pair23_asm_tm andalso
     type_of runtime_ops_chunk1_pair23_asm_tm = ``:asm_inst list``
  then () else raise Fail "runtime chunk 1 pair 2-3 is not closed literal assembly"

Theorem exact_empty_runtime_ops_chunk1_pair23[local]:
  ^runtime_ops_chunk1_pair23_call = ^runtime_ops_chunk1_pair23_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk1_pair23_exact
QED


val runtime_ops_chunk1_pair45 =
  List.take (List.drop (runtime_ops_chunk1, 4), 2)
val runtime_ops_chunk1_pair45_tm =
  listSyntax.mk_list (runtime_ops_chunk1_pair45, runtime_op_ty)
val _ =
  if length runtime_ops_chunk1_pair45 = 2 andalso
     null (free_vars runtime_ops_chunk1_pair45_tm)
  then () else raise Fail "runtime chunk 1 pair 4-5 is not a closed pair"
val runtime_ops_chunk1_pair45_call =
  ``FLAT
      (MAP (exec_stack_op ^runtime_initial_fmp_tm)
        ^runtime_ops_chunk1_pair45_tm)``
val runtime_ops_chunk1_pair45_calls =
  map (fn op_tm => ``exec_stack_op ^runtime_initial_fmp_tm ^op_tm``)
    runtime_ops_chunk1_pair45
val runtime_ops_chunk1_pair45_op_exacts =
  map computeLib.EVAL_CONV runtime_ops_chunk1_pair45_calls
val runtime_ops_chunk1_pair45_exact =
  PURE_REWRITE_CONV
    (runtime_ops_chunk1_pair45_op_exacts @
     [listTheory.MAP, listTheory.FLAT, listTheory.APPEND])
    runtime_ops_chunk1_pair45_call
val runtime_ops_chunk1_pair45_asm_tm =
  rhs (concl runtime_ops_chunk1_pair45_exact)
val _ =
  if null (free_vars runtime_ops_chunk1_pair45_asm_tm) andalso
     listSyntax.is_list runtime_ops_chunk1_pair45_asm_tm andalso
     type_of runtime_ops_chunk1_pair45_asm_tm = ``:asm_inst list``
  then () else raise Fail "runtime chunk 1 pair 4-5 is not closed literal assembly"

Theorem exact_empty_runtime_ops_chunk1_pair45[local]:
  ^runtime_ops_chunk1_pair45_call = ^runtime_ops_chunk1_pair45_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk1_pair45_exact
QED

val runtime_ops_chunk1_call =
  ``FLAT
      (MAP (exec_stack_op ^runtime_initial_fmp_tm)
        ^runtime_ops_chunk1_tm)``
val runtime_ops_chunk1_pairs_call =
  ``^runtime_ops_chunk1_pair01_call ++
    ^runtime_ops_chunk1_pair23_call ++
    ^runtime_ops_chunk1_pair45_call``
val runtime_ops_chunk1_call_reduce =
  PURE_REWRITE_CONV
    [listTheory.MAP, listTheory.FLAT, listTheory.APPEND,
     listTheory.APPEND_NIL, listTheory.APPEND_ASSOC]
    runtime_ops_chunk1_call
val runtime_ops_chunk1_pairs_call_reduce =
  PURE_REWRITE_CONV
    [listTheory.MAP, listTheory.FLAT, listTheory.APPEND,
     listTheory.APPEND_NIL, listTheory.APPEND_ASSOC]
    runtime_ops_chunk1_pairs_call
val _ =
  if aconv (rhs (concl runtime_ops_chunk1_call_reduce))
       (rhs (concl runtime_ops_chunk1_pairs_call_reduce))
  then () else raise Fail "runtime chunk 1 pair calls do not reconstruct the full call"
val runtime_ops_chunk1_to_pairs_exact =
  TRANS runtime_ops_chunk1_call_reduce
    (SYM runtime_ops_chunk1_pairs_call_reduce)

val runtime_ops_chunk1_asm_concat_tm =
  ``^runtime_ops_chunk1_pair01_asm_tm ++
    ^runtime_ops_chunk1_pair23_asm_tm ++
    ^runtime_ops_chunk1_pair45_asm_tm``
val runtime_ops_chunk1_pairs_exact =
  PURE_REWRITE_CONV
    [exact_empty_runtime_ops_chunk1_pair01,
     exact_empty_runtime_ops_chunk1_pair23,
     exact_empty_runtime_ops_chunk1_pair45]
    runtime_ops_chunk1_pairs_call
val _ =
  if aconv (rhs (concl runtime_ops_chunk1_pairs_exact))
       runtime_ops_chunk1_asm_concat_tm
  then () else raise Fail "runtime chunk 1 pair equations produced the wrong concatenation"
val runtime_ops_chunk1_asm_reduce =
  PURE_REWRITE_CONV [listTheory.APPEND]
    runtime_ops_chunk1_asm_concat_tm
val runtime_ops_chunk1_asm_tm =
  rhs (concl runtime_ops_chunk1_asm_reduce)
val runtime_ops_chunk1_exact =
  TRANS runtime_ops_chunk1_to_pairs_exact
    (TRANS runtime_ops_chunk1_pairs_exact runtime_ops_chunk1_asm_reduce)
val _ =
  if null (free_vars runtime_ops_chunk1_asm_tm) andalso
     listSyntax.is_list runtime_ops_chunk1_asm_tm andalso
     type_of runtime_ops_chunk1_asm_tm = ``:asm_inst list`` andalso
     aconv (lhs (concl runtime_ops_chunk1_exact)) runtime_ops_chunk1_call andalso
     aconv (rhs (concl runtime_ops_chunk1_exact)) runtime_ops_chunk1_asm_tm
  then () else raise Fail "runtime chunk 1 exact theorem has wrong shape"

Theorem exact_empty_runtime_ops_chunk1[local]:
  FLAT (MAP (exec_stack_op ^runtime_initial_fmp_tm) ^runtime_ops_chunk1_tm) =
  ^runtime_ops_chunk1_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk1_exact
QED

fun mk_runtime_ops_piece label chunk start count =
  let
    val ops = List.take (List.drop (chunk, start), count)
    val ops_tm = listSyntax.mk_list (ops, runtime_op_ty)
    val _ =
      if length ops = count andalso null (free_vars ops_tm)
      then () else raise Fail (label ^ " is not a closed operation piece")
    val call =
      ``FLAT (MAP (exec_stack_op ^runtime_initial_fmp_tm) ^ops_tm)``
    val op_calls =
      map (fn op_tm => ``exec_stack_op ^runtime_initial_fmp_tm ^op_tm``) ops
    val op_exacts = map computeLib.EVAL_CONV op_calls
    val exact =
      PURE_REWRITE_CONV
        (op_exacts @ [listTheory.MAP, listTheory.FLAT, listTheory.APPEND]) call
    val asm_tm = rhs (concl exact)
    val _ =
      if null (free_vars asm_tm) andalso
         listSyntax.is_list asm_tm andalso
         type_of asm_tm = ``:asm_inst list``
      then () else raise Fail (label ^ " is not closed literal assembly")
  in
    {call = call, asm_tm = asm_tm, exact = exact}
  end

fun compose_runtime_ops_chunk3 label chunk_tm
      (call1, asm1, exact1) (call2, asm2, exact2) (call3, asm3, exact3) =
  let
    val call =
      ``FLAT (MAP (exec_stack_op ^runtime_initial_fmp_tm) ^chunk_tm)``
    val pieces_call = ``^call1 ++ ^call2 ++ ^call3``
    val call_reduce =
      PURE_REWRITE_CONV
        [listTheory.MAP, listTheory.FLAT, listTheory.APPEND,
         listTheory.APPEND_NIL, listTheory.APPEND_ASSOC] call
    val pieces_call_reduce =
      PURE_REWRITE_CONV
        [listTheory.MAP, listTheory.FLAT, listTheory.APPEND,
         listTheory.APPEND_NIL, listTheory.APPEND_ASSOC] pieces_call
    val _ =
      if aconv (rhs (concl call_reduce)) (rhs (concl pieces_call_reduce))
      then () else raise Fail (label ^ " pieces do not reconstruct the chunk")
    val to_pieces_exact = TRANS call_reduce (SYM pieces_call_reduce)
    val asm_concat_tm = ``^asm1 ++ ^asm2 ++ ^asm3``
    val pieces_exact =
      PURE_REWRITE_CONV [exact1, exact2, exact3] pieces_call
    val _ =
      if aconv (rhs (concl pieces_exact)) asm_concat_tm
      then () else raise Fail (label ^ " piece equations produced the wrong concatenation")
    val asm_reduce =
      PURE_REWRITE_CONV
        [listTheory.APPEND, listTheory.APPEND_NIL, listTheory.APPEND_ASSOC]
        asm_concat_tm
    val asm_tm = rhs (concl asm_reduce)
    val exact = TRANS to_pieces_exact (TRANS pieces_exact asm_reduce)
    val _ =
      if null (free_vars asm_tm) andalso
         listSyntax.is_list asm_tm andalso
         type_of asm_tm = ``:asm_inst list`` andalso
         aconv (lhs (concl exact)) call andalso
         aconv (rhs (concl exact)) asm_tm
      then () else raise Fail (label ^ " exact theorem has wrong shape")
  in
    {call = call, asm_tm = asm_tm, exact = exact}
  end

val runtime_ops_chunk2_pair01 =
  mk_runtime_ops_piece "runtime chunk 2 pair 0-1" runtime_ops_chunk2 0 2
val runtime_ops_chunk2_pair01_call = #call runtime_ops_chunk2_pair01
val runtime_ops_chunk2_pair01_asm_tm = #asm_tm runtime_ops_chunk2_pair01
val runtime_ops_chunk2_pair01_exact = #exact runtime_ops_chunk2_pair01

Theorem exact_empty_runtime_ops_chunk2_pair01[local]:
  ^runtime_ops_chunk2_pair01_call = ^runtime_ops_chunk2_pair01_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk2_pair01_exact
QED

val runtime_ops_chunk2_pair23 =
  mk_runtime_ops_piece "runtime chunk 2 pair 2-3" runtime_ops_chunk2 2 2
val runtime_ops_chunk2_pair23_call = #call runtime_ops_chunk2_pair23
val runtime_ops_chunk2_pair23_asm_tm = #asm_tm runtime_ops_chunk2_pair23
val runtime_ops_chunk2_pair23_exact = #exact runtime_ops_chunk2_pair23

Theorem exact_empty_runtime_ops_chunk2_pair23[local]:
  ^runtime_ops_chunk2_pair23_call = ^runtime_ops_chunk2_pair23_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk2_pair23_exact
QED

val runtime_ops_chunk2_pair45 =
  mk_runtime_ops_piece "runtime chunk 2 pair 4-5" runtime_ops_chunk2 4 2
val runtime_ops_chunk2_pair45_call = #call runtime_ops_chunk2_pair45
val runtime_ops_chunk2_pair45_asm_tm = #asm_tm runtime_ops_chunk2_pair45
val runtime_ops_chunk2_pair45_exact = #exact runtime_ops_chunk2_pair45

Theorem exact_empty_runtime_ops_chunk2_pair45[local]:
  ^runtime_ops_chunk2_pair45_call = ^runtime_ops_chunk2_pair45_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk2_pair45_exact
QED

val runtime_ops_chunk2_result =
  compose_runtime_ops_chunk3 "runtime chunk 2" runtime_ops_chunk2_tm
    (runtime_ops_chunk2_pair01_call, runtime_ops_chunk2_pair01_asm_tm,
     exact_empty_runtime_ops_chunk2_pair01)
    (runtime_ops_chunk2_pair23_call, runtime_ops_chunk2_pair23_asm_tm,
     exact_empty_runtime_ops_chunk2_pair23)
    (runtime_ops_chunk2_pair45_call, runtime_ops_chunk2_pair45_asm_tm,
     exact_empty_runtime_ops_chunk2_pair45)
val runtime_ops_chunk2_call = #call runtime_ops_chunk2_result
val runtime_ops_chunk2_asm_tm = #asm_tm runtime_ops_chunk2_result
val runtime_ops_chunk2_exact = #exact runtime_ops_chunk2_result

Theorem exact_empty_runtime_ops_chunk2[local]:
  FLAT (MAP (exec_stack_op ^runtime_initial_fmp_tm) ^runtime_ops_chunk2_tm) =
  ^runtime_ops_chunk2_asm_tm
Proof
  ACCEPT_TAC runtime_ops_chunk2_exact
QED

val _ = export_theory()
