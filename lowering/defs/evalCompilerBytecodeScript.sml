(*
 * Compiler Bytecode Evaluation Fixtures
 *
 * STATUS: Regression/evaluation support, not core lowering definitions.
 * Compares successful executable compiler output against bytecode fixtures and
 * records known checked-guard rejections as NONE, using EVAL_TAC throughout.
 *)

Theory evalCompilerBytecode
Ancestors evalCompiler compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["bytecode"]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Theorem empty_bytecode_matches_expected:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    ([] : toplevel list) =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "empty.hex")
Proof
  EVAL_TAC
QED

Theorem noop_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    noop_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "noop.hex")
Proof
  EVAL_TAC
QED

Theorem return_uint_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    return_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_uint.hex")
Proof
  EVAL_TAC
QED

Theorem return_arg_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    return_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_arg.hex")
Proof
  EVAL_TAC
QED

Theorem local_uint_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    local_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "local_uint.hex")
Proof
  EVAL_TAC
QED

Theorem add_arg_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    add_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "add_arg.hex")
Proof
  EVAL_TAC
QED

Theorem two_external_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    two_external_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "two_external.hex")
Proof
  EVAL_TAC
QED

Theorem storage_read_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    storage_read_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_read.hex")
Proof
  EVAL_TAC
QED

Theorem storage_write_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    storage_write_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_write.hex")
Proof
  EVAL_TAC
QED

Theorem deploy_storage_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    deploy_storage_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "deploy_storage.hex")
Proof
  EVAL_TAC
QED

Theorem event_log_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "event_log.hex")
Proof
  EVAL_TAC
QED

Theorem indexed_event_log_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    indexed_event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "indexed_event_log.hex")
Proof
  EVAL_TAC
QED

Theorem mixed_event_log_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    mixed_event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_log.hex")
Proof
  EVAL_TAC
QED

Theorem hashmap_read_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    hashmap_read_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_read.hex")
Proof
  EVAL_TAC
QED

Theorem hashmap_write_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    hashmap_write_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_write.hex")
Proof
  EVAL_TAC
QED

Theorem if_bool_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    if_bool_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_bool.hex")
Proof
  EVAL_TAC
QED

Theorem if_join_result_lengths:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    if_join_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_join.hex")
Proof
  EVAL_TAC
QED

(* make_ssa gives these loops header PHIs with loop-body back-edge inputs.
 * def_dominates_uses currently checks those inputs as uses in the header, so
 * their loop-body definitions fail the requirement to dominate that header.
 * The checked O1 pipeline consequently returns NONE before bytecode emission;
 * PHI edge-use dominance is intentionally outside this evaluation-only change. *)
Theorem for_pass_evaluates_to_none:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    for_pass_program = NONE
Proof
  EVAL_TAC
QED

Theorem for_accum_evaluates_to_none:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    for_accum_program = NONE
Proof
  EVAL_TAC
QED

Theorem for_continue_evaluates_to_none:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    for_continue_program = NONE
Proof
  EVAL_TAC
QED

Theorem for_break_evaluates_to_none:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    for_break_program = NONE
Proof
  EVAL_TAC
QED

(* compile_internal_function emits its hidden return PC as PARAM.  The checked
 * call-layout code counts PARAM instructions as user inputs, so
 * invoke_input_arity_ok expects one extra argument and the final
 * fmp_lowered_context_wf guard rejects both internal-call programs.  Emitting
 * RETPC_PARAM instead is a separate lowering-semantics change. *)
Theorem internal_call_evaluates_to_none:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    internal_call_program = NONE
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_evaluates_to_none:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    internal_call_arg_program = NONE
Proof
  EVAL_TAC
QED
