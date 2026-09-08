(*
 * Compiler Bytecode Evaluation Fixtures
 *
 * STATUS: Regression/evaluation support, not core lowering definitions.
 * Compares executable compiler output against bytecode fixture files using
 * EVAL_TAC and evalCompilerBytecodeLib.
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
  compile_vyper ([] : toplevel list)
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "empty.hex")
Proof
  EVAL_TAC
QED

Theorem noop_result_lengths:
  compile_vyper noop_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "noop.hex")
Proof
  EVAL_TAC
QED

Theorem return_uint_result_lengths:
  compile_vyper return_uint_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_uint.hex")
Proof
  EVAL_TAC
QED

Theorem return_arg_result_lengths:
  compile_vyper return_arg_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_arg.hex")
Proof
  EVAL_TAC
QED

Theorem local_uint_result_lengths:
  compile_vyper local_uint_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "local_uint.hex")
Proof
  EVAL_TAC
QED

Theorem add_arg_result_lengths:
  compile_vyper add_arg_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "add_arg.hex")
Proof
  EVAL_TAC
QED

Theorem two_external_result_lengths:
  compile_vyper two_external_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "two_external.hex")
Proof
  EVAL_TAC
QED

Theorem storage_read_result_lengths:
  compile_vyper storage_read_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_read.hex")
Proof
  EVAL_TAC
QED

Theorem storage_write_result_lengths:
  compile_vyper storage_write_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_write.hex")
Proof
  EVAL_TAC
QED

Theorem deploy_storage_result_lengths:
  compile_vyper deploy_storage_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "deploy_storage.hex")
Proof
  EVAL_TAC
QED

Theorem event_log_result_lengths:
  compile_vyper event_log_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "event_log.hex")
Proof
  EVAL_TAC
QED

Theorem indexed_event_log_result_lengths:
  compile_vyper indexed_event_log_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "indexed_event_log.hex")
Proof
  EVAL_TAC
QED

Theorem mixed_event_log_result_lengths:
  compile_vyper mixed_event_log_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_log.hex")
Proof
  EVAL_TAC
QED

Theorem hashmap_read_result_lengths:
  compile_vyper hashmap_read_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_read.hex")
Proof
  EVAL_TAC
QED

Theorem hashmap_write_result_lengths:
  compile_vyper hashmap_write_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_write.hex")
Proof
  EVAL_TAC
QED

Theorem if_bool_result_lengths:
  compile_vyper if_bool_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_bool.hex")
Proof
  EVAL_TAC
QED

Theorem if_join_result_lengths:
  compile_vyper if_join_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_join.hex")
Proof
  EVAL_TAC
QED

Theorem for_pass_result_lengths:
  compile_vyper for_pass_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_pass.hex")
Proof
  EVAL_TAC
QED

Theorem for_accum_result_lengths:
  compile_vyper for_accum_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_accum.hex")
Proof
  EVAL_TAC
QED

Theorem for_continue_result_lengths:
  compile_vyper for_continue_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_continue.hex")
Proof
  EVAL_TAC
QED

Theorem for_break_result_lengths:
  compile_vyper for_break_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_break.hex")
Proof
  EVAL_TAC
QED

Theorem internal_call_result_lengths:
  compile_vyper internal_call_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call.hex")
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_result_lengths:
  compile_vyper internal_call_arg_program
    concretize_context_eval Linear =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call_arg.hex")
Proof
  EVAL_TAC
QED
