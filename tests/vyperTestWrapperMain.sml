(* Noninteractive driver for tests/vyper-test-wrappers. *)
val () = load "vyperTestLib";

fun wrapper_main () =
  case OS.Process.getEnv "VYPER_TEST_WRAPPER_MODE" of
      SOME "generate" => vyperTestLib.generate_tests ()
    | SOME "check" => vyperTestLib.check_generated_tests ()
    | SOME mode => raise Fail ("invalid VYPER_TEST_WRAPPER_MODE: " ^ mode)
    | NONE => raise Fail "VYPER_TEST_WRAPPER_MODE is not set";

val () =
  (wrapper_main (); OS.Process.exit OS.Process.success)
  handle e =>
    (TextIO.output (TextIO.stdErr,
       "vyper-test-wrappers: " ^ General.exnMessage e ^ "\n");
     OS.Process.exit OS.Process.failure);
