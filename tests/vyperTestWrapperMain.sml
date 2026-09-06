(* Noninteractive driver for tests/vyper-test-wrappers. *)
val () = load "vyperTestLib";

fun wrapper_main () =
  case OS.Process.getEnv "VYPER_TEST_WRAPPER_MODE" of
      SOME "generate" => vyperTestLib.generate_tests ()
    | SOME "check" => vyperTestLib.check_generated_tests ()
    | SOME mode => raise Fail ("invalid VYPER_TEST_WRAPPER_MODE: " ^ mode)
    | NONE => raise Fail "VYPER_TEST_WRAPPER_MODE is not set";

fun write_selected_count () =
  case OS.Process.getEnv "VYPER_TEST_WRAPPER_COUNT_FILE" of
      NONE => raise Fail "VYPER_TEST_WRAPPER_COUNT_FILE is not set"
    | SOME path => let
        val output = TextIO.openOut path
        val () = TextIO.output
          (output, Int.toString (vyperTestLib.selected_test_count ()) ^ "\n")
        val () = TextIO.closeOut output
      in
        ()
      end;

val () =
  (wrapper_main (); write_selected_count (); OS.Process.exit OS.Process.success)
  handle e =>
    (TextIO.output (TextIO.stdErr,
       "vyper-test-wrappers: " ^ General.exnMessage e ^ "\n");
     OS.Process.exit OS.Process.failure);
