structure vyperTestWrapperMainLib :> vyperTestWrapperMainLib = struct

fun generate_or_check () =
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

fun run () = (generate_or_check (); write_selected_count ());

end
