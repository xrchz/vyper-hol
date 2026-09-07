Theory writeCompilerBytecodeFixturesValidation[no_sig_docs]
Ancestors evalCompilerBytecodeDefs evalCompiler
Libs writeCompilerBytecodeFixturesLib

val () = writeCompilerBytecodeFixturesLib.validate_registry ()
val () =
  ((writeCompilerBytecodeFixturesLib.lookup_entry "not-a-fixture";
    raise Fail "unknown fixture selector was accepted")
   handle Fail message =>
     if String.isPrefix "unknown formal O1 fixture name:" message then ()
     else raise Fail message)

val _ = export_theory ()
