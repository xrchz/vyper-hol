signature compilerEvalLib = sig

  (* Minimal computation set for the mechanical stack-plan and assembly tail
     of the compiler.  It deliberately contains no lowering, analysis, or O1
     pipeline definitions. *)
  val final_codegen_compset : computeLib.compset
  val final_codegen_conv : Conv.conv

end
