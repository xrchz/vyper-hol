signature compilerEvalLib = sig

  (* Incremental computation set for bounded function analyses, context-plan
     orchestration, and the mechanical assembly tail. It deliberately contains
     no lowering or O1 pipeline definitions. *)
  val final_codegen_compset : computeLib.compset
  val final_codegen_conv : Conv.conv

end
