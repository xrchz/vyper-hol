signature compilerEvalLib = sig

  (* Incremental computation set for context-plan orchestration and the
     mechanical assembly tail. It deliberately contains no function-planning,
     lowering, analysis, or O1 pipeline definitions. *)
  val final_codegen_compset : computeLib.compset
  val final_codegen_conv : Conv.conv

end
