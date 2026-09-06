(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps
  valueEncodingProofs
  (* compiler + correctness *)
  vyperCompiler
  vyperLoweringCorrect
  configuredE2ECorrectness
