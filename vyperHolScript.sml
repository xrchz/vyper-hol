(*
 * Build rollup: depends on all project targets so they are built together.
 *
 * STATUS: This is not a claim that end-to-end compiler correctness is closed.
 * Some imported correctness theories still contain cheats/open obligations.
 * See docs/compiler-proof-status.md and docs/compiler-proof-roadmap.md.
 *)
Theory vyperHol
Ancestors
  (* syntax, frontend, semantics *)
  jsonToVyper
  vyperTestRunner
  vyperEvent
  (* semantics properties *)
  vyperSemanticsHol
  (* compiler passes *)
  venomPassesHol
  (* analysis roll-up *)
  venomAnalysisHol
  (* pipeline + codegen *)
  venomPipelineCorrect
  (* lowering + e2e *)
  vyperLoweringHol
  (* codegen *)
  venomToAsmProps asmToBytecodeProps codegenCorrectness
