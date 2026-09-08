(* Roll-up theory for all venom analysis infrastructure *)
Theory venomAnalysisHol
Ancestors
  (* shared *)
  venomWf
  venomEffects
  venomInstProps
  (* configured per-function schedule runner and structural guarantees *)
  venomFnScheduleRunnerProps
  memLocDefs
  memLocProps
  (* cfg *)
  cfgAnalysis
  (* fcg: public executable + postorder/correctness interface *)
  fcgAnalysis
  (* dataflow framework *)
  dataflowAnalysis
  (* liveness *)
  livenessAnalysis
  (* dfg *)
  dfgAnalysis
  (* dominators *)
  dominatorAnalysis
  (* base pointer *)
  basePtrAnalysis
  (* conservative FMP reclaim analysis *)
  fmpReclaimProps
  (* available expression *)
  availExprAnalysis
  (* stack order *)
  stackOrderAnalysis
  (* memory alias *)
  memAliasAnalysis
  (* memory SSA *)
  memSSAAnalysis
  (* variable definition *)
  varDefAnalysis
  (* variable range *)
  variableRangeAnalysis
  (* readonly memory args *)
  readonlyMemoryArgsProps
  (* analysis-driven simulation bridge *)
  analysisSimProps
