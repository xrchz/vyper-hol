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
  (* fcg *)
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


(* Structural analyses consume instruction metadata uniformly; this executable
   boundary check guards representative extended opcodes against special-case
   omissions. *)
Theorem task011_structural_analysis_eval:
  let dret = mk_inst 1 DRET [Var "retbuf"; Label "exit"] [] in
  let invoke = mk_inst 2 INVOKE [Var "arg"] ["result"] in
  let param = mk_inst 3 PARAM [Var "p_src"] ["p"] in
  let fmp_param = mk_inst 4 FMP_PARAM [Var "fmp_src"] ["fmp"] in
  let retpc_param = mk_inst 5 RETPC_PARAM [Var "pc_src"] ["pc"] in
    dfg_get_uses (dfg_add_inst dfg_empty dret) "retbuf" = [dret] /\
    dfg_get_uses (dfg_add_inst dfg_empty invoke) "arg" = [invoke] /\
    dfg_get_def (dfg_add_inst dfg_empty invoke) "result" = SOME invoke /\
    dfg_get_uses (dfg_add_inst dfg_empty param) "p_src" = [param] /\
    dfg_get_def (dfg_add_inst dfg_empty param) "p" = SOME param /\
    dfg_get_uses (dfg_add_inst dfg_empty fmp_param) "fmp_src" = [fmp_param] /\
    dfg_get_def (dfg_add_inst dfg_empty fmp_param) "fmp" = SOME fmp_param /\
    dfg_get_uses (dfg_add_inst dfg_empty retpc_param) "pc_src" = [retpc_param] /\
    dfg_get_def (dfg_add_inst dfg_empty retpc_param) "pc" = SOME retpc_param /\
    liveness_transfer [] dret ["live"] = ["live"; "retbuf"] /\
    get_successors dret = ["exit"] /\
    get_successors invoke = [] /\
    MAP is_param_opcode [PARAM; FMP_PARAM; RETPC_PARAM] = [T; T; T]
Proof
  EVAL_TAC
QED
