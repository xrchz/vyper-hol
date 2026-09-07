Theory evalCompilerBytecodeSimplifyCfgProbe
Ancestors evalCompilerBytecodeStageProbe

open HolKernel Parse boolLib bossLib

Theorem imported_first_simplify_cfg_operation_unfold:
  !fn.
    simplify_cfg_fn_with_labels fn =
      simplify_cfg_iter_with_labels (LENGTH fn.fn_blocks) fn
Proof
  ACCEPT_TAC
    evalCompilerBytecodeStageProbeTheory.first_simplify_cfg_operation_unfold
QED

val _ = export_theory()
