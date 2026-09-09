(*
 * Canonical per-function pass dispatcher interface.
 *
 * This theory owns the closed heterogeneous result boundary and executable
 * effect contracts.  Schedule iteration and compilation-unit replacement are
 * deliberately outside this layer.
 *)

Theory venomPassDispatcher
Ancestors
  venomPassSchedule fcgDefs lowerDloadDefs irSupply
  makeSsaCurrentDefs singleUseExpansionDefs cfgNormDefs
  simplifyCfgDefs dftDefs dretDesugarDefs concretizeMemLocDefs fmpLowerDefs
Datatype:
  fn_pass_output = <|
    fpo_function : ir_function;
    fpo_label_map : (string # string) list;
    fpo_supply : ir_supply
  |>
End

Type fn_pass_runner =
  ``:resolved_compiler_policy -> configured_fn_pass -> compilation_unit ->
     ir_supply -> ir_function -> fn_pass_output option``

(* These classifications are data, rather than comments, so later scheduler
 * validation can inspect the exact exceptional fields without unfolding the
 * dispatcher or any pass implementation. *)
Datatype:
  fn_metadata_effect =
    FME_PreserveStaticInput
  | FME_ClearForcedAllocPositions
End

Datatype:
  fn_static_layout_effect =
    FSLE_Preserve
  | FSLE_Concretize
  | FSLE_InvalidateOnDload
End

Datatype:
  fn_abi_effect =
    FAE_PreserveFmpConvention
  | FAE_InstallFmpConvention
End

Datatype:
  global_reservation_effect =
    GRE_Irrelevant
  | GRE_ReadCurrentUnit
End

Definition fn_pass_metadata_effect_def:
  fn_pass_metadata_effect tag =
    case tag of
      VP_ConcretizeMemLoc => FME_ClearForcedAllocPositions
    | VP_CFGNormalization => FME_PreserveStaticInput
    | VP_DFT => FME_PreserveStaticInput
    | VP_DretDesugar => FME_PreserveStaticInput
    | VP_FmpLowering => FME_PreserveStaticInput
    | VP_LowerDload => FME_PreserveStaticInput
    | VP_MakeSSA => FME_PreserveStaticInput
    | VP_SimplifyCFG => FME_PreserveStaticInput
    | VP_SingleUseExpansion => FME_PreserveStaticInput
End

Definition fn_pass_static_layout_effect_def:
  fn_pass_static_layout_effect tag =
    case tag of
      VP_ConcretizeMemLoc => FSLE_Concretize
    | VP_CFGNormalization => FSLE_Preserve
    | VP_DFT => FSLE_Preserve
    | VP_DretDesugar => FSLE_Preserve
    | VP_FmpLowering => FSLE_Preserve
    | VP_LowerDload => FSLE_InvalidateOnDload
    | VP_MakeSSA => FSLE_Preserve
    | VP_SimplifyCFG => FSLE_Preserve
    | VP_SingleUseExpansion => FSLE_Preserve
End

Definition fn_pass_abi_effect_def:
  fn_pass_abi_effect tag =
    case tag of
      VP_ConcretizeMemLoc => FAE_PreserveFmpConvention
    | VP_CFGNormalization => FAE_PreserveFmpConvention
    | VP_DFT => FAE_PreserveFmpConvention
    | VP_DretDesugar => FAE_PreserveFmpConvention
    | VP_FmpLowering => FAE_InstallFmpConvention
    | VP_LowerDload => FAE_PreserveFmpConvention
    | VP_MakeSSA => FAE_PreserveFmpConvention
    | VP_SimplifyCFG => FAE_PreserveFmpConvention
    | VP_SingleUseExpansion => FAE_PreserveFmpConvention
End

Definition fn_pass_global_reservation_effect_def:
  fn_pass_global_reservation_effect tag =
    case tag of
      VP_ConcretizeMemLoc => GRE_ReadCurrentUnit
    | VP_CFGNormalization => GRE_Irrelevant
    | VP_DFT => GRE_Irrelevant
    | VP_DretDesugar => GRE_Irrelevant
    | VP_FmpLowering => GRE_Irrelevant
    | VP_LowerDload => GRE_Irrelevant
    | VP_MakeSSA => GRE_Irrelevant
    | VP_SimplifyCFG => GRE_Irrelevant
    | VP_SingleUseExpansion => GRE_Irrelevant
End

Definition fn_metadata_effect_holds_def:
  fn_metadata_effect_holds tag before after <=>
    fn_identity_metadata_eq after before /\
    case fn_pass_metadata_effect tag of
      FME_PreserveStaticInput => fn_static_input_eq after before
    | FME_ClearForcedAllocPositions =>
        after.fn_forced_alloc_positions = FEMPTY
End

Definition fn_static_layout_effect_holds_def:
  fn_static_layout_effect_holds tag before after <=>
    case fn_pass_static_layout_effect tag of
      FSLE_Preserve => fn_static_layout_eq after before
    | FSLE_Concretize => IS_SOME after.fn_eom
    | FSLE_InvalidateOnDload =>
        after.fn_eom =
          if lower_dload_invalidates_layout before then NONE else before.fn_eom
End

Definition fn_abi_effect_holds_def:
  fn_abi_effect_holds tag before after <=>
    after.fn_call_abi = before.fn_call_abi /\
    case fn_pass_abi_effect tag of
      FAE_PreserveFmpConvention => fn_fmp_convention_eq after before
    | FAE_InstallFmpConvention => IS_SOME after.fn_fmp_signature
End

(* A function result cannot mutate its compilation unit.  This contract makes
 * the sole permitted reservation dependency explicit: concretization reads
 * the reservation list from the current unit; every other tag is independent
 * of it.  The implementation equations establish that dependency directly. *)
Definition fn_global_reservation_effect_holds_def:
  fn_global_reservation_effect_holds tag unit reserved <=>
    case fn_pass_global_reservation_effect tag of
      GRE_Irrelevant => reserved = []
    | GRE_ReadCurrentUnit => reserved = unit.cu_context.ctx_global_reserved
End

Definition fn_pass_effects_hold_def:
  fn_pass_effects_hold tag before out <=>
    fn_metadata_effect_holds tag before out.fpo_function /\
    fn_static_layout_effect_holds tag before out.fpo_function /\
    fn_abi_effect_holds tag before out.fpo_function
End

Definition introduces_no_invoke_edges_def:
  introduces_no_invoke_edges before after <=>
    EVERY
      (\target. MEM target (MAP FST (fcg_scan_function before)))
      (MAP FST (fcg_scan_function after))
End

Definition execute_configured_fn_pass_def:
  execute_configured_fn_pass rpolicy (CFP_Simple tag) unit s fn =
    case tag of
      VP_ConcretizeMemLoc =>
        (case concretize_function_eval
                unit.cu_context.ctx_global_reserved fn of
           NONE => NONE
         | SOME fn' => SOME <| fpo_function := fn';
                              fpo_label_map := [];
                              fpo_supply := s |>)
    | VP_CFGNormalization =>
        (case cfg_norm_function_supply s fn of
           (fn',s') => SOME <| fpo_function := fn';
                              fpo_label_map := [];
                              fpo_supply := s' |>)
    | VP_DFT =>
        SOME <| fpo_function := dft_fn fn;
                fpo_label_map := [];
                fpo_supply := s |>
    | VP_DretDesugar =>
        (case dret_desugar_function rpolicy.rpol_target s fn of
           NONE => NONE
         | SOME (fn',s') => SOME <| fpo_function := fn';
                                  fpo_label_map := [];
                                  fpo_supply := s' |>)
    | VP_FmpLowering =>
        (case fmp_lower_function unit.cu_context s fn of
           NONE => NONE
         | SOME (fn',s') => SOME <| fpo_function := fn';
                                  fpo_label_map := [];
                                  fpo_supply := s' |>)
    | VP_LowerDload =>
        (case lower_dload_function_supply s fn of
           (fn',s') => SOME <| fpo_function := fn';
                              fpo_label_map := [];
                              fpo_supply := s' |>)
    | VP_MakeSSA =>
        (case make_ssa_current_fn s fn of
           (fn',s') => SOME <| fpo_function := fn';
                              fpo_label_map := [];
                              fpo_supply := s' |>)
    | VP_SimplifyCFG =>
        (case simplify_cfg_fn_with_labels fn of
           (fn',labels) => SOME <| fpo_function := fn';
                                  fpo_label_map := labels;
                                  fpo_supply := s |>)
    | VP_SingleUseExpansion =>
        (case sue_expand_function_supply s fn of
           (fn',s') => SOME <| fpo_function := fn';
                              fpo_label_map := [];
                              fpo_supply := s' |>)
End

Theorem execute_configured_fn_pass_concretize[simp]:
  execute_configured_fn_pass rpolicy
    (CFP_Simple VP_ConcretizeMemLoc) unit s fn =
  case concretize_function_eval unit.cu_context.ctx_global_reserved fn of
    NONE => NONE
  | SOME fn' => SOME <| fpo_function := fn'; fpo_label_map := [];
                        fpo_supply := s |>
Proof
  simp[execute_configured_fn_pass_def]
QED

Theorem execute_configured_fn_pass_cfg_normalization[simp]:
  execute_configured_fn_pass rpolicy
    (CFP_Simple VP_CFGNormalization) unit s fn =
  case cfg_norm_function_supply s fn of
    (fn',s') => SOME <| fpo_function := fn'; fpo_label_map := [];
                       fpo_supply := s' |>
Proof
  simp[execute_configured_fn_pass_def]
QED

Theorem execute_configured_fn_pass_dft[simp]:
  execute_configured_fn_pass rpolicy (CFP_Simple VP_DFT) unit s fn =
  SOME <| fpo_function := dft_fn fn; fpo_label_map := [];
          fpo_supply := s |>
Proof
  simp[execute_configured_fn_pass_def]
QED

Theorem execute_configured_fn_pass_dret[simp]:
  execute_configured_fn_pass rpolicy
    (CFP_Simple VP_DretDesugar) unit s fn =
  case dret_desugar_function rpolicy.rpol_target s fn of
    NONE => NONE
  | SOME (fn',s') => SOME <| fpo_function := fn'; fpo_label_map := [];
                             fpo_supply := s' |>
Proof
  simp[execute_configured_fn_pass_def]
QED

Theorem execute_configured_fn_pass_fmp[simp]:
  execute_configured_fn_pass rpolicy
    (CFP_Simple VP_FmpLowering) unit s fn =
  case fmp_lower_function unit.cu_context s fn of
    NONE => NONE
  | SOME (fn',s') => SOME <| fpo_function := fn'; fpo_label_map := [];
                             fpo_supply := s' |>
Proof
  simp[execute_configured_fn_pass_def]
QED

Theorem execute_configured_fn_pass_lower_dload[simp]:
  execute_configured_fn_pass rpolicy
    (CFP_Simple VP_LowerDload) unit s fn =
  case lower_dload_function_supply s fn of
    (fn',s') => SOME <| fpo_function := fn'; fpo_label_map := [];
                       fpo_supply := s' |>
Proof
  simp[execute_configured_fn_pass_def]
QED

Theorem execute_configured_fn_pass_make_ssa[simp]:
  execute_configured_fn_pass rpolicy
    (CFP_Simple VP_MakeSSA) unit s fn =
  case make_ssa_current_fn s fn of
    (fn',s') => SOME <| fpo_function := fn'; fpo_label_map := [];
                       fpo_supply := s' |>
Proof
  simp[execute_configured_fn_pass_def]
QED

Theorem execute_configured_fn_pass_simplify_cfg[simp]:
  execute_configured_fn_pass rpolicy
    (CFP_Simple VP_SimplifyCFG) unit s fn =
  case simplify_cfg_fn_with_labels fn of
    (fn',labels) => SOME <| fpo_function := fn'; fpo_label_map := labels;
                           fpo_supply := s |>
Proof
  simp[execute_configured_fn_pass_def]
QED

Theorem execute_configured_fn_pass_sue[simp]:
  execute_configured_fn_pass rpolicy
    (CFP_Simple VP_SingleUseExpansion) unit s fn =
  case sue_expand_function_supply s fn of
    (fn',s') => SOME <| fpo_function := fn'; fpo_label_map := [];
                       fpo_supply := s' |>
Proof
  simp[execute_configured_fn_pass_def]
QED

val _ = export_theory ();
