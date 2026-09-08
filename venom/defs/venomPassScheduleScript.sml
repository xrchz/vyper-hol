(*
 * Generic configured-pass schedules and the exact Venom O1 schedule data.
 *
 * This theory contains configuration only.  Pass execution and pipeline
 * well-formedness belong to later layers.
 *)

Theory venomPassSchedule
Ancestors
  venomCompilerTypes

Datatype:
  venom_pass_tag =
    VP_ConcretizeMemLoc
  | VP_CFGNormalization
  | VP_DFT
  | VP_DretDesugar
  | VP_FmpLowering
  | VP_LowerDload
  | VP_MakeSSA
  | VP_SimplifyCFG
  | VP_SingleUseExpansion
End

Datatype:
  configured_fn_pass = CFP_Simple venom_pass_tag
End

Datatype:
  pass_constraints = <|
    pc_predecessors : venom_pass_tag list;
    pc_successors : venom_pass_tag list;
    pc_immediate_predecessors : venom_pass_tag list;
    pc_immediate_successors : venom_pass_tag list;
    pc_ordered_after : venom_pass_tag list
  |>
End

Definition fn_pass_tag_def:
  fn_pass_tag (CFP_Simple tag) = tag
End

Definition configured_fn_pass_wf_def:
  configured_fn_pass_wf (CFP_Simple tag) = T
End

(* Nonempty immediate lists denote the allowed tags at the adjacent slot.
 * ordered_after is optional ordering: a named tag may be absent, but it may
 * not occur in the strict suffix of the current pass.
 *)
Definition pass_constraints_hold_def:
  pass_constraints_hold pc prefix suffix <=>
    EVERY (\tag. MEM tag prefix) pc.pc_predecessors /\
    EVERY (\tag. MEM tag suffix) pc.pc_successors /\
    (NULL pc.pc_immediate_predecessors \/
     (~NULL prefix /\ MEM (LAST prefix) pc.pc_immediate_predecessors)) /\
    (NULL pc.pc_immediate_successors \/
     (~NULL suffix /\ MEM (HD suffix) pc.pc_immediate_successors)) /\
    EVERY (\tag. ~MEM tag suffix) pc.pc_ordered_after
End

Definition no_pass_constraints_def:
  no_pass_constraints = <|
    pc_predecessors := [];
    pc_successors := [];
    pc_immediate_predecessors := [];
    pc_immediate_successors := [];
    pc_ordered_after := []
  |>
End

Definition pass_constraints_for_def:
  pass_constraints_for tag =
    case tag of
      VP_ConcretizeMemLoc =>
        no_pass_constraints with
          pc_predecessors := [VP_LowerDload]
    | VP_FmpLowering =>
        no_pass_constraints with <|
          pc_predecessors := [VP_MakeSSA];
          pc_successors := [VP_MakeSSA]
        |>
    | VP_SimplifyCFG =>
        no_pass_constraints with
          pc_predecessors := [VP_MakeSSA]
    | VP_DFT =>
        no_pass_constraints with <|
          pc_predecessors := [VP_SingleUseExpansion];
          pc_immediate_successors := [VP_CFGNormalization]
        |>
    | _ => no_pass_constraints
End

Definition valid_pass_at_def:
  valid_pass_at tags i <=>
    i < LENGTH tags /\
    pass_constraints_hold
      (pass_constraints_for (EL i tags))
      (TAKE i tags)
      (DROP (SUC i) tags)
End

Definition valid_pass_order_def:
  valid_pass_order tags <=>
    EVERY (valid_pass_at tags) (GENLIST I (LENGTH tags))
End

Definition build_fn_pass_pipeline_def:
  build_fn_pass_pipeline passes =
    if EVERY configured_fn_pass_wf passes /\
       valid_pass_order (MAP fn_pass_tag passes)
    then SOME passes
    else NONE
End

Datatype:
  pipeline_stage =
    PS_MapFunctions configured_fn_pass
  | PS_DiscardAnalyses
End

Datatype:
  pipeline_spec = <|
    ps_pre_walk_stages : pipeline_stage list;
    ps_fn_passes : configured_fn_pass list;
    ps_prune_unreachable : bool;
    ps_require_acyclic_calls : bool;
    ps_post_walk_stages : pipeline_stage list;
    ps_final_assembly : final_assembly_policy
  |>
End

Definition o1_fn_passes_def:
  o1_fn_passes =
    [CFP_Simple VP_MakeSSA;
     CFP_Simple VP_LowerDload;
     CFP_Simple VP_ConcretizeMemLoc;
     CFP_Simple VP_FmpLowering;
     CFP_Simple VP_MakeSSA;
     CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
End

Definition o1_pipeline_spec_def:
  o1_pipeline_spec = <|
    ps_pre_walk_stages :=
      [PS_MapFunctions (CFP_Simple VP_SimplifyCFG);
       PS_MapFunctions (CFP_Simple VP_DretDesugar);
       PS_DiscardAnalyses];
    ps_fn_passes := o1_fn_passes;
    ps_prune_unreachable := T;
    ps_require_acyclic_calls := T;
    ps_post_walk_stages := [];
    ps_final_assembly := FAP_Optimize
  |>
End

Theorem build_fn_pass_pipeline_valid:
  build_fn_pass_pipeline requested = SOME passes ==>
  passes = requested /\
  valid_pass_order (MAP fn_pass_tag passes)
Proof
  simp [build_fn_pass_pipeline_def] >>
  strip_tac >>
  gvs []
QED

Theorem o1_fn_pass_order_valid:
  valid_pass_order (MAP fn_pass_tag o1_fn_passes)
Proof
  EVAL_TAC
QED

Theorem o1_build_fn_pass_pipeline:
  build_fn_pass_pipeline o1_fn_passes = SOME o1_fn_passes
Proof
  simp [build_fn_pass_pipeline_def, o1_fn_pass_order_valid,
        o1_fn_passes_def, configured_fn_pass_wf_def]
QED

val _ = export_theory ();
