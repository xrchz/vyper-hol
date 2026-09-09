(*
 * CFG Normalization Pass — Definitions
 *
 * Splits basic blocks when a block has a conditional predecessor
 * (predecessor with >1 successor) to ensure each block has at most
 * one conditional predecessor. Required by the code generator.
 *
 * For each block B with multiple predecessors, if a predecessor P has
 * >1 successor (conditional branch), insert a split block S between P and B:
 *   P → S → B
 * The split block contains:
 *   - Forwarding ASSIGN instructions for PHI operands that need it
 *   - Unconditional JMP to B
 *
 * PHI nodes in B are updated to reference S instead of P.
 *
 * TOP-LEVEL:
 *   needs_forwarding      — does a PHI operand var need a forwarding store?
 *   split_block_name      — generate split block label
 *   build_split_block     — construct the forwarding split block
 *   update_phis_for_split — update PHIs in target to reference split block
 *   insert_split          — perform one split
 *   cfg_norm_fn           — iterated to convergence
 *   cfg_norm_ctx          — transform all functions in context
 *
 * Source: vyper/venom/passes/cfg_normalization.py
 *)

Theory cfgNormDefs
Ancestors
  cfgTransform venomWf venomExecSemantics irSupply

(* ===== Forwarding Store Detection ===== *)

(* Does a variable need a forwarding ASSIGN in the split block?
   True if:
   - var is defined by a PHI in the predecessor, OR
   - var is not defined in the predecessor at all
   Matches Python _needs_forwarding_store. *)
Definition needs_forwarding_def:
  needs_forwarding var pred_bb ⇔
    case FIND (λinst. MEM var inst.inst_outputs) pred_bb.bb_instructions of
      NONE => T
    | SOME inst => inst.inst_opcode = PHI
End

(* ===== Split Block Construction ===== *)

(* Generate split block label.
   Matches Python: f"{pred_bb.label.value}_split_{bb.label.value}" *)
Definition split_block_name_def:
  split_block_name pred_label target_label =
    STRCAT pred_label (STRCAT "_split_" target_label)
End

(* Collect PHI operand variables from target block that come from pred_label
   and need forwarding. *)
Definition phi_vars_needing_forward_def:
  phi_vars_needing_forward pred_label pred_bb [] = [] ∧
  phi_vars_needing_forward pred_label pred_bb (inst::rest) =
    if inst.inst_opcode ≠ PHI then
      phi_vars_needing_forward pred_label pred_bb rest
    else
      let pairs = phi_pairs inst.inst_operands in
      let matching = FILTER (λ(l,v). l = pred_label) pairs in
      let need_fwd = FILTER (λ(l,v). needs_forwarding v pred_bb) matching in
      MAP SND need_fwd ++ phi_vars_needing_forward pred_label pred_bb rest
End

(* Build forwarding ASSIGN instructions.
   Each var that needs forwarding: %new_var = assign %old_var.
   Returns (var_replacements, assign_instructions). *)
Definition build_forwarding_assigns_def:
  build_forwarding_assigns split_label id_base [] = ([], []) ∧
  build_forwarding_assigns split_label id_base (var::vars) =
    let new_var = STRCAT split_label (STRCAT "_fwd_" var) in
    let assign_inst = <|
      inst_id := id_base;
      inst_opcode := ASSIGN;
      inst_operands := [Var var];
      inst_outputs := [new_var]
    |> in
    let (rest_repls, rest_insts) =
      build_forwarding_assigns split_label (id_base + 1) vars in
    ((var, new_var) :: rest_repls, assign_inst :: rest_insts)
End

(* Build the split block: forwarding assigns + JMP to target. *)
Definition build_split_block_def:
  build_split_block pred_bb target_bb id_base =
    let split_label = split_block_name pred_bb.bb_label target_bb.bb_label in
    let fwd_vars = nub (phi_vars_needing_forward
                         pred_bb.bb_label pred_bb target_bb.bb_instructions) in
    let (var_repls, fwd_insts) =
      build_forwarding_assigns split_label id_base fwd_vars in
    let jmp_inst = <|
      inst_id := id_base + LENGTH fwd_vars;
      inst_opcode := JMP;
      inst_operands := [Label target_bb.bb_label];
      inst_outputs := []
    |> in
    let split_bb = <|
      bb_label := split_label;
      bb_instructions := fwd_insts ++ [jmp_inst]
    |> in
    (split_bb, var_repls)
End

(* ===== PHI Update ===== *)

(* Apply variable replacements to PHI operands for a given predecessor.
   Replaces old_label with new_label and applies var substitutions. *)
Definition update_phi_ops_def:
  update_phi_ops old_label new_label var_repls [] = [] ∧
  update_phi_ops old_label new_label var_repls [x] = [x] ∧
  update_phi_ops old_label new_label var_repls (Label l :: val_op :: rest) =
    (if l = old_label then
       let val_op' = case val_op of
                       Var v => (case ALOOKUP var_repls v of
                                   SOME new_v => Var new_v
                                 | NONE => Var v)
                     | other => other
       in
       Label new_label :: val_op' ::
         update_phi_ops old_label new_label var_repls rest
     else
       Label l :: val_op ::
         update_phi_ops old_label new_label var_repls rest) ∧
  update_phi_ops old_label new_label var_repls (x :: y :: rest) =
    x :: y :: update_phi_ops old_label new_label var_repls rest
End

(* Update all PHI instructions in target block for a split. *)
Definition update_phis_for_split_def:
  update_phis_for_split old_label new_label var_repls bb =
    bb with bb_instructions :=
      MAP (λinst.
        if inst.inst_opcode ≠ PHI then inst
        else inst with inst_operands :=
          update_phi_ops old_label new_label var_repls inst.inst_operands)
      bb.bb_instructions
End

(* ===== Single Split Operation ===== *)

(* Perform one split: insert split block between pred_bb and target_bb.
   Python only replaces the label in the PREDECESSOR's terminator,
   not in all blocks. *)
Definition insert_split_def:
  insert_split func pred_bb target_bb id_base =
    let (split_bb, var_repls) =
      build_split_block pred_bb target_bb id_base in
    let split_label = split_bb.bb_label in
    (* Update ONLY predecessor's terminator: target → split *)
    let pred_bb' = subst_label_terminator target_bb.bb_label split_label pred_bb in
    let func1 = func with fn_blocks :=
      replace_block pred_bb.bb_label pred_bb' func.fn_blocks in
    (* Update target's PHIs *)
    let target_bb' = update_phis_for_split
                       pred_bb.bb_label split_label var_repls target_bb in
    let func2 = func1 with fn_blocks :=
      replace_block target_bb.bb_label target_bb' func1.fn_blocks in
    (* Append split block *)
    func2 with fn_blocks := func2.fn_blocks ++ [split_bb]
End

(* ===== One Round ===== *)

(* Find and perform one split. Scans blocks, for each block with >1
   predecessor, checks if any predecessor has >1 successor.
   Returns (updated_fn, changed, updated_id_base). *)
Definition find_and_split_def:
  find_and_split func id_base [] = (func, F, id_base) ∧
  find_and_split func id_base (bb::rest) =
    let preds = block_preds func bb.bb_label in
    if LENGTH preds ≤ 1 then find_and_split func id_base rest
    else
      case FIND (λp. num_succs p > 1) preds of
        NONE => find_and_split func id_base rest
      | SOME pred_bb =>
          let func' = insert_split func pred_bb bb id_base in
          (func', T, id_base + LENGTH bb.bb_instructions + 1)
End

(* One round: find and perform one split. *)
Definition cfg_norm_round_def:
  cfg_norm_round func id_base =
    find_and_split func id_base func.fn_blocks
End

(* ===== Iterated Pass ===== *)

(* Iterate normalization rounds until convergence.
   Python iterates up to num_basic_blocks * 2. *)
Definition cfg_norm_iter_def:
  cfg_norm_iter 0 func id_base = func ∧
  cfg_norm_iter (SUC n) func id_base =
    let (func', changed, id_base') = cfg_norm_round func id_base in
    if changed then cfg_norm_iter n func' id_base'
    else func
End

(* Each split eliminates exactly one critical edge and never creates new ones.
   A function with N blocks has at most 2N edges (each block has ≤ 2 successors),
   so at most 2N critical edges exist. *)
Definition cfg_norm_fn_def:
  cfg_norm_fn func =
    let n = LENGTH func.fn_blocks in
    cfg_norm_iter (2 * n) func 0
End

(* Transform all functions in context. *)
Definition cfg_norm_ctx_def:
  cfg_norm_ctx ctx =
    ctx with ctx_functions := MAP cfg_norm_fn ctx.ctx_functions
End


(* ===== Supply-aware configured transform ===== *)

(* The legacy arithmetic/name-based normalizer above remains available for its
   existing proof development.  Configured callers use this unit-wide supply
   traversal instead. *)
Definition build_forwarding_assigns_supply_def:
  build_forwarding_assigns_supply s [] = ([],[],s) /\
  build_forwarding_assigns_supply s (var::vars) =
    case fresh_ir_var s of (new_var,s1) =>
    case fresh_inst_id s1 of (id,s2) =>
    case build_forwarding_assigns_supply s2 vars of
      (rest_repls,rest_insts,s3) =>
      ((var,new_var)::rest_repls,
       <| inst_id := id; inst_opcode := ASSIGN;
          inst_operands := [Var var]; inst_outputs := [new_var] |>
         :: rest_insts,
       s3)
End

Definition build_split_block_supply_def:
  build_split_block_supply s pred_bb target_bb =
    case fresh_ir_label s of (split_label,s1) =>
    let fwd_vars = nub (phi_vars_needing_forward
                          pred_bb.bb_label pred_bb
                          target_bb.bb_instructions) in
    case build_forwarding_assigns_supply s1 fwd_vars of
      (var_repls,fwd_insts,s2) =>
    case fresh_inst_id s2 of (jmp_id,s3) =>
      (<| bb_label := split_label;
          bb_instructions :=
            fwd_insts ++
            [<| inst_id := jmp_id; inst_opcode := JMP;
                inst_operands := [Label target_bb.bb_label];
                inst_outputs := [] |>] |>,
       var_repls,s3)
End

Definition insert_split_supply_def:
  insert_split_supply s func pred_bb target_bb =
    case build_split_block_supply s pred_bb target_bb of
      (split_bb,var_repls,s1) =>
    let split_label = split_bb.bb_label in
    let pred_bb' =
      subst_label_terminator target_bb.bb_label split_label pred_bb in
    let func1 = func with fn_blocks :=
      replace_block pred_bb.bb_label pred_bb' func.fn_blocks in
    let target_bb' = update_phis_for_split
      pred_bb.bb_label split_label var_repls target_bb in
    let func2 = func1 with fn_blocks :=
      replace_block target_bb.bb_label target_bb' func1.fn_blocks in
      (func2 with fn_blocks := func2.fn_blocks ++ [split_bb],s1)
End

Definition find_and_split_supply_def:
  find_and_split_supply func s [] = (func,F,s) /\
  find_and_split_supply func s (bb::rest) =
    let preds = block_preds func bb.bb_label in
    if LENGTH preds <= 1 then find_and_split_supply func s rest
    else
      case FIND (\p. num_succs p > 1) preds of
        NONE => find_and_split_supply func s rest
      | SOME pred_bb =>
          (case insert_split_supply s func pred_bb bb of (func',s1) =>
             (func',T,s1))
End

Definition cfg_norm_round_supply_def:
  cfg_norm_round_supply s func =
    find_and_split_supply func s func.fn_blocks
End

Definition cfg_norm_iter_supply_def:
  cfg_norm_iter_supply 0 s func = (func,s) /\
  cfg_norm_iter_supply (SUC n) s func =
    case cfg_norm_round_supply s func of (func',changed,s1) =>
      if changed then cfg_norm_iter_supply n s1 func'
      else (func',s1)
End

Definition cfg_norm_function_supply_def:
  cfg_norm_function_supply s func =
    cfg_norm_iter_supply (2 * LENGTH func.fn_blocks) s func
End

Definition cfg_norm_functions_supply_def:
  cfg_norm_functions_supply s [] = ([],s) /\
  cfg_norm_functions_supply s (func::funcs) =
    case cfg_norm_function_supply s func of (func',s1) =>
    case cfg_norm_functions_supply s1 funcs of (funcs',s2) =>
      (func'::funcs',s2)
End

Definition cfg_norm_context_supply_def:
  cfg_norm_context_supply s ctx =
    case cfg_norm_functions_supply s ctx.ctx_functions of (funcs,s1) =>
      (ctx with ctx_functions := funcs,s1)
End

Definition cfg_norm_unit_supply_def:
  cfg_norm_unit_supply s unit =
    case cfg_norm_context_supply s unit.cu_context of (ctx,s1) =>
      (unit with cu_context := ctx,s1)
End

Definition cfg_norm_configured_with_supply_def:
  cfg_norm_configured_with_supply unit =
    cfg_norm_unit_supply (init_ir_supply unit) unit
End

Definition cfg_norm_configured_def:
  cfg_norm_configured unit = FST (cfg_norm_configured_with_supply unit)
End
