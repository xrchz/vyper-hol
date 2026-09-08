(*
 * Stack Plan Generation — Per-Instruction/Block/Function
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Port of _generate_evm_for_instruction, _generate_evm_for_basicblock_r,
 * generate_evm_assembly from venom_to_assembly.py.
 *
 * TOP-LEVEL:
 *   generate_context_plan — plan for entire venom_context
 *   generate_context_plan_fuel — bounded evaluator variant
 *)

Theory stackPlanGen
Ancestors
  stackPlanOps livenessDefs cfgDefs venomWf passSharedDefs staticLayoutDefs
  callLayoutDefs list relation pair pred_set arithmetic

(* =========================================================================
   Emit Input Operands
   Port of _emit_input_operands
   ========================================================================= *)

Definition emit_one_input_def:
  emit_one_input opc next_liveness op ps =
    (* Restore if spilled *)
    let (restore_ops, ps1) =
      if is_var_operand op ∧ IS_SOME (FLOOKUP ps.ps_spilled op)
      then do_restore op ps
      else ([] : stack_op list, ps) in
    (* Push labels/literals, or dup live vars *)
    case op of
      Label l =>
        let ps2 = ps1 with ps_stack := stack_push op ps1.ps_stack in
        if opc ≠ INVOKE then
          (restore_ops ++ [SOPushLabel l], ps2)
        else (restore_ops, ps2)
    | Lit v =>
        (restore_ops ++ [SOPush (Lit v)],
         ps1 with ps_stack := stack_push op ps1.ps_stack)
    | Var v =>
        if MEM v next_liveness then
          case stack_get_depth op ps1.ps_stack of
            SOME dist =>
              let (dup_ops, ps2) = do_dup dist ps1 in
              (restore_ops ++ dup_ops, ps2)
          | NONE => (restore_ops, ps1)
        else (restore_ops, ps1)
End

Definition emit_input_plan_def:
  emit_input_plan opc [] next_liveness ps = ([] : stack_op list, ps) /\
  emit_input_plan opc (op :: rest) next_liveness ps =
    let (step_ops, ps1) =
      emit_one_input opc (operand_vars rest ++ next_liveness) op ps in
    let (rest_ops, ps2) = emit_input_plan opc rest next_liveness ps1 in
      (step_ops ++ rest_ops, ps2)
End

Theorem emit_input_plan_nil[simp]:
  !opc next_liveness ps.
    emit_input_plan opc [] next_liveness ps = ([], ps)
Proof
  simp[emit_input_plan_def]
QED

Theorem emit_input_plan_cons:
  !opc op rest next_liveness ps.
    emit_input_plan opc (op :: rest) next_liveness ps =
      let (step_ops, ps1) =
        emit_one_input opc (operand_vars rest ++ next_liveness) op ps in
      let (rest_ops, ps2) = emit_input_plan opc rest next_liveness ps1 in
        (step_ops ++ rest_ops, ps2)
Proof
  simp[emit_input_plan_def]
QED

Theorem emit_input_plan_one:
  !opc op next_liveness ps.
    emit_input_plan opc [op] next_liveness ps =
      emit_one_input opc next_liveness op ps
Proof
  rpt gen_tac >>
  simp[emit_input_plan_def, venomInstTheory.operand_vars_def,
       dfgDefsTheory.operand_vars_def] >>
  Cases_on `emit_one_input opc next_liveness op ps` >> simp[]
QED

Theorem emit_input_plan_two:
  !opc op1 op2 next_liveness ps.
    emit_input_plan opc [op1; op2] next_liveness ps =
      let (ops1, ps1) =
        emit_one_input opc (operand_vars [op2] ++ next_liveness) op1 ps in
      let (ops2, ps2) = emit_one_input opc next_liveness op2 ps1 in
        (ops1 ++ ops2, ps2)
Proof
  rpt gen_tac >>
  simp[emit_input_plan_def] >>
  Cases_on `emit_one_input opc (operand_vars [op2] ++ next_liveness) op1 ps` >>
  Cases_on `emit_one_input opc next_liveness op2 r` >>
  simp[venomInstTheory.operand_vars_def, dfgDefsTheory.operand_vars_def]
QED

(* =========================================================================
   Optimistic Swap
   Port of _optimistic_swap
   ========================================================================= *)

Definition optimistic_swap_plan_def:
  optimistic_swap_plan dfg inst next_liveness next_is_terminator ps =
    (* Python: skip if next instruction is a basic block terminator *)
    if next_is_terminator then ([] : stack_op list, ps)
    else if inst.inst_outputs = [] then ([], ps)
    else if next_liveness = [] then ([], ps)
    else
      let next_scheduled = LAST next_liveness in
      let current_top = LAST inst.inst_outputs in
      if operand_equiv dfg (Var current_top) (Var next_scheduled)
      then ([], ps)
      else
        case stack_get_depth (Var next_scheduled) ps.ps_stack of
          NONE => ([], ps)
        | SOME dist => do_swap dist ps
End

(* =========================================================================
   Phi Handling
   ========================================================================= *)

Definition generate_phi_plan_def:
  generate_phi_plan inst next_liveness ps =
    let phi_vars = FILTER is_var_operand inst.inst_operands in
    case stack_get_phi_depth phi_vars ps.ps_stack of
      NONE => ([] : stack_op list, ps)
    | SOME dist =>
        let at_depth = stack_peek dist ps.ps_stack in
        let ret = Var (HD inst.inst_outputs) in
        if MEM (operand_to_string at_depth) next_liveness then
          let (dup_ops, ps') = do_dup dist ps in
          let ps'' = ps' with ps_stack :=
            stack_poke 0 ret ps'.ps_stack in
          (dup_ops ++ [SOPoke 0 ret], ps'')
        else
          let ps' = ps with ps_stack :=
            stack_poke dist ret ps.ps_stack in
          ([SOPoke dist ret], ps')
End

(* =========================================================================
   Offset Handling
   ========================================================================= *)

Definition generate_offset_plan_def:
  generate_offset_plan inst ps =
    let ofst_val = HD inst.inst_operands in
    let label_op = EL 1 inst.inst_operands in
    let n = case ofst_val of Lit v => w2n v | _ => 0 in
    let ret = Var (HD inst.inst_outputs) in
    case label_op of
      Label l =>
        ([SOPushOfst l n],
         ps with ps_stack := stack_push ret ps.ps_stack)
    | _ => ([] : stack_op list, ps)
End

(* =========================================================================
   Emit EVM Opcode(s)
   Per-opcode emission logic.
   ========================================================================= *)

Definition bump_round_word_def:
  bump_round_word (sz:bytes32) =
    word_lsl (word_lsr (sz + 31w) 5) 5
End

Definition bump_emit_ops_def:
  bump_emit_ops =
    [SOPush (Lit 31w); SOEmit "ADD";
     SOPush (Lit 5w); SOEmit "SHR";
     SOPush (Lit 5w); SOEmit "SHL";
     SODup 2; SOEmit "ADD"]
End

Definition generate_emit_ops_def:
  generate_emit_ops inst log_topic_count ps =
    let opc = inst.inst_opcode in
    if opc = INITIAL_FMP then ([SOInitialFmp], ps)
    else if opc = BUMP then (bump_emit_ops, ps)
    else case venom_to_evm_name opc of
      SOME name => ([SOEmit name], ps)
    | NONE =>
        if opc = JNZ then
          let labels = FILTER is_label_operand inst.inst_operands in
          (case labels of
            [Label if_nz; Label if_z] =>
              ([SOPushLabel if_nz; SOEmit "JUMPI";
                SOPushLabel if_z; SOEmit "JUMP"], ps)
          | _ => ([] : stack_op list, ps))
        else if opc = JMP then
          (case inst.inst_operands of
            [Label target] => ([SOPushLabel target; SOEmit "JUMP"], ps)
          | _ => ([], ps))
        else if opc = DJMP then ([SOEmit "JUMP"], ps)
        else if opc = INVOKE then
          (case HD inst.inst_operands of
            Label l =>
              let (ret_lbl, ps') = fresh_label "return_label" ps in
              ([SOPushLabel ret_lbl; SOPushLabel l;
                SOEmit "JUMP"; SOLabel ret_lbl], ps')
          | _ => ([], ps))
        else if opc = RET then ([SOEmit "JUMP"], ps)
        else if opc = ASSERT then
          ([SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"], ps)
        else if opc = ASSERT_UNREACHABLE then
          let (end_lbl, ps') = fresh_label "reachable" ps in
          ([SOPushLabel end_lbl; SOEmit "JUMPI";
            SOEmit "INVALID"; SOLabel end_lbl], ps')
        else if opc = LOG then
          ([SOEmit ("LOG" ++ num_to_dec_string log_topic_count)], ps)
        else if opc = ISTORE then
          ([SOEmit "SWAP1"; SOEmit "MSTORE"], ps)
        else ([], ps)
End

(* =========================================================================
   Compute Operands for an Instruction
   Which operands go to the stack (excludes labels for control flow ops)
   ========================================================================= *)

Definition compute_operands_def:
  compute_operands inst =
    let opc = inst.inst_opcode in
    if MEM opc [JMP; DJMP; JNZ; INVOKE] then
      get_non_label_operands inst
    else if opc = LOG then
      TL inst.inst_operands
    else
      inst.inst_operands
End

(* =========================================================================
   Per-Instruction Plan Generation
   Port of _generate_evm_for_instruction (non-phi, non-offset cases)
   ========================================================================= *)

Definition generate_regular_inst_plan_def:
  generate_regular_inst_plan liveness dfg cfg fn inst
    next_liveness is_halting next_is_terminator cur_bb_label ps =
    let opc = inst.inst_opcode in
    let operands = compute_operands inst in
    let log_topic_count =
      case opc of LOG =>
        (case HD inst.inst_operands of Lit v => w2n v | _ => 0)
      | _ => 0 in

    (* Emit input operands *)
    let (input_ops, ps1) =
      emit_input_plan opc operands next_liveness ps in

    (* Join-point reorder (jmp only) *)
    let (join_ops, ps2) =
      if opc = JMP then
        (case inst.inst_operands of
          [Label target] =>
            let target_live = live_vars_at liveness target 0 in
            (case lookup_block target fn.fn_blocks of
              NONE => ([] : stack_op list, ps1)
            | SOME target_bb =>
                let target_stack =
                  input_vars_from cur_bb_label
                    target_bb.bb_instructions target_live in
                reorder_plan dfg (MAP Var target_stack) ps1)
        | _ => ([], ps1))
      else ([], ps1) in

    (* Commutative optimization *)
    let (operands', ps3) =
      if is_commutative opc ∧ LENGTH operands ≥ 2 then
        let (ops_a, _) = reorder_plan dfg operands ps2 in
        let cost_a = reorder_cost ops_a in
        let n = LENGTH operands in
        let swapped = TAKE (n - 2) operands ++
          [EL (n - 1) operands; EL (n - 2) operands] in
        let (ops_b, _) = reorder_plan dfg swapped ps2 in
        let cost_b = reorder_cost ops_b in
        if cost_a < cost_b then (operands, ps2)
        else (swapped, ps2)
      else (operands, ps2) in

    (* Final reorder *)
    let (reorder_ops, ps4) = reorder_plan dfg operands' ps3 in

    (* Pop consumed, push outputs *)
    let ps5 = ps4 with ps_stack :=
      stack_pop (LENGTH operands') ps4.ps_stack in
    let outputs = inst.inst_outputs in
    let ps6 = FOLDL (λps' out.
      ps' with ps_stack := stack_push (Var out) ps'.ps_stack)
      ps5 outputs in

    (* Emit EVM opcode(s) *)
    let (emit_ops, ps7) = generate_emit_ops inst log_topic_count ps6 in

    (* Post-processing *)
    if outputs = [] then
      let ps8 = release_dead_spills next_liveness ps7 in
      (input_ops ++ join_ops ++ reorder_ops ++ emit_ops, ps8)
    else
      let (pop_ops, ps8) =
        if ¬ is_halting then
          let dead = FILTER (λout. ¬ MEM out next_liveness) outputs in
          popmany_plan (MAP Var dead) ps7
        else ([] : stack_op list, ps7) in
      let live_outs = FILTER (λout. MEM out next_liveness) outputs in
      let (opt_ops, ps9) =
        if live_outs = [] then ([] : stack_op list, ps8)
        else optimistic_swap_plan dfg inst next_liveness
               next_is_terminator ps8 in
      let ps10 = release_dead_spills next_liveness ps9 in
      (input_ops ++ join_ops ++ reorder_ops ++ emit_ops ++
       pop_ops ++ opt_ops, ps10)
End

(* Raw FMP operations still require lowering before legacy codegen.  Setup
   operations INITIAL_FMP and BUMP have explicit stack-plan implementations. *)
Definition is_unlowered_fmp_opcode_def:
  is_unlowered_fmp_opcode opc ⇔ is_raw_fmp_opcode opc
End

Definition is_unlowered_internal_call_opcode_def:
  is_unlowered_internal_call_opcode opc ⇔ F
End

(* INVOKE is planned directly, but only after decoding its label-headed
   operand shape.  Context-level call-layout checks establish callee
   resolution and exact input/output arities before codegen. *)
Definition invoke_operands_wf_def:
  invoke_operands_wf inst ⇔
    case inst.inst_operands of Label callee_name :: args => T | _ => F
End

(* Opcodes that should never appear at legacy codegen time. *)
Definition is_pre_codegen_opcode_def:
  is_pre_codegen_opcode opc ⇔
    MEM opc [ALLOCA; SINK; DLOAD; DLOADBYTES; MEMTOP] ∨
    is_unlowered_fmp_opcode opc ∨
    is_unlowered_internal_call_opcode opc
End

(* =========================================================================
   Codegen Preconditions
   These are what the caller (pipeline proof) must discharge.
   ========================================================================= *)

(* Per-instruction: no pre-codegen opcodes *)
Definition codegen_ready_inst_def:
  codegen_ready_inst inst ⇔
    ¬ is_pre_codegen_opcode inst.inst_opcode ∧
    (inst.inst_opcode = INVOKE ==> invoke_operands_wf inst)
End

(* Per-function: structural WF + SSA + SUE + normalized CFG + no bad opcodes *)
Definition codegen_ready_fn_def:
  codegen_ready_fn fn ⇔
    canonical_param_prefix fn ∧
    wf_function fn ∧
    fn_inst_wf fn ∧
    ssa_form fn ∧
    def_dominates_uses fn ∧
    single_use_form fn ∧
    cfg_is_normalized (cfg_analyze fn) fn ∧
    EVERY (λbb. EVERY codegen_ready_inst bb.bb_instructions) fn.fn_blocks
End

(* Per-context: all functions ready *)
Definition codegen_ready_def:
  codegen_ready ctx ⇔ EVERY codegen_ready_fn ctx.ctx_functions
End

(* Dispatch to phi, offset, or regular.
   Returns NONE if an opcode that should have been eliminated is encountered. *)
Definition generate_inst_plan_def:
  generate_inst_plan liveness dfg cfg fn inst
    next_liveness is_halting next_is_terminator cur_bb_label ps =
    if is_pre_codegen_opcode inst.inst_opcode then NONE
    else if inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst then NONE
    else if inst.inst_opcode = PHI then
      SOME (generate_phi_plan inst next_liveness ps)
    else if inst.inst_opcode = OFFSET then
      SOME (generate_offset_plan inst ps)
    else if is_param_opcode inst.inst_opcode then
      SOME ([] : stack_op list, ps)
    else if inst.inst_opcode = NOP then
      SOME ([], ps)
    else
      (* ASSIGN and all other opcodes go through regular pipeline.
         generate_emit_ops returns [] for opcodes with no EVM equivalent. *)
      SOME (generate_regular_inst_plan liveness dfg cfg fn inst
              next_liveness is_halting next_is_terminator cur_bb_label ps)
End

Theorem generate_inst_plan_pre_codegen_none:
  is_pre_codegen_opcode inst.inst_opcode ==>
  generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
    next_is_terminator cur_bb_label ps = NONE
Proof
  simp[generate_inst_plan_def]
QED

Theorem generate_inst_plan_malformed_invoke_none:
  inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst ==>
  generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
    next_is_terminator cur_bb_label ps = NONE
Proof
  simp[generate_inst_plan_def]
QED

Theorem invoke_operands_wf_eval:
  invoke_operands_wf (mk_inst 0 INVOKE [Label "callee"] []) /\
  invoke_operands_wf (mk_inst 1 INVOKE [Label "callee"; Lit 7w] ["out"]) /\
  ~invoke_operands_wf (mk_inst 2 INVOKE [] []) /\
  ~invoke_operands_wf (mk_inst 3 INVOKE [Lit 0w] [])
Proof
  EVAL_TAC
QED

(* =========================================================================
   Prepare Stack for Function Entry
   Port of _prepare_stack_for_function
   ========================================================================= *)

Definition get_params_def:
  get_params [] = ([] : instruction list) ∧
  get_params (inst :: rest) =
    if is_param_opcode inst.inst_opcode then inst :: get_params rest
    else []
End

Definition prepare_params_plan_def:
  prepare_params_plan liveness fn ps =
    let entry = HD fn.fn_blocks in
    let params = get_params entry.bb_instructions in
    if params = [] then ([] : stack_op list, ps)
    else
      let ps' = FOLDL (λps' inst.
        ps' with ps_stack := stack_push
          (Var (HD inst.inst_outputs)) ps'.ps_stack)
        ps params in
      let next_live = live_vars_at liveness
            entry.bb_label (LENGTH params) in
      let to_pop = FILTER
            (λv. ¬ MEM (operand_to_string v) next_live)
            ps'.ps_stack in
      let to_pop_vars = FILTER is_var_operand to_pop in
      let (pop_ops, ps'') = popmany_plan to_pop_vars ps' in
      (* Python: _optimistic_swap checks if the next instruction (first
         non-param) is a terminator. Compute that here. *)
      let first_non_param = FIND (λinst. ¬is_param_opcode inst.inst_opcode)
            entry.bb_instructions in
      let next_is_term = case first_non_param of
          SOME inst => is_terminator inst.inst_opcode
        | NONE => F in
      let (swap_ops, ps''') =
        optimistic_swap_plan dfg_empty (LAST params) next_live
          next_is_term ps'' in
      (pop_ops ++ swap_ops, ps''')
End

(* =========================================================================
   Clean Stack from CFG In
   Port of clean_stack_from_cfg_in
   ========================================================================= *)

Definition clean_stack_plan_def:
  clean_stack_plan liveness cfg fn bb ps =
    let preds = cfg_preds_of cfg bb.bb_label in
    case preds of
      [pred_lbl] =>
        if LENGTH (cfg_succs_of cfg pred_lbl) ≤ 1 then
          ([] : stack_op list, ps)
        else
          (case lookup_block pred_lbl fn.fn_blocks of
            NONE => ([], ps)
          | SOME pred_bb =>
              let inputs = input_vars_from pred_lbl
                bb.bb_instructions
                (live_vars_at liveness bb.bb_label 0) in
              let layout = live_vars_at liveness pred_lbl
                (LENGTH pred_bb.bb_instructions) in
              let to_pop = FILTER (λv. ¬ MEM v inputs) layout in
              popmany_plan (MAP Var to_pop) ps)
    | _ => ([], ps)
End

(* =========================================================================
   Non-Param Instructions
   ========================================================================= *)

Definition non_param_insts_def:
  non_param_insts bb =
    FILTER (λinst. ¬is_param_opcode inst.inst_opcode) bb.bb_instructions
End

(* =========================================================================
   Per-Block Plan Generation
   ========================================================================= *)

Definition generate_block_plan_def:
  generate_block_plan liveness dfg cfg fn bb ps =
    let label_op = [SOLabel bb.bb_label] in
    let (param_ops, ps1) =
      if bb = HD fn.fn_blocks
      then prepare_params_plan liveness fn ps
      else ([] : stack_op list, ps) in
    let (clean_ops, ps2) =
      if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
      then clean_stack_plan liveness cfg fn bb ps1
      else ([], ps1) in
    let insts = non_param_insts bb in
    let is_halting = bb_is_halting bb in
    let n_params = LENGTH (get_params bb.bb_instructions) in
    let result =
      FOLDL (λacc (i, inst).
        case acc of
          NONE => NONE
        | SOME (ops, ps) =>
            let next_live =
              if i + 1 < LENGTH insts then
                live_vars_at liveness bb.bb_label (i + n_params + 1)
              else
                live_vars_at liveness bb.bb_label
                  (LENGTH bb.bb_instructions) in
            (* Python: _optimistic_swap skips if next inst is terminator *)
            let next_is_term =
              if i + 1 < LENGTH insts then
                is_terminator (EL (i + 1) insts).inst_opcode
              else F in
            case generate_inst_plan liveness dfg cfg fn inst
                   next_live is_halting next_is_term bb.bb_label ps of
              NONE => NONE
            | SOME (step_ops, ps') =>
                SOME (ops ++ step_ops, ps'))
      (SOME ([] : stack_op list, ps2))
      (MAPi (λi inst. (i, inst)) insts) in
    case result of
      NONE => NONE
    | SOME (inst_ops, ps3) =>
        SOME (label_op ++ param_ops ++ clean_ops ++ inst_ops, ps3)
End

(* =========================================================================
   Recursive DFS Block Traversal
   Mutual recursion with explicit visited set for clean termination.
   Follows cfgDefsScript.sml INDUCTIVE_INVARIANT pattern.
   ========================================================================= *)

(* Helper: FIND SOME implies MEM *)
Theorem FIND_SOME_MEM:
  ∀P l x. FIND P l = SOME x ⇒ MEM x l ∧ P x
Proof
  gen_tac >> Induct >> simp[FIND_thm] >>
  rw[] >> Cases_on `P h` >> gvs[]
QED

(* Helper: lookup_block SOME implies label in fn_labels *)
Theorem lookup_block_mem_fn_labels:
  lookup_block lbl bbs = SOME bb ⇒
  MEM lbl (MAP (λb. b.bb_label) bbs)
Proof
  rw[venomInstTheory.lookup_block_def] >>
  drule FIND_SOME_MEM >> simp[MEM_MAP] >> metis_tac[]
QED

(* The Hol_defn: visited is an explicit parameter, NOT in plan_state *)
val fn_plan_defn = Hol_defn "generate_fn_plan_aux" `
  (generate_fn_plan_aux liveness dfg cfg fn [] visited ps =
    SOME ([] : stack_op list, visited, ps)) /\

  (generate_fn_plan_aux liveness dfg cfg fn (lbl :: rest) visited ps =
    if MEM lbl visited then
      generate_fn_plan_aux liveness dfg cfg fn rest visited ps
    else
      let visited' = lbl :: visited in
      case lookup_block lbl fn.fn_blocks of
        NONE => generate_fn_plan_aux liveness dfg cfg fn rest visited' ps
      | SOME bb =>
        case generate_block_plan liveness dfg cfg fn bb ps of
          NONE => NONE
        | SOME (block_ops, ps') =>
          let succs = cfg_succs_of cfg lbl in
          case generate_succs_plan liveness dfg cfg fn
                 ps'.ps_stack ps'.ps_spilled succs visited' ps' of
            NONE => NONE
          | SOME (succ_ops, visited'', ps'') =>
            case generate_fn_plan_aux liveness dfg cfg fn
                   rest visited'' ps'' of
              NONE => NONE
            | SOME (rest_ops, visited_final, ps_final) =>
                SOME (block_ops ++ succ_ops ++ rest_ops,
                      visited_final, ps_final)) /\

  (generate_succs_plan liveness dfg cfg fn
     saved_stack saved_spilled [] visited ps_g =
    SOME ([] : stack_op list, visited, ps_g)) /\

  (generate_succs_plan liveness dfg cfg fn
     saved_stack saved_spilled (succ :: rest) visited ps_g =
    let ps_branch = ps_g with <|
      ps_stack := saved_stack;
      ps_spilled := saved_spilled |> in
    case generate_fn_plan_aux liveness dfg cfg fn
           [succ] visited ps_branch of
      NONE => NONE
    | SOME (s_ops, visited_after, ps_after) =>
      let ps_g' = ps_g with <|
        ps_alloc := ps_after.ps_alloc;
        ps_label_counter := ps_after.ps_label_counter |> in
      case generate_succs_plan liveness dfg cfg fn
             saved_stack saved_spilled rest visited_after ps_g' of
        NONE => NONE
      | SOME (rest_ops, visited_final, ps_final) =>
          SOME (s_ops ++ rest_ops, visited_final, ps_final))`;

(* --- Termination machinery --- *)

val fn_plan_aux_def = DB.fetch "-" "generate_fn_plan_aux_UNION_AUX_def";
val fn_plan_M = fn_plan_aux_def |> SPEC_ALL |> concl |> rhs |> rand;

(* Sum type for the mutual recursion *)
val sum_ty =
  fn_plan_M |> type_of |> dom_rng |> #1 |> dom_rng |> #1;
val result_ty =
  fn_plan_M |> type_of |> dom_rng |> #1 |> dom_rng |> #2;

val fn_plan_R = ``inv_image ($< LEX $< LEX ($< : num -> num -> bool))
  (\(x : ^(ty_antiq sum_ty)).
    case x of
      INL (liveness, dfg, cfg, fn, worklist, visited, ps) =>
        (CARD (set (fn_labels fn) DIFF set visited), LENGTH worklist, 0n)
    | INR (liveness, dfg, cfg, fn, saved_stack, saved_spilled,
           succs, visited, ps_g) =>
        (CARD (set (fn_labels fn) DIFF set visited), LENGTH succs, 1n))``;

val fn_plan_P = ``\(x : ^(ty_antiq sum_ty)) (result : ^(ty_antiq result_ty)).
  case result of
    NONE => T
  | SOME (ops, visited_out, ps_out) =>
    (case x of
      INL (_, _, _, _, _, visited, _) => set visited SUBSET set visited_out
    | INR (_, _, _, _, _, _, _, visited, _) => set visited SUBSET set visited_out)``;

val fn_plan_wf = prove(``WF ^fn_plan_R``,
  MATCH_MP_TAC WF_inv_image >>
  MATCH_MP_TAC WF_LEX >> simp[] >>
  MATCH_MP_TAC WF_LEX >> simp[]);

(* INDUCTIVE_INVARIANT: visited grows monotonically *)
Theorem fn_plan_inv_thm:
  INDUCTIVE_INVARIANT ^fn_plan_R ^fn_plan_P ^fn_plan_M
Proof
  simp[INDUCTIVE_INVARIANT_DEF, inv_image_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `x` >> simp[]
  (* ===== INL case ===== *)
  >- (
    PairCases_on `x'` >> simp[] >>
    Cases_on `x'4` >> simp[]
    >> Cases_on `MEM h x'5` >> simp[]
    >- (
      first_x_assum (qspec_then `INL (x'0,x'1,x'2,x'3,t,x'5,x'6)` mp_tac) >>
      simp[LEX_DEF]
    )
    >> Cases_on `lookup_block h (x'3.fn_blocks)` >> simp[]
    >- (
      first_x_assum (qspec_then `INL (x'0,x'1,x'2,x'3,t,h::x'5,x'6)` mp_tac) >>
      (impl_tac >- (
        simp[] >> simp[LEX_DEF] >>
        Cases_on `MEM h (fn_labels x'3)` >> simp[]
        >- (DISJ1_TAC >>
            `set (fn_labels x'3) INTER set x'5 PSUBSET
             set (fn_labels x'3) INTER (h INSERT set x'5)` by (
              simp[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
              Q.EXISTS_TAC `h` >> simp[]) >>
            `CARD (set (fn_labels x'3) INTER set x'5) <
             CARD (set (fn_labels x'3) INTER (h INSERT set x'5))` by
              metis_tac[CARD_PSUBSET, FINITE_INTER,
                        FINITE_LIST_TO_SET, FINITE_INSERT] >>
            `CARD (set (fn_labels x'3) INTER set x'5) <=
             CARD (set (fn_labels x'3))` by
              (irule CARD_SUBSET >> simp[SUBSET_DEF]) >>
            `CARD (set (fn_labels x'3) INTER (h INSERT set x'5)) <=
             CARD (set (fn_labels x'3))` by
              (irule CARD_SUBSET >> simp[SUBSET_DEF]) >>
            simp[])
        >- (DISJ2_TAC >>
            `set (fn_labels x'3) INTER (h INSERT set x'5) =
             set (fn_labels x'3) INTER set x'5` by
              (simp[EXTENSION] >> metis_tac[]) >>
            simp[])
      )) >>
      strip_tac >> rpt CASE_TAC >> fs[] >>
      metis_tac[SUBSET_DEF, listTheory.MEM]
    )
    (* SOME bb: block_plan then two recursive calls *)
    >> rpt CASE_TAC >> simp[] >> fs[]
    (* Apply IH to INR (succs) call *)
    >> first_assum (qspec_then
        `INR (x'0,x'1,x'2,x'3,r.ps_stack,r.ps_spilled,
              cfg_succs_of x'2 h, h::x'5, r)` mp_tac) >>
    (impl_tac >- (
      simp[] >> simp[LEX_DEF] >>
      DISJ1_TAC >>
      `set (fn_labels x'3) INTER set x'5 PSUBSET
       set (fn_labels x'3) INTER (h INSERT set x'5)` by (
        simp[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
        Q.EXISTS_TAC `h` >> simp[] >>
        imp_res_tac lookup_block_mem_fn_labels >>
        fs[venomInstTheory.fn_labels_def]) >>
      `CARD (set (fn_labels x'3) INTER set x'5) <
       CARD (set (fn_labels x'3) INTER (h INSERT set x'5))` by
        metis_tac[CARD_PSUBSET, FINITE_INTER,
                  FINITE_LIST_TO_SET, FINITE_INSERT] >>
      `CARD (set (fn_labels x'3) INTER set x'5) <=
       CARD (set (fn_labels x'3))` by
        (irule CARD_SUBSET >> simp[SUBSET_DEF]) >>
      `CARD (set (fn_labels x'3) INTER (h INSERT set x'5)) <=
       CARD (set (fn_labels x'3))` by
        (irule CARD_SUBSET >> simp[SUBSET_DEF]) >>
      simp[]
    )) >> simp[] >> strip_tac >>
    (* Apply IH to INL (rest) call *)
    first_x_assum (qspec_then
        `INL (x'0,x'1,x'2,x'3,t,q'',r'')` mp_tac) >>
    (impl_tac >- (
      simp[] >> simp[LEX_DEF] >>
      `CARD (set (fn_labels x'3) INTER set x'5) <=
       CARD (set (fn_labels x'3) INTER set q'')` by (
        irule CARD_SUBSET >> simp[SUBSET_DEF] >>
        metis_tac[SUBSET_DEF]) >>
      simp[]
    )) >> simp[] >> strip_tac >>
    metis_tac[SUBSET_TRANS, SUBSET_DEF, listTheory.MEM]
  )
  (* ===== INR case ===== *)
  >- (
    PairCases_on `y` >> simp[] >>
    Cases_on `y6` >> simp[]
    >> rpt CASE_TAC >> simp[] >> fs[]
    (* Apply IH to INL [h] call *)
    >> first_assum (qspec_then
        `INL (y0,y1,y2,y3,[h],y7,
              y8 with <| ps_stack := y4; ps_spilled := y5 |>)` mp_tac) >>
    (impl_tac >- (simp[] >> simp[LEX_DEF] >> Cases_on `t` >> simp[])) >>
    simp[] >> strip_tac >>
    (* Apply IH to INR rest call *)
    first_x_assum (qspec_then
        `INR (y0,y1,y2,y3,y4,y5,t,q',
              y8 with <| ps_alloc := r'.ps_alloc;
                         ps_label_counter := r'.ps_label_counter |>)` mp_tac) >>
    (impl_tac >- (
      simp[] >> simp[LEX_DEF] >>
      `CARD (set (fn_labels y3) INTER set y7) <=
       CARD (set (fn_labels y3) INTER set q')` by (
        irule CARD_SUBSET >> simp[SUBSET_DEF] >>
        metis_tac[SUBSET_DEF]) >>
      simp[]
    )) >> simp[] >> strip_tac >>
    metis_tac[SUBSET_TRANS]
  )
QED
val fn_plan_inv = DB.fetch "-" "fn_plan_inv_thm";

(* Extract monotonicity: fn_plan_aux_UNION_AUX preserves visited *)
val fn_plan_mono_raw =
  MATCH_MP INDUCTIVE_INVARIANT_WFREC (CONJ fn_plan_wf fn_plan_inv);
val fn_plan_mono =
  REWRITE_RULE [GSYM fn_plan_aux_def] fn_plan_mono_raw;
val fn_plan_mono_simp = SIMP_RULE (srw_ss()) [] fn_plan_mono;

(* Helper: extract visited SUBSET from a successful INL call *)
val fn_plan_mono_inl = prove(
  ``!liveness dfg cfg fn wl visited ps ops vis' ps'.
    generate_fn_plan_aux_UNION_aux ^fn_plan_R
      (INL (liveness,dfg,cfg,fn,wl,visited,ps)) = SOME (ops,vis',ps')
    ==> set visited SUBSET set vis'``,
  rpt strip_tac >>
  mp_tac (Q.SPEC `INL(liveness,dfg,cfg,fn,wl,visited,ps)` fn_plan_mono_simp) >>
  gvs[]
);

(* Helper: extract visited SUBSET from a successful INR call *)
val fn_plan_mono_inr = prove(
  ``!liveness dfg cfg fn ss sp succs visited ps ops vis' ps'.
    generate_fn_plan_aux_UNION_aux ^fn_plan_R
      (INR (liveness,dfg,cfg,fn,ss,sp,succs,visited,ps)) = SOME (ops,vis',ps')
    ==> set visited SUBSET set vis'``,
  rpt strip_tac >>
  mp_tac (Q.SPEC `INR(liveness,dfg,cfg,fn,ss,sp,succs,visited,ps)` fn_plan_mono_simp) >>
  gvs[]
);

(* Termination obligation tactic *)
fun fn_plan_obl_tac () =
  EXISTS_TAC fn_plan_R >>
  conj_tac >- ACCEPT_TAC fn_plan_wf >>
  (* Obl 1: INR → INR rest (after INL [succ], uses mono_inl) *)
  conj_tac >- (
    rpt strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    drule fn_plan_mono_inl >> simp[] >> strip_tac >>
    simp[inv_image_def, LEX_DEF] >>
    `CARD (set (fn_labels fn) DIFF set visited_after) <=
     CARD (set (fn_labels fn) DIFF set visited)` by (
      irule CARD_SUBSET >> simp[SUBSET_DEF] >>
      rpt strip_tac >> gvs[SUBSET_DEF]) >>
    gvs[]) >>
  (* Obl 2: INR → INL [succ] *)
  conj_tac >- (
    rpt strip_tac >> gvs[inv_image_def, LEX_DEF] >>
    Cases_on `rest` >> simp[]) >>
  (* Obl 3: INL → INL rest after INR (uses mono_inr) *)
  conj_tac >- (
    rpt strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    drule fn_plan_mono_inr >> simp[] >> strip_tac >>
    simp[inv_image_def, LEX_DEF] >>
    `MEM lbl (fn_labels fn)` by
      (simp[venomInstTheory.fn_labels_def] >>
       irule lookup_block_mem_fn_labels >> metis_tac[]) >>
    `CARD (set (fn_labels fn) DIFF set visited'') <=
     CARD (set (fn_labels fn) DIFF (lbl INSERT set visited))` by (
      irule CARD_SUBSET >> simp[SUBSET_DEF] >>
      rpt strip_tac >> gvs[SUBSET_DEF]) >>
    `CARD (set (fn_labels fn) DIFF (lbl INSERT set visited)) <
     CARD (set (fn_labels fn) DIFF set visited)` by (
      irule CARD_PSUBSET >>
      simp[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
      qexists_tac `lbl` >> simp[]) >>
    gvs[]) >>
  (* Obl 4: INL → INR succs *)
  conj_tac >- (
    rpt strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qmatch_goalsub_abbrev_tac`inv_image _ ff` >>
    simp[inv_image_def, LEX_DEF] >>
    `MEM lbl (fn_labels fn)` by
      (simp[venomInstTheory.fn_labels_def] >>
       irule lookup_block_mem_fn_labels >> metis_tac[]) >>
    qunabbrev_tac`ff` >>
    simp_tac (std_ss ++ pairSimps.PAIR_ss) [pair_case_def] >>
    disj1_tac >> irule CARD_PSUBSET >>
    simp[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
    qexists_tac `lbl` >> simp[]) >>
  (* Obl 5: INL, lookup NONE → INL rest *)
  conj_tac >- (
    rpt strip_tac >> gvs[inv_image_def, LEX_DEF, Excl"CARD_DIFF"] >>
    `CARD (set (fn_labels fn) DIFF (lbl INSERT set visited)) <=
     CARD (set (fn_labels fn) DIFF set visited)` by (
      irule CARD_SUBSET >> simp[SUBSET_DEF]) >>
    simp[Excl"CARD_DIFF"]) >>
  (* Obl 6: INL, MEM lbl visited → INL rest *)
  rpt strip_tac >> gvs[inv_image_def, LEX_DEF];

val (fn_plan_aux_eqs, fn_plan_aux_ind) =
  Defn.tprove(fn_plan_defn, fn_plan_obl_tac());

Theorem generate_fn_plan_aux_def[compute] = fn_plan_aux_eqs
Theorem generate_fn_plan_aux_ind = fn_plan_aux_ind

Theorem visited_subset_cons:
  !lbl visited. set visited SUBSET set (lbl :: visited)
Proof
  simp[SUBSET_DEF]
QED

(* Visited monotonicity for the clean mutually recursive functions. *)
Theorem generate_plan_visited_mono:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
     generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
       SOME (ops,visited',ps') ==>
     set visited SUBSET set visited') /\
  (!liveness dfg cfg fn saved_stack saved_spilled succs visited ps ops
      visited' ps'.
     generate_succs_plan liveness dfg cfg fn saved_stack saved_spilled
       succs visited ps = SOME (ops,visited',ps') ==>
     set visited SUBSET set visited')
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `MEM lbl visited`
      >- gvs[Once generate_fn_plan_aux_def]
      >> Cases_on `lookup_block lbl fn.fn_blocks`
      >- gvs[Once generate_fn_plan_aux_def]
      >> rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
      Cases_on `generate_block_plan liveness dfg cfg fn bb ps`
      >- gvs[Once generate_fn_plan_aux_def]
      >> rename1 `generate_block_plan liveness dfg cfg fn bb ps = SOME bp` >>
      PairCases_on `bp` >>
      Cases_on `generate_succs_plan liveness dfg cfg fn bp1.ps_stack
                  bp1.ps_spilled (cfg_succs_of cfg lbl) (lbl::visited) bp1`
      >- gvs[Once generate_fn_plan_aux_def]
      >> rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME sr` >>
      PairCases_on `sr` >>
      Cases_on `generate_fn_plan_aux liveness dfg cfg fn worklist sr1 sr2`
      >- gvs[Once generate_fn_plan_aux_def]
      >> rename1 `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME rr` >>
      PairCases_on `rr` >>
      gvs[Once generate_fn_plan_aux_def] >>
      irule SUBSET_TRANS >> qexists `set (lbl::visited)` >> conj_tac
      >- (MATCH_ACCEPT_TAC visited_subset_cons)
      >> irule SUBSET_TRANS >> qexists `set sr1` >> conj_tac >> simp[])
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def])
  >> rpt gen_tac >> strip_tac >>
     Cases_on `generate_fn_plan_aux liveness dfg cfg fn [succ] visited
                 (ps with <| ps_stack := saved_stack;
                             ps_spilled := saved_spilled |>)`
     >- gvs[Once (cj 4 generate_fn_plan_aux_def)]
     >> rename1 `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME sr` >>
     PairCases_on `sr` >>
     Cases_on `generate_succs_plan liveness dfg cfg fn saved_stack
                 saved_spilled succs sr1
                 (ps with <| ps_alloc := sr2.ps_alloc;
                             ps_label_counter := sr2.ps_label_counter |>)`
     >- gvs[Once (cj 4 generate_fn_plan_aux_def)]
     >> rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME rr` >>
     PairCases_on `rr` >>
     gvs[Once (cj 4 generate_fn_plan_aux_def)] >>
     irule SUBSET_TRANS >> qexists `set sr1` >> conj_tac >> simp[]
QED

Theorem generate_fn_plan_aux_visited_mono =
  CONJUNCT1 generate_plan_visited_mono

Theorem generate_succs_plan_visited_mono =
  CONJUNCT2 generate_plan_visited_mono

Definition generate_fn_plan_aux_fuel_def:
  generate_fn_plan_aux_fuel 0 liveness dfg cfg fn worklist visited ps =
    NONE ∧
  generate_fn_plan_aux_fuel (SUC fuel) liveness dfg cfg fn [] visited ps =
    SOME ([] : stack_op list, visited, ps) ∧
  generate_fn_plan_aux_fuel (SUC fuel) liveness dfg cfg fn
      (lbl :: rest) visited ps =
    (if MEM lbl visited then
       generate_fn_plan_aux_fuel fuel liveness dfg cfg fn rest visited ps
     else
       let visited' = lbl :: visited in
       case lookup_block lbl fn.fn_blocks of
         NONE =>
           generate_fn_plan_aux_fuel fuel liveness dfg cfg fn
             rest visited' ps
       | SOME bb =>
           case generate_block_plan liveness dfg cfg fn bb ps of
             NONE => NONE
           | SOME (block_ops, ps') =>
               let succs = cfg_succs_of cfg lbl in
               case generate_succs_plan_fuel fuel liveness dfg cfg fn
                      ps'.ps_stack ps'.ps_spilled succs visited' ps' of
                 NONE => NONE
               | SOME (succ_ops, visited'', ps'') =>
                   case generate_fn_plan_aux_fuel fuel liveness dfg cfg fn
                          rest visited'' ps'' of
                     NONE => NONE
                   | SOME (rest_ops, visited_final, ps_final) =>
                       SOME (block_ops ++ succ_ops ++ rest_ops,
                             visited_final, ps_final)) ∧
  generate_succs_plan_fuel 0 liveness dfg cfg fn
      saved_stack saved_spilled succs visited ps_g =
    NONE ∧
  generate_succs_plan_fuel (SUC fuel) liveness dfg cfg fn
      saved_stack saved_spilled [] visited ps_g =
    SOME ([] : stack_op list, visited, ps_g) ∧
  generate_succs_plan_fuel (SUC fuel) liveness dfg cfg fn
      saved_stack saved_spilled (succ :: rest) visited ps_g =
    (let ps_branch = ps_g with <|
       ps_stack := saved_stack;
       ps_spilled := saved_spilled |> in
     case generate_fn_plan_aux_fuel fuel liveness dfg cfg fn
            [succ] visited ps_branch of
       NONE => NONE
     | SOME (s_ops, visited_after, ps_after) =>
         let ps_g' = ps_g with <|
           ps_alloc := ps_after.ps_alloc;
           ps_label_counter := ps_after.ps_label_counter |> in
         case generate_succs_plan_fuel fuel liveness dfg cfg fn
                saved_stack saved_spilled rest visited_after ps_g' of
           NONE => NONE
         | SOME (rest_ops, visited_final, ps_final) =>
             SOME (s_ops ++ rest_ops, visited_final, ps_final))
Termination
  WF_REL_TAC `measure (λx. case x of
      INL (fuel, liveness, dfg, cfg, fn, worklist, visited, ps) => fuel
    | INR (fuel, liveness, dfg, cfg, fn, saved_stack, saved_spilled,
           succs, visited, ps_g) => fuel)`
  \\ rw[]
End

(* =========================================================================
   Top-Level Entry Points
   ========================================================================= *)

Definition generate_fn_plan_def:
  generate_fn_plan fn spill_base (lbl_ctr : num) =
    if ¬canonical_param_prefix fn then NONE
    else
      let liveness = liveness_analyze fn in
      let dfg = dfg_build_function fn in
      let cfg = cfg_analyze fn in
      let ps = (init_plan_state spill_base) with ps_label_counter := lbl_ctr in
      case fn_entry_label fn of
        NONE => SOME ([] : stack_op list, ps)
      | SOME lbl =>
          case generate_fn_plan_aux liveness dfg cfg fn [lbl] [] ps of
            NONE => NONE
          | SOME (ops, _, ps') => SOME (ops, ps')
End

Definition generate_fn_plan_fuel_def:
  generate_fn_plan_fuel fuel fn spill_base (lbl_ctr : num) =
    if ¬canonical_param_prefix fn then NONE
    else
      let liveness = liveness_analyze_fuel fuel fn in
      let dfg = dfg_build_function fn in
      let cfg = cfg_analyze fn in
      let ps = (init_plan_state spill_base) with ps_label_counter := lbl_ctr in
      case fn_entry_label fn of
        NONE => SOME ([] : stack_op list, ps)
      | SOME lbl =>
          case generate_fn_plan_aux_fuel fuel liveness dfg cfg fn [lbl] [] ps of
            NONE => NONE
          | SOME (ops, _, ps') => SOME (ops, ps')
End

Definition revert_postamble_def:
  revert_postamble =
    [SOLabel "revert"; SOPush (Lit 0w); SOEmit "DUP1"; SOEmit "REVERT"]
End

Definition collect_fn_eoms_def:
  (collect_fn_eoms [] = SOME ([] : num list)) /\
  (collect_fn_eoms (fn::fns) =
    case fn.fn_eom of
      NONE => NONE
    | SOME eom =>
        case collect_fn_eoms fns of
          NONE => NONE
        | SOME eoms => SOME (eom::eoms))
End

Definition max_live_eom_def:
  max_live_eom ctx =
    if ~reserved_intervals_wf ctx.ctx_global_reserved then NONE else
    case global_reserved_end ctx.ctx_global_reserved 0 of
      NONE => NONE
    | SOME global_end =>
        OPTION_MAP (FOLDL MAX global_end)
                   (collect_fn_eoms ctx.ctx_functions)
End

Definition generate_context_regions_def:
  (generate_context_regions gen [] acc = SOME acc) /\
  (generate_context_regions gen (fn::fns) acc =
    let spill_base = acc.cpa_next_spill_base in
    case gen fn spill_base acc.cpa_label_counter of
      NONE => NONE
    | SOME (fn_ops,ps) =>
        let spill_end = ps.ps_alloc.sa_next_offset in
        let region = <|
          sr_fn_name := fn.fn_name;
          sr_spill_base := spill_base;
          sr_spill_end := spill_end;
          sr_plan := fn_ops
        |> in
        if spill_plan_in_region spill_base spill_end fn_ops then
          let peak =
            if spill_base < spill_end then
              MAX acc.cpa_peak_spill_end spill_end
            else acc.cpa_peak_spill_end in
          generate_context_regions gen fns
            (acc with <|
              cpa_regions := SNOC region acc.cpa_regions;
              cpa_label_counter := ps.ps_label_counter;
              cpa_next_spill_base := spill_end;
              cpa_peak_spill_end := peak
            |>)
        else NONE)
End

Definition finish_context_plan_def:
  finish_context_plan max_eom acc = <|
    cp_regions := acc.cpa_regions;
    cp_max_static_eom := max_eom;
    cp_peak_spill_end := acc.cpa_peak_spill_end;
    cp_initial_fmp := ceil32
      (MAX max_eom acc.cpa_peak_spill_end)
  |>
End

Definition generate_context_plan_with_def:
  generate_context_plan_with gen ctx =
    case max_live_eom ctx of
      NONE => NONE
    | SOME max_eom =>
        let init = <|
          cpa_regions := [];
          cpa_label_counter := 0;
          cpa_next_spill_base := max_eom;
          cpa_peak_spill_end := 0
        |> in
        case generate_context_regions gen ctx.ctx_functions init of
          NONE => NONE
        | SOME acc =>
            let cp = finish_context_plan max_eom acc in
            if cp.cp_initial_fmp < dimword (:256)
            then SOME cp else NONE
End

Definition generate_context_plan_def:
  generate_context_plan ctx =
    generate_context_plan_with generate_fn_plan ctx
End

Definition generate_context_plan_fuel_def:
  generate_context_plan_fuel fuel ctx =
    generate_context_plan_with (generate_fn_plan_fuel fuel) ctx
End
Theorem generate_context_regions_rejects_malformed_spill:
  generate_context_regions
    (\fn base labels. SOME ([SOSpill base], init_plan_state base))
    [fn] acc = NONE
Proof
  simp[generate_context_regions_def,
       stackPlanTypesTheory.spill_plan_in_region_def,
       stackPlanTypesTheory.stack_op_in_spill_region_def,
       stackPlanTypesTheory.init_plan_state_def,
       stackPlanTypesTheory.init_spill_alloc_def]
QED

Theorem generate_context_regions_accepts_empty_plan:
  IS_SOME
    (generate_context_regions
      (\fn base labels. SOME ([], init_plan_state base)) [fn] acc)
Proof
  simp[generate_context_regions_def,
       stackPlanTypesTheory.spill_plan_in_region_def,
       stackPlanTypesTheory.init_plan_state_def,
       stackPlanTypesTheory.init_spill_alloc_def]
QED


Definition context_plan_ops_def:
  context_plan_ops cp =
    FLAT (MAP (\r. r.sr_plan) cp.cp_regions) ++ revert_postamble
End
