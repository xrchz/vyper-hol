(*
 * Function Inliner Pass — Definitions
 *
 * Inlines small internal functions at their call sites. Copies callee's
 * basic blocks into the caller, binds parameters, and rewires control flow.
 *
 * Source: vyper/venom/passes/function_inliner.py (~241 LOC)
 * Upstream: vyperlang/vyper@cff4f6822
 *
 * TOP-LEVEL:
 *   clone_function              — clone function with prefixed labels/vars
 *   inline_call_site            — inline callee at a single INVOKE site
 *   fix_inline_phis             — fix PHIs after inlining
 *   inline_at_sites             — inline callee at all sites in a function
 *   remove_function             — remove a function from context
 *   build_call_walk             — postorder DFS walk over call graph
 *   select_inline_candidate     — select next function to inline
 *   function_inliner_ctx        — full pass
 *
 * Helper:
 *   is_label_op / inline_prefix / return_block_label
 *   clone_operand / clone_instruction / clone_basic_block
 *   rotate_invoke_ops
 *   rewrite_inline_inst / rewrite_inline_insts
 *   rewrite_inline_block / rewrite_inline_blocks
 *   find_invoke_idx / find_invoke_site
 *   fn_code_size / fn_code_size_from_ctx
 *)

Theory functionInlinerDefs
Ancestors
  cfgTransform venomWf venomExecSemantics fcgDefs

(* ===== Operand Helpers ===== *)

Definition is_label_op_def:
  is_label_op (Label _) = T ∧
  is_label_op _ = F
End

(* ===== Naming ===== *)

(* Prefix for inline instance N. Python: f"inl{self.inline_count}_" *)
Definition inline_prefix_def:
  inline_prefix (n:num) = STRCAT "inl" (STRCAT (num_to_dec_string n) "_")
End

(* Return block label. Python: ctx.get_next_label(f"{prefix}inline_return")
   produces f"{prefix}inline_return{label_counter}". *)
Definition return_block_label_def:
  return_block_label prefix (label_counter:num) =
    STRCAT prefix (STRCAT "inline_return" (num_to_dec_string label_counter))
End

(* ===== Cloning ===== *)

(* Clone operand: prefix internal labels and all variables.
   fn_block_labels: block labels of the source function.
   Labels not in fn_block_labels (e.g. data labels) are kept as-is. *)
Definition clone_operand_def:
  clone_operand prefix fn_block_labels (Label l) =
    (if MEM l fn_block_labels then Label (STRCAT prefix l) else Label l) ∧
  clone_operand prefix fn_block_labels (Var v) = Var (STRCAT prefix v) ∧
  clone_operand prefix fn_block_labels (Lit w) = Lit w
End

Definition clone_instruction_def:
  clone_instruction prefix fn_block_labels inst =
    inst with <|
      inst_operands :=
        MAP (clone_operand prefix fn_block_labels) inst.inst_operands;
      inst_outputs :=
        MAP (λv. STRCAT prefix v) inst.inst_outputs
    |>
End

Definition clone_basic_block_def:
  clone_basic_block prefix fn_block_labels bb =
    <| bb_label := STRCAT prefix bb.bb_label;
       bb_instructions :=
         MAP (clone_instruction prefix fn_block_labels) bb.bb_instructions |>
End

(* Clone by updating the callee record: only identity name and blocks change.
   ABI, noinline, forced-allocation, EOM, and FMP metadata stay with the callee. *)
Definition clone_function_def:
  clone_function prefix func =
    let labels = fn_labels func in
    func with <| fn_name := STRCAT prefix func.fn_name;
                 fn_blocks :=
                   MAP (clone_basic_block prefix labels) func.fn_blocks |>
End

(* ===== Parameter / Return Rewriting ===== *)

(* Rotate INVOKE operands for PARAM binding.
   Python: ops = call_site.operands[1:] + [call_site.operands[0]]
   Moves the callee label (return PC) to the end so PARAM indices
   match argument positions. *)
Definition rotate_invoke_ops_def:
  rotate_invoke_ops [] = [] ∧
  rotate_invoke_ops (first::rest) = rest ++ [first]
End

(* Rewrite a single instruction in a cloned block.
   Returns (replacement instructions, updated param_idx).
   PARAM → ASSIGN from caller's operand (rotated).
     The last PARAM gets a Label operand (return PC). Python assigns it
     because labels are addresses at runtime. Our eval_operand returns
     NONE for Labels — the correctness proof must show this assign is
     dead code (output unused after RET → JMP).
   RET → assign return values to INVOKE outputs, then JMP to return block.
   Others → unchanged. *)
Definition rewrite_inline_inst_def:
  rewrite_inline_inst invoke_ops invoke_outs return_label inst param_idx =
    if inst.inst_opcode = PARAM then
      if param_idx < LENGTH invoke_ops then
        ([inst with <| inst_opcode := ASSIGN;
                       inst_operands := [EL param_idx invoke_ops] |>],
         param_idx + 1)
      else
        ([inst], param_idx)
    else if inst.inst_opcode = RET then
      let all_but_last =
        TAKE (LENGTH inst.inst_operands - 1) inst.inst_operands in
      let ret_vals = FILTER (λop. ¬is_label_op op) all_but_last in
      let assigns = MAPi (λi rv.
        <| inst_id := 0;
           inst_opcode := ASSIGN;
           inst_operands := [rv];
           inst_outputs := [EL i invoke_outs] |>)
        ret_vals in
      let jmp = inst with <| inst_opcode := JMP;
                              inst_operands := [Label return_label];
                              inst_outputs := [] |> in
      (assigns ++ [jmp], param_idx)
    else
      ([inst], param_idx)
End

(* Rewrite an instruction list, threading param_idx. *)
Definition rewrite_inline_insts_def:
  rewrite_inline_insts invoke_ops invoke_outs return_label [] param_idx =
    ([], param_idx) ∧
  rewrite_inline_insts invoke_ops invoke_outs return_label (inst::rest)
      param_idx =
    let (inst_list, pi') =
      rewrite_inline_inst invoke_ops invoke_outs return_label
        inst param_idx in
    let (rest_list, pi'') =
      rewrite_inline_insts invoke_ops invoke_outs return_label rest pi' in
    (inst_list ++ rest_list, pi'')
End

Definition rewrite_inline_block_def:
  rewrite_inline_block invoke_ops invoke_outs return_label bb param_idx =
    let (insts, pi') =
      rewrite_inline_insts invoke_ops invoke_outs return_label
        bb.bb_instructions param_idx in
    (bb with bb_instructions := insts, pi')
End

(* Rewrite all cloned blocks. param_idx is shared across blocks
   (matching Python's shared param_idx counter). *)
Definition rewrite_inline_blocks_def:
  rewrite_inline_blocks invoke_ops invoke_outs return_label [] param_idx =
    ([], param_idx) ∧
  rewrite_inline_blocks invoke_ops invoke_outs return_label (bb::rest)
      param_idx =
    let (bb', pi') =
      rewrite_inline_block invoke_ops invoke_outs return_label bb param_idx in
    let (rest', pi'') =
      rewrite_inline_blocks invoke_ops invoke_outs return_label rest pi' in
    (bb' :: rest', pi'')
End

(* ===== Call Site Inlining ===== *)

(* Inline callee at a single INVOKE call site.
   Steps (matching Python _inline_call_site):
   1. Split call block at INVOKE index
   2. Clone callee with prefix
   3. Rewrite cloned blocks: PARAM → ASSIGN, RET → assigns + JMP
   4. Append return block and cloned blocks to caller
   5. Truncated call block gets JMP to cloned entry *)
(* The result is always the caller itself or a caller record update changing
   only fn_blocks; callee metadata is never transferred to the caller. *)
Definition inline_call_site_def:
  inline_call_site prefix return_label caller_fn callee_fn
      call_bb_lbl call_idx =
    case lookup_block call_bb_lbl caller_fn.fn_blocks of
      NONE => caller_fn
    | SOME call_bb =>
        let call_inst = EL call_idx call_bb.bb_instructions in
        let invoke_ops = rotate_invoke_ops call_inst.inst_operands in
        let invoke_outs = call_inst.inst_outputs in
        (* Split block *)
        let before_invoke = TAKE call_idx call_bb.bb_instructions in
        let after_invoke =
          DROP (call_idx + 1) call_bb.bb_instructions in
        let return_bb = <| bb_label := return_label;
                           bb_instructions := after_invoke |> in
        (* Clone and rewrite *)
        let callee_clone = clone_function prefix callee_fn in
        let (rewritten_blocks, _) =
          rewrite_inline_blocks invoke_ops invoke_outs return_label
            callee_clone.fn_blocks 0 in
        (* Entry label of cloned callee *)
        let cloned_entry_label =
          case callee_clone.fn_blocks of
            [] => ""
          | (eb::_) => eb.bb_label in
        (* Truncated call block: before_invoke ++ JMP to cloned entry *)
        let jmp_inst =
          <| inst_id := 0; inst_opcode := JMP;
             inst_operands := [Label cloned_entry_label];
             inst_outputs := [] |> in
        let truncated_bb = call_bb with
          bb_instructions := before_invoke ++ [jmp_inst] in
        (* Assemble: replace call block, append return + cloned blocks *)
        caller_fn with fn_blocks :=
          replace_block call_bb_lbl truncated_bb caller_fn.fn_blocks
          ++ [return_bb]
          ++ rewritten_blocks
End

(* ===== PHI Fixup ===== *)

(* After inlining, successors of the return block may have PHIs
   referencing the original call block. Update to reference return block.
   Matches Python _fix_phi. *)
(* PHI repair is likewise a block-only update of the caller-derived function. *)
Definition fix_inline_phis_def:
  fix_inline_phis orig_label new_label return_bb func =
    let succ_labels = bb_succs return_bb in
    func with fn_blocks :=
      MAP (λbb.
        if MEM bb.bb_label succ_labels then
          bb with bb_instructions :=
            MAP (λinst.
              if inst.inst_opcode ≠ PHI then inst
              else subst_label_inst orig_label new_label inst)
            bb.bb_instructions
        else bb)
      func.fn_blocks
End

(* ===== Inline State ===== *)

(* Counters threaded through inlining for fresh name generation. *)
Datatype:
  inline_state = <|
    is_inline_count : num;
    is_label_counter : num
  |>
End

(* ===== Find INVOKE Sites ===== *)

(* Find index of first INVOKE targeting callee_name in a block. *)
Definition find_invoke_idx_def:
  find_invoke_idx callee_name [] (n:num) = NONE ∧
  find_invoke_idx callee_name (inst::rest) n =
    if inst.inst_opcode = INVOKE ∧
       (case inst.inst_operands of
          Label l :: _ => l = callee_name
        | _ => F)
    then SOME n
    else find_invoke_idx callee_name rest (n + 1)
End

(* Find a call site (block label, instruction index) in a function. *)
Definition find_invoke_site_def:
  find_invoke_site callee_name [] = NONE ∧
  find_invoke_site callee_name (bb::rest) =
    case find_invoke_idx callee_name bb.bb_instructions 0 of
      SOME idx => SOME (bb.bb_label, idx)
    | NONE => find_invoke_site callee_name rest
End

(* ===== Inline at All Sites ===== *)

(* Inline callee at one call site. Returns NONE if no site found. *)
Definition inline_one_site_def:
  inline_one_site caller_fn callee_fn ist =
    case find_invoke_site callee_fn.fn_name caller_fn.fn_blocks of
      NONE => NONE
    | SOME (bb_lbl, idx) =>
        let prefix = inline_prefix ist.is_inline_count in
        let ret_lbl = return_block_label prefix ist.is_label_counter in
        let caller' =
          inline_call_site prefix ret_lbl caller_fn callee_fn bb_lbl idx in
        let caller'' =
          case lookup_block ret_lbl caller'.fn_blocks of
            SOME ret_bb =>
              fix_inline_phis bb_lbl ret_lbl ret_bb caller'
          | NONE => caller' in
        SOME (renumber_fn_inst_ids caller'',
              ist with <| is_inline_count := ist.is_inline_count + 1;
                          is_label_counter := ist.is_label_counter + 1 |>)
End

(* Inline callee at ALL sites in caller, iterating until no more found.
   Fuel bounds iterations (at most one INVOKE per instruction). *)
Definition inline_at_sites_def:
  inline_at_sites 0 caller_fn callee_fn ist = (caller_fn, ist) ∧
  inline_at_sites (SUC n) caller_fn callee_fn ist =
    case inline_one_site caller_fn callee_fn ist of
      NONE => (caller_fn, ist)
    | SOME (caller', ist') =>
        inline_at_sites n caller' callee_fn ist'
End

(* ===== Function Removal ===== *)

Definition remove_function_def:
  remove_function name ctx =
    ctx with ctx_functions :=
      FILTER (λf. f.fn_name ≠ name) ctx.ctx_functions
End

(* ===== Call Walk (Postorder DFS) ===== *)

(* Compatibility alias for the shared total FCG postorder traversal. *)
Definition build_call_walk_def:
  build_call_walk fcg entry_name = fcg_postorder fcg entry_name
End

Theorem build_call_walk_eq_fcg_postorder:
  ∀fcg entry. build_call_walk fcg entry = fcg_postorder fcg entry
Proof
  simp[build_call_walk_def]
QED

(* ===== Candidate Selection ===== *)

(* Non-pseudo instruction count as code size estimate. *)
Definition fn_code_size_def:
  fn_code_size func =
    LENGTH (FILTER (λinst. ¬is_pseudo inst.inst_opcode) (fn_insts func))
End

(* Look up function code size from context. *)
Definition fn_code_size_from_ctx_def:
  fn_code_size_from_ctx ctx fn_name =
    case lookup_function fn_name ctx.ctx_functions of
      NONE => 0
    | SOME func => fn_code_size func
End

(* Select first inlinable function from the walk.
   Inlinable if: has call sites AND (single call site OR cost ≤ threshold).
   Matches Python _select_inline_candidate. *)
Definition select_inline_candidate_def:
  select_inline_candidate ctx fcg threshold [] = NONE ∧
  select_inline_candidate ctx fcg threshold (fn_name::rest) =
    let call_count = LENGTH (fcg_get_call_sites fcg fn_name) in
    if call_count = 0 then
      select_inline_candidate ctx fcg threshold rest
    else if call_count = 1 then
      SOME fn_name
    else if fn_code_size_from_ctx ctx fn_name ≤ threshold then
      SOME fn_name
    else
      select_inline_candidate ctx fcg threshold rest
End

(* ===== Inline a Candidate Across All Callers ===== *)

(* Inline callee into all functions in the context. *)
Definition inline_candidate_def:
  inline_candidate ctx callee ist =
    let (fns', ist') =
      FOLDL (λ(fns, st) caller_fn.
        let max_sites = LENGTH (fn_insts caller_fn) in
        let (caller', st') =
          inline_at_sites max_sites caller_fn callee st in
        (SNOC caller' fns, st'))
      ([], ist)
      ctx.ctx_functions in
    (ctx with ctx_functions := fns', ist')
End

(* ===== Full Pass ===== *)

(* One round: recompute FCG, select candidate, inline, remove.
   Returns NONE if no candidate found. *)
Definition function_inliner_round_def:
  function_inliner_round ctx walk threshold ist =
    let fcg = fcg_analyze ctx in
    case select_inline_candidate ctx fcg threshold walk of
      NONE => NONE
    | SOME candidate_name =>
        case lookup_function candidate_name ctx.ctx_functions of
          NONE => NONE
        | SOME callee =>
            let (ctx', ist') = inline_candidate ctx callee ist in
            let ctx'' = remove_function candidate_name ctx' in
            let walk' = FILTER (λn. n ≠ candidate_name) walk in
            SOME (ctx'', walk', ist')
End

(* Iterate rounds until no more candidates.
   Bounded by function count (one removed per round). *)
Definition function_inliner_loop_def:
  function_inliner_loop 0 ctx walk threshold ist = ctx ∧
  function_inliner_loop (SUC n) ctx walk threshold ist =
    case function_inliner_round ctx walk threshold ist of
      NONE => ctx
    | SOME (ctx', walk', ist') =>
        function_inliner_loop n ctx' walk' threshold ist'
End

(* Top-level entry point. *)
Definition function_inliner_ctx_def:
  function_inliner_ctx threshold ctx =
    let fcg = fcg_analyze ctx in
    let walk =
      case ctx.ctx_entry of
        NONE => []
      | SOME entry => build_call_walk fcg entry in
    let ist = <| is_inline_count := 0; is_label_counter := 0 |> in
    function_inliner_loop (LENGTH ctx.ctx_functions) ctx walk threshold ist
End
