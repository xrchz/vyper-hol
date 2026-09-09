(*
 * Mem2Var Pass — Definitions
 *
 * Ports vyper/venom/passes/mem2var.py to HOL4.
 *
 * Promotes memory operations to variable operations where safe:
 *   - alloca only used by mstore/mload/return → promote to variable
 *
 * For alloca promotion (size = 32):
 *   mstore [alloca_addr; val]  → assign [val] → [alloca_var]
 *   mload [alloca_addr]        → assign [alloca_var] → [orig_out]
 *   return with alloca_addr    → insert mstore before, keep return
 *
 * Uses DFG analysis (use tracking per variable).
 *
 * TOP-LEVEL:
 *   m2v_can_promote_alloca      — check if alloca uses are all mstore/mload/return
 *   m2v_promote_inst            — promote a single alloca use
 *   m2v_transform_function      — function-level transform
 *   m2v_stores_dominate_loads   — precondition: MSTOREs dominate MLOADs per alloca
 *   m2v_promotable_wf           — all promoted allocas satisfy domination
 *   m2v_equiv                   — equivalence relation (ignores memory)
 *
 * Upstream: vyperlang/vyper@8780b3134 (remove alloca_id)
 *)

Theory mem2varDefs
Ancestors
  passSimulationDefs dfgDefs venomExecSemantics venomInst stateEquiv venomWf
  pred_set finite_map

(* ===== Fresh Variable ===== *)

Definition m2v_fresh_var_def:
  m2v_fresh_var (varname : string) (count : num) =
    STRCAT "alloca_" (STRCAT varname (STRCAT "_" (toString count)))
End

(* ===== Use Analysis ===== *)

(* Check if all uses are mstore/mload/return (promotable).
   Requires at least one mstore (otherwise never written). *)
Definition m2v_can_promote_alloca_def:
  m2v_can_promote_alloca uses <=>
    EVERY (\inst. inst.inst_opcode = MSTORE \/
                  inst.inst_opcode = MLOAD \/
                  inst.inst_opcode = RETURN) uses /\
    EXISTS (\inst. inst.inst_opcode = MSTORE) uses
End



(* ===== Store-Dominates-Load Precondition ===== *)

(* For a given alloca output variable, every MLOAD use is dominated
   by some MSTORE use of the same alloca.  Without this, promotion
   can turn a read-from-zero-memory into a read-from-undefined-variable.
   Python's SSA sandwich (MakeSSA before mem2var) ensures this in practice. *)
Definition m2v_stores_dominate_loads_def:
  m2v_stores_dominate_loads fn alloca_out <=>
    !bb load_inst.
      MEM bb fn.fn_blocks /\
      MEM load_inst bb.bb_instructions /\
      (load_inst.inst_opcode = MLOAD \/ load_inst.inst_opcode = RETURN) /\
      MEM (Var alloca_out) load_inst.inst_operands ==>
      ?store_bb store_inst.
        MEM store_bb fn.fn_blocks /\
        MEM store_inst store_bb.bb_instructions /\
        store_inst.inst_opcode = MSTORE /\
        MEM (Var alloca_out) store_inst.inst_operands /\
        fn_dominates fn store_bb.bb_label bb.bb_label /\
        (store_bb = bb ==>
          ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
                EL i bb.bb_instructions = store_inst /\
                EL j bb.bb_instructions = load_inst)
End

(* Every promoted alloca satisfies the store-dominates-load property. *)
Definition m2v_promotable_wf_def:
  m2v_promotable_wf fn <=>
    let dfg = dfg_build_function fn in
    !inst alloca_out.
      MEM inst (fn_insts fn) /\
      inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [alloca_out] /\
      m2v_can_promote_alloca (dfg_get_uses dfg alloca_out) ==>
      m2v_stores_dominate_loads fn alloca_out
End

(* ===== Promotion Transform ===== *)

(*
 * Promote a single mstore/mload/return instruction that uses an alloca.
 *
 * Parameters:
 *   alloca_var  — the promoted variable name
 *   alloca_out  — the original alloca output (address variable)
 *   size        — alloca size (only promote if 32)
 *   inst        — instruction to transform
 *
 * In HOL4 semantic operand order:
 *   mstore [offset; value] → if offset = alloca_out: assign [value] → [alloca_var]
 *   mload [addr] → if addr = alloca_out: assign [Var alloca_var] → [orig_out]
 *   return [offset; size] → if offset = alloca_out: insert mstore before, keep return
 *)
Definition m2v_promote_inst_def:
  m2v_promote_inst alloca_var alloca_out (size : num) inst =
    if inst.inst_opcode = MSTORE /\ size = 32 then
      case inst.inst_operands of
        [ofs; val_op] =>
          if ofs = Var alloca_out then
            (* mstore to alloca → assign val to promoted var *)
            [inst with <| inst_opcode := ASSIGN;
                          inst_operands := [val_op];
                          inst_outputs := [alloca_var] |>]
          else [inst]
      | _ => [inst]
    else if inst.inst_opcode = MLOAD /\ size = 32 then
      case inst.inst_operands of
        [addr] =>
          if addr = Var alloca_out then
            (* mload from alloca → assign promoted var *)
            [inst with <| inst_opcode := ASSIGN;
                          inst_operands := [Var alloca_var] |>]
          else [inst]
      | _ => [inst]
    else if inst.inst_opcode = RETURN /\ size <= 32 then
      case inst.inst_operands of
        (* HOL4 RETURN: [offset; size]. Python operands[1] = offset = HOL4 op1.
           Check if offset (first operand) is the alloca address. *)
        [off_op; sz_op] =>
          if off_op = Var alloca_out then
            (* return from alloca: insert mstore to materialize value *)
            let store = <| inst_id := inst.inst_id;
                           inst_opcode := MSTORE;
                           inst_operands := [Var alloca_out; Var alloca_var];
                           inst_outputs := [] |> in
            [store; inst]
          else [inst]
      | _ => [inst]
    else [inst]
End

(* ===== Function-Level Transform ===== *)

(*
 * Transform function: collect promotion info, then rewrite instructions.
 *
 * Single-pass approach (post alloca_id removal — upstream 8780b3134):
 *   1. Scan ALLOCA instructions, determine which are promotable
 *   2. Rewrite all instructions according to promotion decisions
 *
 * An alloca is promotable iff ALL uses are mstore/mload/return
 * (checked by m2v_can_promote_alloca). Non-promotable allocas are
 * left unchanged — the old _fix_adds / escape_use path was removed
 * upstream because phi/assign guards on alloca are impossible after
 * alloca_id removal.
 *)
Definition m2v_transform_function_def:
  m2v_transform_function fn =
    let dfg = dfg_build_function fn in
    (* Collect alloca instructions *)
    let alloca_insts = FILTER (\i : instruction.
      i.inst_opcode = ALLOCA)
      (fn_insts fn) in
    (* Build promotion map *)
    let scan_result = FOLDL (\(ctr, promos) (i : instruction).
      case i.inst_outputs of
        [alloca_out] =>
          let uses = dfg_get_uses dfg alloca_out in
          let size_val = case i.inst_operands of
                           Lit w :: _ => w2n w | _ => 0 in
          if m2v_can_promote_alloca uses then
            let var = m2v_fresh_var alloca_out ctr in
            (ctr + 1, (alloca_out, var, size_val) :: promos)
          else
            (ctr, promos)
        | _ => (ctr, promos))
      (0, []) alloca_insts in
    let promo_list = SND scan_result in
    (* Rewrite instructions *)
    let rewrite_inst = \i : instruction.
      case FIND (\(ao, _, _). MEM (Var ao) i.inst_operands) promo_list of
        SOME (ao, pvar, sz) => m2v_promote_inst pvar ao sz i
      | NONE => [i] in
    fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        FLAT (MAP rewrite_inst bb.bb_instructions))
      fn.fn_blocks
End

(* ===== Equivalence Relation ===== *)

(*
 * m2v_equiv: State equivalence ignoring vs_memory.
 *
 * mem2var promotes MSTORE→ASSIGN, so memory genuinely differs after
 * transformation (alloca regions are not written in the transformed code).
 * This relation captures everything that IS preserved:
 *   - All variables (except fresh alloca promotion vars)
 *   - All non-memory state fields
 *   - Control flow fields (usable as both R_ok and R_term in lift_result)
 *
 * The `vars` parameter excludes fresh variables introduced by promotion
 * (the alloca_N_M naming scheme). These variables exist only in the
 * transformed state.
 *
 * This is the same relation as icf_equiv (invokeCopyFwdCommon) but
 * with variable exclusion, defined here to avoid cross-pass dependency.
 *)
Definition m2v_equiv_def:
  m2v_equiv vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next
End

(* Fresh variables introduced by the transform *)
Definition m2v_fresh_vars_def:
  m2v_fresh_vars fn =
    let dfg = dfg_build_function fn in
    let alloca_insts = FILTER (\i : instruction.
      i.inst_opcode = ALLOCA)
      (fn_insts fn) in
    let scan_result = FOLDL (\(ctr, fresh) (i : instruction).
      case i.inst_outputs of
        [alloca_out] =>
          let uses = dfg_get_uses dfg alloca_out in
          let size_val = case i.inst_operands of
                           Lit w :: _ => w2n w | _ => 0 in
          if m2v_can_promote_alloca uses then
            let var = m2v_fresh_var alloca_out ctr in
            (ctr + 1, var INSERT fresh)
          else
            (ctr, fresh)
        | _ => (ctr, fresh))
      (0, {}) alloca_insts in
    SND scan_result
End

(* Fresh variable names don't collide with any original instruction
   output or operand variable. This ensures:
   (1) original execution never writes to fresh variables
   (2) original instructions never read fresh variables
   so operand agreement holds between original and transformed states. *)
Definition m2v_fresh_names_disjoint_def:
  m2v_fresh_names_disjoint fn <=>
    !v. v IN m2v_fresh_vars fn ==>
      !inst. MEM inst (fn_insts fn) ==>
        ~MEM v inst.inst_outputs /\ ~MEM (Var v) inst.inst_operands
End


(* ================================================================
   INVARIANT DEFINITIONS (moved from mem2varProofsScript)
   ================================================================ *)

(* Promotion list: extracted from function *)
Definition m2v_promo_list_def:
  m2v_promo_list fn =
    let dfg = dfg_build_function fn in
    let alloca_insts = FILTER (\i : instruction.
      i.inst_opcode = ALLOCA) (fn_insts fn) in
    SND (FOLDL (\(ctr, promos) (i : instruction).
      case i.inst_outputs of
        [alloca_out] =>
          let uses = dfg_get_uses dfg alloca_out in
          let size_val = case i.inst_operands of
                           Lit w :: _ => w2n w | _ => 0 in
          if m2v_can_promote_alloca uses then
            let var = m2v_fresh_var alloca_out ctr in
            (ctr + 1, (alloca_out, var, size_val) :: promos)
          else (ctr, promos)
        | _ => (ctr, promos))
      (0, []) alloca_insts)
End

(* Block transform *)
Definition m2v_bt_def:
  m2v_bt fn bb =
    let promo_list = m2v_promo_list fn in
    let rewrite_inst = \i : instruction.
      case FIND (\(ao, _, _). MEM (Var ao) i.inst_operands) promo_list of
        SOME (ao, pvar, sz) => m2v_promote_inst pvar ao sz i
      | NONE => [i] in
    bb with bb_instructions :=
      FLAT (MAP rewrite_inst bb.bb_instructions)
End

(* Set of promoted alloca instruction IDs *)
Definition m2v_promoted_ids_def:
  m2v_promoted_ids fn =
    { inst.inst_id |
      inst |
      MEM inst (fn_insts fn) /\
      inst.inst_opcode = ALLOCA /\
      ?alloca_out. inst.inst_outputs = [alloca_out] /\
        m2v_can_promote_alloca
          (dfg_get_uses (dfg_build_function fn) alloca_out) }
End

(* A byte address falls in a promoted alloca's memory region.
   Only covers sz=32 entries: these are the actually-promoted allocas
   whose memory writes are replaced by variable assignments.
   sz≠32 entries are left unchanged, so their memory is tracked by
   the general memory agreement clause in m2v_inv_noix. *)
Definition in_promoted_region_def:
  in_promoted_region fn s (addr : num) <=>
    ?aid base.
      aid IN m2v_promoted_ids fn /\
      FLOOKUP s.vs_allocas aid = SOME (base, 32) /\
      base <= addr /\ addr < base + 32
End

(* Read a memory byte with zero-padding beyond allocated memory *)
Definition mem_byte_def:
  mem_byte (i : num) (s : venom_state) =
    if i < LENGTH s.vs_memory then EL i s.vs_memory else (0w : word8)
End

(* Inter-block invariant:
   1. m2v_equiv: all non-fresh variables and non-memory fields agree
   2. Memory agreement outside promoted alloca regions
   3. Sync: each written promoted variable tracks the alloca memory cell *)
Definition m2v_inv_def:
  m2v_inv fn s1 s2 <=>
    m2v_equiv (m2v_fresh_vars fn) s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!i. ~in_promoted_region fn s1 i ==>
         mem_byte i s1 = mem_byte i s2) /\
    (!ao pvar sz.
       MEM (ao, pvar, sz) (m2v_promo_list fn) ==>
       !addr. lookup_var ao s1 = SOME addr ==>
         IS_SOME (lookup_var pvar s2) ==>
         lookup_var pvar s2 = SOME (mload (w2n addr) s1))
End

(* Predicate: all promoted allocas have size exactly 32.
 * Required because EVM MSTORE/MLOAD always accesses 32 bytes,
 * and RETURN promotion inserts a MSTORE that writes exactly 32 bytes.
 * In practice, Vyper allocas for single words are always 32 bytes.
 * Provable from a sound bp_ptrs_bounded analysis that tracks alloca pointers. *)
Definition m2v_promo_sizes_bounded_def:
  m2v_promo_sizes_bounded fn <=>
    !ao pvar sz. MEM (ao, pvar, sz) (m2v_promo_list fn) ==> sz = 32
End

(* Predicate: promoted RETURN instructions have literal size ≤ alloca size.
 * Required because the inserted MSTORE only restores 32 bytes (alloca size),
 * so the RETURN must read ≤ 32 bytes from the alloca region for the
 * simulation to produce identical return data.
 * Derivable from bp_ptrs_bounded when the RETURN size operand is a literal. *)
Definition m2v_return_size_bounded_def:
  m2v_return_size_bounded fn <=>
    !bb inst ao pvar sz.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = RETURN /\
      MEM (ao, pvar, sz) (m2v_promo_list fn) /\
      MEM (Var ao) inst.inst_operands ==>
      ?n. inst.inst_operands = [Var ao; Lit n] /\ w2n n <= sz
End

(* Predicate: fresh variables are undefined in a state *)
Definition m2v_fresh_undef_def:
  m2v_fresh_undef fn s <=>
    !v. v IN m2v_fresh_vars fn ==> lookup_var v s = NONE
End

(* Combined scan: compute (ctr, promo_list, fresh_set) in one FOLDL *)
Definition m2v_scan_step_def:
  m2v_scan_step dfg (ctr, promos, fresh) (i : instruction) =
    case i.inst_outputs of
      [alloca_out] =>
        let uses = dfg_get_uses dfg alloca_out in
        let size_val = case i.inst_operands of
                         Lit w :: _ => w2n w | _ => 0 in
        if m2v_can_promote_alloca uses then
          let var = m2v_fresh_var alloca_out ctr in
          (ctr + 1, (alloca_out, var, size_val) :: promos, var INSERT fresh)
        else (ctr, promos, fresh)
    | _ => (ctr, promos, fresh)
End
