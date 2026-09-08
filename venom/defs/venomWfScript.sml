(*
 * Venom Well-Formedness Predicates
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * This theory defines structural well-formedness for Venom IR functions
 * and contexts: entry blocks, block structure, successor closure, and
 * context-level invariants.
 *)

Theory venomWf
Ancestors
  dretShapeDefs

(* ==========================================================================
   PHI operand well-formedness: alternating (Label, Var) pairs.
   ========================================================================== *)

Definition phi_well_formed_def:
  phi_well_formed [] = T /\
  phi_well_formed [_] = T /\
  phi_well_formed (Label lbl :: Var v :: rest) = phi_well_formed rest /\
  phi_well_formed (Label lbl :: _ :: rest) = F /\
  phi_well_formed (_ :: _ :: rest) = phi_well_formed rest
End

(* ==========================================================================
   Per-instruction well-formedness (inst_wf)

   Captures the structural shape (operand count/type, output count) that
   step_inst_base requires for each opcode.  Eliminates ~60 Error branches
   due to wrong operand counts, missing outputs, or wrong operand types.

   Runtime errors (undefined operand, phi predecessor mismatch, param OOB,
   non-terminating ext_call) are NOT eliminated — those require state info.
   ========================================================================== *)

Definition inst_wf_def:
  inst_wf inst ⇔
    case inst.inst_opcode of
    (* ---- exec_pure2: 2 operands, 1 output ---- *)
    | ADD => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SUB => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | MUL => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | Div => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | Mod => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SDIV => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SMOD => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | Exp => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | EQ => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | LT => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | GT => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SLT => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SGT => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | AND => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | OR => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | XOR => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SHL => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SHR => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SAR => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SIGNEXTEND => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | BYTE => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    (* ---- exec_pure1: 1 operand, 1 output ---- *)
    | ISZERO => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | NOT => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    (* ---- exec_pure3: 3 operands, 1 output ---- *)
    | ADDMOD => LENGTH inst.inst_operands = 3 ∧ LENGTH inst.inst_outputs = 1
    | MULMOD => LENGTH inst.inst_operands = 3 ∧ LENGTH inst.inst_outputs = 1
    (* ---- exec_read0: 0 operands, 1 output ---- *)
    | CALLER => LENGTH inst.inst_outputs = 1
    | ADDRESS => LENGTH inst.inst_outputs = 1
    | CALLVALUE => LENGTH inst.inst_outputs = 1
    | GAS => LENGTH inst.inst_outputs = 1
    | ORIGIN => LENGTH inst.inst_outputs = 1
    | GASPRICE => LENGTH inst.inst_outputs = 1
    | CHAINID => LENGTH inst.inst_outputs = 1
    | COINBASE => LENGTH inst.inst_outputs = 1
    | TIMESTAMP => LENGTH inst.inst_outputs = 1
    | NUMBER => LENGTH inst.inst_outputs = 1
    | PREVRANDAO => LENGTH inst.inst_outputs = 1
    | GASLIMIT => LENGTH inst.inst_outputs = 1
    | BASEFEE => LENGTH inst.inst_outputs = 1
    | BLOBBASEFEE => LENGTH inst.inst_outputs = 1
    | CALLDATASIZE => LENGTH inst.inst_outputs = 1
    | RETURNDATASIZE => LENGTH inst.inst_outputs = 1
    | MEMTOP => LENGTH inst.inst_outputs = 1
    | CODESIZE => LENGTH inst.inst_outputs = 1
    | SELFBALANCE => LENGTH inst.inst_outputs = 1
    (* ---- exec_read1: 1 operand, 1 output ---- *)
    | MLOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | SLOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | TLOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | ILOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | DLOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | BLOCKHASH => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | BLOBHASH => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | BALANCE => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | CALLDATALOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | EXTCODESIZE => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | EXTCODEHASH => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    (* ---- exec_write2: 2 operands, no output ---- *)
    | MSTORE => LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []
    | MSTORE8 => LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []
    | SSTORE => LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []
    | TSTORE => LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []
    | ISTORE => LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []
    (* ---- copy/bulk ops: no output ---- *)
    | MCOPY => LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []
    | CALLDATACOPY => LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []
    | RETURNDATACOPY => LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []
    | DLOADBYTES => LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []
    | CODECOPY => LENGTH inst.inst_operands = 3 /\ inst.inst_outputs = []
    (* ---- 4 operands, no output ---- *)
    | EXTCODECOPY => LENGTH inst.inst_operands = 4 /\ inst.inst_outputs = []
    (* ---- SHA3: 2 operands, 1 output ---- *)
    | SHA3 => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    (* ---- Control flow ---- *)
    | JMP => ∃lbl. inst.inst_operands = [Label lbl] /\ inst.inst_outputs = []
    | JNZ => ∃c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
                        inst.inst_outputs = []
    | DJMP => ∃sel label_ops.
               inst.inst_operands = sel :: label_ops ∧
               EVERY (λop. IS_SOME (get_label op)) label_ops /\
               inst.inst_outputs = []
    | RET => inst.inst_outputs = []
    | RETURN => LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []
    | REVERT => LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []
    | STOP => inst.inst_outputs = []
    | SINK => inst.inst_outputs = []
    (* ---- SSA ---- *)
    | PHI => LENGTH inst.inst_outputs = 1 ∧
             phi_well_formed inst.inst_operands
    | ASSIGN => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | NOP => inst.inst_outputs = []
    | PARAM => ∃idx. inst.inst_operands = [Lit idx] ∧
                     LENGTH inst.inst_outputs = 1
    | FMP_PARAM => (∃idx. inst.inst_operands = [Lit idx]) ∧
                         LENGTH inst.inst_outputs = 1
    | RETPC_PARAM => (∃idx. inst.inst_operands = [Lit idx]) ∧
                           LENGTH inst.inst_outputs = 1
    (* ---- Allocation and frame-memory-pointer operations ---- *)
    | ALLOCA => ∃sz. inst.inst_operands = [Lit sz] ∧
                     LENGTH inst.inst_outputs = 1
    | DALLOCA => LENGTH inst.inst_operands = 1 ∧
                 LENGTH inst.inst_outputs = 1
    | DRET => inst.inst_outputs = [] ∧ IS_SOME (parse_dret_shape inst)
    | GETFMP => inst.inst_operands = [] ∧ LENGTH inst.inst_outputs = 1
    | SETFMP => LENGTH inst.inst_operands = 1 ∧ inst.inst_outputs = []
    | RETFMP => inst.inst_operands <> [] ∧ inst.inst_outputs = []
    | INITIAL_FMP => inst.inst_operands = [] ∧ LENGTH inst.inst_outputs = 1
    | BUMP => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 2
    (* ---- External calls ---- *)
    | CALL => LENGTH inst.inst_operands = 7 ∧ LENGTH inst.inst_outputs = 1
    | STATICCALL => LENGTH inst.inst_operands = 6 ∧ LENGTH inst.inst_outputs = 1
    | DELEGATECALL => LENGTH inst.inst_operands = 6 ∧ LENGTH inst.inst_outputs = 1
    | CREATE => LENGTH inst.inst_operands = 3 ∧ LENGTH inst.inst_outputs = 1
    | CREATE2 => LENGTH inst.inst_operands = 4 ∧ LENGTH inst.inst_outputs = 1
    (* ---- Special ---- *)
    | OFFSET => ∃v lbl. inst.inst_operands = [Lit v; Label lbl] ∧
                        LENGTH inst.inst_outputs = 1
    | LOG => ∃tc rest. inst.inst_operands = Lit tc :: rest ∧
                       LENGTH rest = w2n tc + 2 /\ inst.inst_outputs = []
    | SELFDESTRUCT => LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = []
    | INVALID => inst.inst_outputs = []
    (* ---- Assertions ---- *)
    | ASSERT => LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = []
    | ASSERT_UNREACHABLE => LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = []
    (* ---- INVOKE: Label + args, outputs unconstrained (matches callee return
       arity which can be 0, 1, or more - see check_venom._collect_ret_arities) ---- *)
    | INVOKE => ∃lbl args. inst.inst_operands = Label lbl :: args
End

Theorem inst_wf_offset_shape:
  inst_wf inst /\ inst.inst_opcode = OFFSET ==>
  ?v lbl out.
    inst.inst_operands = [Lit v; Label lbl] /\
    inst.inst_outputs = [out]
Proof
  rpt strip_tac >>
  gvs[inst_wf_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

(* The function has an entry block (fn_blocks is non-empty). *)
Definition fn_has_entry_def:
  fn_has_entry fn <=> fn.fn_blocks <> []
End

(* A basic block is well-formed: non-empty and ends with a terminator. *)
Definition bb_well_formed_def:
  bb_well_formed bb <=>
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (* Terminator only at end *)
    (!i. i < LENGTH bb.bb_instructions /\
         is_terminator (EL i bb.bb_instructions).inst_opcode ==>
         i = PRE (LENGTH bb.bb_instructions)) /\
    (* PHI instructions form a prefix of the block *)
    (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
           (EL j bb.bb_instructions).inst_opcode = PHI ==>
           (EL i bb.bb_instructions).inst_opcode = PHI)
End

(* All pseudo instructions (PHI, PARAM) form a prefix of the block.
 * Matches Vyper compiler output where PHIs and PARAMs are always emitted
 * first. Stronger than bb_well_formed's PHI-only prefix constraint.
 * Defined separately to avoid modifying bb_well_formed (which would cause
 * a 30+ minute rebuild of execEquivProofs). *)
Definition pseudos_prefix_def:
  pseudos_prefix bb <=>
    !i j. i < j /\ j < LENGTH bb.bb_instructions /\
          is_pseudo (EL j bb.bb_instructions).inst_opcode ==>
          is_pseudo (EL i bb.bb_instructions).inst_opcode
End

(* All blocks in a function have pseudos as a prefix. *)
Definition fn_pseudos_prefix_def:
  fn_pseudos_prefix fn <=>
    !bb. MEM bb fn.fn_blocks ==> pseudos_prefix bb
End

(* All successor labels of every block exist as block labels in the function. *)
Definition fn_succs_closed_def:
  fn_succs_closed fn <=>
    !bb succ.
      MEM bb fn.fn_blocks /\ MEM succ (bb_succs bb) ==>
      MEM succ (fn_labels fn)
End

(* All instruction ids across all blocks are distinct. *)
Definition fn_inst_ids_distinct_def:
  fn_inst_ids_distinct fn <=>
    ALL_DISTINCT
      (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks))
End

(* Structural well-formedness for IR functions:
 * unique labels, has entry, blocks well-formed, successor labels exist,
 * instruction ids are globally unique. *)
Definition wf_function_def:
  wf_function fn <=>
    ALL_DISTINCT (fn_labels fn) /\
    fn_has_entry fn /\
    (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\
    fn_succs_closed fn /\
    fn_inst_ids_distinct fn
End

(* ==========================================================================
   SSA and instruction predicates (general IR concepts)
   ========================================================================== *)

(* SSA form: each variable is defined at most once across all instructions.
   Every output variable name appears at most once across all instruction
   output lists. This is the textbook definition: every variable has exactly
   one definition point, including multi-output instructions like INVOKE. *)
Definition ssa_form_def:
  ssa_form fn <=>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))
End

(* CFG edge relation on block labels within a function. *)
Definition fn_cfg_edge_def:
  fn_cfg_edge fn a b <=>
    ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = a /\ MEM b (bb_succs bb)
End

(* A block label is reachable from the entry block via CFG edges.
   Uses RTC (reflexive-transitive closure). *)
Definition fn_reachable_def:
  fn_reachable fn lbl <=>
    ?entry. fn_entry_label fn = SOME entry /\ RTC (fn_cfg_edge fn) entry lbl
End

(* A path through the function's CFG.
   Every consecutive pair (a,b) in the path is a CFG edge. *)
Definition is_fn_path_def:
  is_fn_path fn [] = T /\
  is_fn_path fn [l] = T /\
  is_fn_path fn (l1 :: l2 :: rest) =
    (fn_cfg_edge fn l1 l2 /\ is_fn_path fn (l2 :: rest))
End

(* Block d dominates block n in function fn: d is on every CFG path from
   the entry to n. *)
Definition fn_dominates_def:
  fn_dominates fn d n <=>
    fn_reachable fn n /\
    !path. is_fn_path fn path /\
           path <> [] /\
           (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
           LAST path = n ==>
           MEM d path
End

(* Every variable use is dominated by its definition.
   Standard SSA property: if instruction inst in block bb uses Var v,
   then v is defined by some instruction in some block def_bb, and
   def_bb dominates bb.  When def and use are in the same block, the
   def must appear at a strictly earlier index (intra-block ordering).
   This is the standard formulation: "every def reaches its use." *)
Definition def_dominates_uses_def:
  def_dominates_uses fn <=>
    !bb inst v.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands ==>
      ?def_bb def_inst.
        MEM def_bb fn.fn_blocks /\
        MEM def_inst def_bb.bb_instructions /\
        MEM v def_inst.inst_outputs /\
        fn_dominates fn def_bb.bb_label bb.bb_label /\
        (def_bb = bb ==>
          ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
                EL i bb.bb_instructions = def_inst /\
                EL j bb.bb_instructions = inst)
End

(* Well-formed SSA: unique definitions AND definitions dominate uses.
   Within-block ordering follows from def_dominates_uses + fn_inst_ids_distinct
   (part of wf_function). *)
Definition wf_ssa_def:
  wf_ssa fn <=> ssa_form fn /\ def_dominates_uses fn
End

(* Check if instruction is a PHI. *)
Definition is_phi_inst_def:
  is_phi_inst inst <=> inst.inst_opcode = PHI
End

(* No generated split-block label collides with existing labels. *)
Definition split_labels_fresh_def:
  split_labels_fresh name_fn func ⇔
    ∀p t. ¬MEM (name_fn p t) (fn_labels func)
End

(* ==========================================================================
   Context well-formedness
   ========================================================================== *)

(* Function names in the context are distinct. *)
Definition ctx_distinct_fn_names_def:
  ctx_distinct_fn_names ctx <=> ALL_DISTINCT (ctx_fn_names ctx)
End

(* The context has an entry function that names a real function. *)
Definition ctx_has_entry_def:
  ctx_has_entry ctx <=>
    ?entry_name. ctx.ctx_entry = SOME entry_name /\
       MEM entry_name (ctx_fn_names ctx)
End

(* Well-formed context. *)
Definition ctx_wf_def:
  ctx_wf ctx <=> ctx_distinct_fn_names ctx /\ ctx_has_entry ctx
End

(* All instruction ids across all functions in the context are distinct.
   Matches Python: inst_id is a global counter across the whole module. *)
Definition ctx_inst_ids_distinct_def:
  ctx_inst_ids_distinct ctx ⇔
    ALL_DISTINCT
      (FLAT (MAP (λfn.
        FLAT (MAP (λbb. MAP (λi. i.inst_id) bb.bb_instructions)
          fn.fn_blocks)) ctx.ctx_functions))
End

(* Every INVOKE instruction's first operand is a Label naming a
 * function in the context. *)
Definition wf_invoke_targets_def:
  wf_invoke_targets ctx <=>
    (!func inst.
       MEM func ctx.ctx_functions /\
       MEM inst (fn_insts func) /\
       inst.inst_opcode = INVOKE ==>
       ?lbl rest. inst.inst_operands = Label lbl :: rest /\
                  MEM lbl (ctx_fn_names ctx))
End

(* ==========================================================================
   Whole-function inst_wf: every instruction in the function is well-formed.
   ========================================================================== *)

Definition fn_inst_wf_def:
  fn_inst_wf fn ⇔
    ∀bb inst.
      MEM bb fn.fn_blocks ∧
      MEM inst bb.bb_instructions ==>
      inst_wf inst
End

(* ==========================================================================
   Composed venom_wf — single precondition for high-level theorems.

   Level 1 (syntactic/structural): eliminates ~60 structural Error branches
   from step_inst_base.  No analysis required.
   ========================================================================== *)

Definition venom_wf_def:
  venom_wf ctx ⇔
    ctx_wf ctx ∧
    wf_invoke_targets ctx ∧
    ctx_inst_ids_distinct ctx ∧
    (∀fn. MEM fn ctx.ctx_functions ==>
          wf_function fn ∧ fn_inst_wf fn)
End
