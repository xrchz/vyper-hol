(*
 * Pass Shared Definitions
 *
 * Common helpers used by multiple optimization passes.
 * Opcode-level predicates (is_volatile, is_terminator) live in venomInst.
 *
 * TOP-LEVEL:
 *   is_removable          — instruction can be NOP'd if output unused
 *   mk_nop_inst           — replace instruction with NOP
 *   mk_assign_inst        — replace instruction with ASSIGN from operand
 *   is_copy_opcode        — bulk memory copy opcodes (MCOPY, etc.)
 *   is_store_opcode       — single-word store opcodes (MSTORE, etc.)
 *   load_opcode_addr_space  — map load opcode to address space
 *   store_opcode_addr_space — map store opcode to address space
 *   (addr_space_word_scale is in venomEffects)
 *   subst_operand         — substitute a variable in an operand
 *   subst_operands        — substitute a variable across all operands
 *   subst_operands_map    — substitute multiple variables via fmap
 *   is_lit_op             — check if operand is a literal
 *   lit_eq                — check if operand is a literal with a specific value
 *   is_power_of_two       — power-of-two check for bytes32
 *   word_log2             — integer log2 for bytes32
 *   is_comparator         — comparator opcode check (GT, LT, SGT, SLT)
 *   flip_comparison_opcode — flip comparison opcode (GT↔LT, SGT↔SLT)
 *)

Theory passSharedDefs
Ancestors
  venomInst venomEffects memLocDefs While

(* ===== Removability ===== *)

(* An instruction is removable (can be NOP'd) if:
   - it is not volatile
   - it is not a terminator
   - it has outputs (otherwise it's already effectful or a no-op) *)
Definition is_removable_def:
  is_removable inst <=>
    ~is_volatile inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_outputs <> []
End

(* ===== Instruction builders ===== *)

(* Replace an instruction with NOP, clearing operands and outputs *)
Definition mk_nop_inst_def:
  mk_nop_inst inst =
    inst with <| inst_opcode := NOP;
                 inst_operands := [];
                 inst_outputs := [] |>
End

(* Replace an instruction with ASSIGN from a single operand.
   Preserves inst_id and inst_outputs. *)
Definition mk_assign_inst_def:
  mk_assign_inst inst src_op =
    inst with <| inst_opcode := ASSIGN;
                 inst_operands := [src_op] |>
End

(* ===== PHI helpers ===== *)

(* Extract variable names that appear as value operands in PHI
   instructions. PHI operands are [Label l1, Var v1, Label l2, Var v2, ...].
   Returns the list of variable names [v1, v2, ...]. *)
Definition phi_value_vars_def:
  phi_value_vars [] = [] /\
  phi_value_vars [_] = [] /\
  phi_value_vars (Label _ :: Var v :: rest) = v :: phi_value_vars rest /\
  phi_value_vars (_ :: _ :: rest) = phi_value_vars rest
End

(* Collect all variable names that appear as value operands in any
   PHI instruction across the function. *)
Definition phi_used_vars_def:
  phi_used_vars fn =
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst.
        if inst.inst_opcode = PHI then phi_value_vars inst.inst_operands
        else [])
        bb.bb_instructions))
      fn.fn_blocks))
End

(* ===== Store opcode predicate ===== *)

(* Memory/storage/transient store instructions *)
Definition is_store_opcode_def:
  is_store_opcode MSTORE = T /\
  is_store_opcode MSTORE8 = T /\
  is_store_opcode SSTORE = T /\
  is_store_opcode TSTORE = T /\
  is_store_opcode _ = F
End

(* NOTE: is_alloca_op already in venomInst — use that instead *)

(* ===== Copy opcode predicate ===== *)

(* Bulk memory copy opcodes *)
Definition is_copy_opcode_def:
  is_copy_opcode MCOPY = T /\
  is_copy_opcode CALLDATACOPY = T /\
  is_copy_opcode CODECOPY = T /\
  is_copy_opcode DLOADBYTES = T /\
  is_copy_opcode RETURNDATACOPY = T /\
  is_copy_opcode _ = F
End

(* ===== Opcode ↔ address space mappings ===== *)

(* Map load opcode to its address space *)
Definition load_opcode_addr_space_def:
  load_opcode_addr_space MLOAD = AddrSp_Memory /\
  load_opcode_addr_space SLOAD = AddrSp_Storage /\
  load_opcode_addr_space TLOAD = AddrSp_Transient /\
  load_opcode_addr_space _ = AddrSp_Memory  (* default; shouldn't happen *)
End

(* Map store opcode to its address space *)
Definition store_opcode_addr_space_def:
  store_opcode_addr_space MSTORE = AddrSp_Memory /\
  store_opcode_addr_space MSTORE8 = AddrSp_Memory /\
  store_opcode_addr_space SSTORE = AddrSp_Storage /\
  store_opcode_addr_space TSTORE = AddrSp_Transient /\
  store_opcode_addr_space _ = AddrSp_Memory
End

(* ===== Operand substitution ===== *)

(* Substitute a single variable: if operand is Var old, replace with new_op *)
Definition subst_operand_def:
  subst_operand old new_op (Var v) =
    (if v = old then new_op else Var v) /\
  subst_operand old new_op op = op
End

(* Substitute across all operands of an instruction *)
Definition subst_operands_def:
  subst_operands old new_op inst =
    inst with inst_operands :=
      MAP (subst_operand old new_op) inst.inst_operands
End

(* Substitute a single operand using a substitution map *)
Definition subst_op_map_def:
  subst_op_map (subs : (string, operand) fmap) (Var v) =
    (case FLOOKUP subs v of SOME new_op => new_op | NONE => Var v) /\
  subst_op_map subs (Lit w) = Lit w /\
  subst_op_map subs (Label l) = Label l
End

(* Substitute multiple variables (from a finite map) *)
Definition subst_operands_map_def:
  subst_operands_map (subs : (string, operand) fmap) inst =
    inst with inst_operands :=
      MAP (subst_op_map subs) inst.inst_operands
End

(* ===== Copy propagation helpers ===== *)

(* An ASSIGN instruction is "forwardable" if:
   1. Source variable doesn't feed a PHI (literals always pass)
   2. Output variable doesn't feed a PHI
   Used by copy propagation (assign_elim) transfer, transform,
   and eliminated_vars computation.
   phi_vars = phi_used_vars fn *)
Definition is_forwardable_assign_def:
  is_forwardable_assign (phi_vars : string set) inst <=>
    inst.inst_opcode = ASSIGN /\
    (case (inst.inst_operands, inst.inst_outputs) of
       ([src_op], [out]) =>
         (case src_op of
            Var v => v NOTIN phi_vars
          | Lit _ => T
          | Label _ => F) /\
         out NOTIN phi_vars
     | _ => F)
End


(* ===== NOP clearing ===== *)

(* Remove NOP instructions from a block.
   Matches Python's IRBasicBlock.clear_nops(). *)
Definition clear_nops_block_def:
  clear_nops_block bb =
    bb with bb_instructions :=
      FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions
End

(* Remove NOPs from all blocks in a function *)
Definition clear_nops_function_def:
  clear_nops_function fn =
    fn with fn_blocks := MAP clear_nops_block fn.fn_blocks
End

Theorem clear_nops_function_identity_metadata_eq:
  !fn. fn_identity_metadata_eq (clear_nops_function fn) fn
Proof
  simp[clear_nops_function_def, fn_identity_metadata_eq_def]
QED

Theorem clear_nops_function_static_input_eq:
  !fn. fn_static_input_eq (clear_nops_function fn) fn
Proof
  simp[clear_nops_function_def, fn_static_input_eq_def]
QED

Theorem clear_nops_function_static_layout_eq:
  !fn. fn_static_layout_eq (clear_nops_function fn) fn
Proof
  simp[clear_nops_function_def, fn_static_layout_eq_def]
QED

Theorem clear_nops_function_fmp_convention_eq:
  !fn. fn_fmp_convention_eq (clear_nops_function fn) fn
Proof
  simp[clear_nops_function_def, fn_fmp_convention_eq_def]
QED

(* ===== Transitive use computation ===== *)

(* Collect output variables of instructions that use any variable in vars.
   Follows the use-def chain forward: if an instruction reads a var
   in vars, its outputs are added. Matches Python dfg.get_transitive_uses. *)
Definition use_step_def:
  use_step fn vars =
    FLAT (MAP (\bb.
      FLAT (MAP (\inst.
        if EXISTS (\op. case op of Var v => MEM v vars | _ => F)
                  inst.inst_operands
        then inst.inst_outputs
        else [])
        bb.bb_instructions))
      fn.fn_blocks)
End

(* Single step of transitive closure: add newly reachable vars. *)
Definition transitive_use_step_def:
  transitive_use_step fn vars =
    let new_vars = FILTER (\v. ~MEM v vars) (use_step fn vars) in
    if new_vars = [] then NONE
    else SOME (vars ++ new_vars)
End

(* Compute transitive closure of use-def chain from starting variables.
   Iterates until fixpoint via OWHILE (terminates because the set of
   accumulated variables grows strictly, bounded by total outputs). *)
Definition transitive_use_vars_def:
  transitive_use_vars fn vars =
    case OWHILE ISL (\v. case transitive_use_step fn (OUTL v) of
                           NONE => INR (OUTL v)
                         | SOME vs => INL vs)
                (INL vars) of
      SOME (INR result) => result
    | _ => vars
End

(* ===== General IR Utilities ===== *)

(* Check if operand is a literal *)
Definition is_lit_op_def:
  is_lit_op (Lit _) = T /\
  is_lit_op _ = F
End

(* Check if operand is a literal with a specific value *)
Definition lit_eq_def:
  lit_eq op v <=>
    case op of Lit w => (w = v) | _ => F
End

(* Power-of-two check: w ≠ 0 ∧ w AND (w - 1) = 0 *)
Definition is_power_of_two_def:
  is_power_of_two (w : bytes32) <=>
    w <> 0w /\ word_and w (w - 1w) = 0w
End

(* Integer log2: find n such that 2^n = w. Returns 0 for non-powers. *)
Definition word_log2_def:
  word_log2 (w : bytes32) : bytes32 =
    n2w (LOG2 (w2n w))
End

(* Comparator opcode check *)
Definition is_comparator_def:
  is_comparator (opc : opcode) <=>
    (opc = GT \/ opc = LT \/ opc = SGT \/ opc = SLT)
End

(* Flip comparison opcode: GT↔LT, SGT↔SLT *)
Definition flip_comparison_opcode_def:
  flip_comparison_opcode GT = (LT : opcode) /\
  flip_comparison_opcode LT = GT /\
  flip_comparison_opcode SGT = SLT /\
  flip_comparison_opcode SLT = SGT /\
  flip_comparison_opcode opc = opc
End

(* ===== Single Use Form ===== *)

(* Opcodes exempt from the single-use count. These are all instructions
   that SingleUseExpansion skips (sue_should_skip) because they don't go
   through normal EVM stack scheduling:
   - ASSIGN: copy instruction, no stack slot consumed
   - PHI: pseudo-instruction, lowered to parallel copies on CFG edges
   - PARAM/FMP_PARAM/RETPC_PARAM: pseudo-instructions lowered to hidden inputs
   - OFFSET: handled specially in venom_to_assembly (direct label+offset emit) *)
Definition sue_count_exempt_def:
  sue_count_exempt opc <=>
    opc = ASSIGN \/ opc = PHI \/ opc = OFFSET \/ is_param_opcode opc
End

(* Count uses of variable v across non-exempt instructions in a block. *)
Definition var_use_count_block_def:
  var_use_count_block v bb =
    LENGTH (FILTER (\inst.
      ~sue_count_exempt inst.inst_opcode /\
      MEM (Var v) inst.inst_operands)
      bb.bb_instructions)
End

(* Single Use Form: each variable is used at most once across all
   non-exempt instructions in the entire function.
   Established by SingleUseExpansion pass, required by DFT/venom_to_assembly. *)
Definition single_use_form_def:
  single_use_form fn <=>
    !v. SUM (MAP (var_use_count_block v) fn.fn_blocks) <= 1
End
