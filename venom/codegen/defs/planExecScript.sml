(*
 * Plan Executor
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Mechanical translation: stack_op list -> asm_inst list.
 * No intelligence — just maps each stack_op to assembly instructions.
 *
 * TOP-LEVEL:
 *   execute_plan — convert stack_op list to asm_inst list
 *)

Theory planExec
Ancestors
  stackPlanGen

(* ===== SWAP/DUP Name Tables (1..16) ===== *)

Definition swap_name_def:
  swap_name (n:num) =
    if n = 1 then "SWAP1" else if n = 2 then "SWAP2"
    else if n = 3 then "SWAP3" else if n = 4 then "SWAP4"
    else if n = 5 then "SWAP5" else if n = 6 then "SWAP6"
    else if n = 7 then "SWAP7" else if n = 8 then "SWAP8"
    else if n = 9 then "SWAP9" else if n = 10 then "SWAP10"
    else if n = 11 then "SWAP11" else if n = 12 then "SWAP12"
    else if n = 13 then "SWAP13" else if n = 14 then "SWAP14"
    else if n = 15 then "SWAP15" else if n = 16 then "SWAP16"
    else "SWAP?" (* should not happen *)
End

Definition dup_name_def:
  dup_name (n:num) =
    if n = 1 then "DUP1" else if n = 2 then "DUP2"
    else if n = 3 then "DUP3" else if n = 4 then "DUP4"
    else if n = 5 then "DUP5" else if n = 6 then "DUP6"
    else if n = 7 then "DUP7" else if n = 8 then "DUP8"
    else if n = 9 then "DUP9" else if n = 10 then "DUP10"
    else if n = 11 then "DUP11" else if n = 12 then "DUP12"
    else if n = 13 then "DUP13" else if n = 14 then "DUP14"
    else if n = 15 then "DUP15" else if n = 16 then "DUP16"
    else "DUP?" (* should not happen *)
End

(* ===== Execute a Single Stack Operation ===== *)

Definition exec_stack_op_def:
  exec_stack_op initial_fmp (SOPush (Lit v)) =
    (* Python: PUSH(wrap256(value)) → minimal big-endian byte list.
       0 → PUSH0, 42 → PUSH1 42, etc. encode_num_bytes gives minimal. *)
    ([AsmPush (encode_num_bytes (w2n v))] : asm_inst list) ∧
  exec_stack_op initial_fmp (SOPush (Var _)) = [] ∧
  exec_stack_op initial_fmp (SOPush (Label l)) = [AsmPushLabel l] ∧
  exec_stack_op initial_fmp (SOPop n) = REPLICATE n (AsmOp "POP") ∧
  exec_stack_op initial_fmp (SOSwap n) = [AsmOp (swap_name n)] ∧
  exec_stack_op initial_fmp (SODup n) = [AsmOp (dup_name n)] ∧
  exec_stack_op initial_fmp (SOPoke _ _) = [] ∧
  exec_stack_op initial_fmp (SOSpill off) =
    [AsmPush (encode_num_bytes off); AsmOp "MSTORE"] ∧
  exec_stack_op initial_fmp (SORestore off) =
    [AsmPush (encode_num_bytes off); AsmOp "MLOAD"] ∧
  exec_stack_op initial_fmp (SOEmit opc) = [AsmOp opc] ∧
  exec_stack_op initial_fmp SOInitialFmp =
    [AsmPush (encode_num_bytes initial_fmp)] ∧
  exec_stack_op initial_fmp (SOLabel lbl) = [AsmLabel lbl] ∧
  exec_stack_op initial_fmp (SOPushLabel lbl) = [AsmPushLabel lbl] ∧
  exec_stack_op initial_fmp (SOPushOfst lbl off) = [AsmPushOfst lbl off]
End

(* ===== Execute Full Plan ===== *)

Definition execute_plan_def:
  execute_plan initial_fmp ops = FLAT (MAP (exec_stack_op initial_fmp) ops)
End
