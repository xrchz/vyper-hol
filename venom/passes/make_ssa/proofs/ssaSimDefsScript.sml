(*
 * Make SSA Pass — Simulation Definitions
 *
 * Upstream: vyperlang/vyper@fa30658 (make_ssa pass)
 *
 * Extracted from makeSsaProofScript.sml to break circular dependencies.
 * Contains:
 *   - ssa_sim: simulation relation between original and SSA states
 *   - renamed_operand / inst_renamed: instruction correspondence
 *   - eval_operand_renamed / eval_operands_renamed: operand agreement
 *   - ssa_sim_update_var: simulation preserved by variable update
 *   - ssa_sim_phi_step: simulation preserved by PHI execution
 *   - utility lemmas (execution_equiv_UNIV, result_equiv_UNIV_refl, etc.)
 *)

Theory ssaSimDefs
Ancestors
  stateEquiv venomExecSemantics venomExecProofs venomWf venomState venomInst
  list rich_list finite_map pred_set

(* ==========================================================================
   Part 0: Utility lemmas
   ========================================================================== *)

Theorem execution_equiv_UNIV:
  execution_equiv UNIV s1 s2 <=>
    s1.vs_memory = s2.vs_memory /\
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
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next
Proof
  simp[execution_equiv_def, IN_UNIV]
QED

Theorem result_equiv_UNIV_refl:
  !r. result_equiv UNIV r r
Proof
  Cases >> simp[result_equiv_def, execution_equiv_def, state_equiv_def,
                IN_UNIV]
QED

(* ==========================================================================
   Part 1: Variable-only instructions preserve non-variable state
   ========================================================================== *)

Theorem step_inst_base_var_only_preserves_non_var:
  !inst s s'.
    (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = NOP) /\
    step_inst_base inst s = OK s' ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_code = s.vs_code /\
    s'.vs_params = s.vs_params /\
    s'.vs_fmp = s.vs_fmp /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rpt gen_tac >> strip_tac >> gvs[] >| [
    gvs[step_inst_base_def, AllCaseEqs(), update_var_def],
    gvs[step_inst_base_def]
  ]
QED

(* ==========================================================================
   Part 2: Simulation relation
   ========================================================================== *)

(* sigma : string -> string maps original var names to SSA version names.
   ssa_sim sigma s1 s2: s1 is original state, s2 is SSA state. *)
Definition ssa_sim_def:
  ssa_sim sigma s1 s2 <=>
    (!x v. lookup_var x s1 = SOME v ==>
           lookup_var (sigma x) s2 = SOME v) /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    (s1.vs_halted <=> s2.vs_halted) /\
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
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb
End

Theorem ssa_sim_implies_exec_equiv_UNIV:
  !sigma s1 s2. ssa_sim sigma s1 s2 ==> execution_equiv UNIV s1 s2
Proof
  rw[ssa_sim_def, execution_equiv_UNIV]
QED

Theorem ssa_sim_halted:
  !sigma s1 s2. ssa_sim sigma s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)
Proof
  simp[ssa_sim_def]
QED

Theorem ssa_sim_current_bb:
  !sigma s1 s2. ssa_sim sigma s1 s2 ==> (s1.vs_current_bb = s2.vs_current_bb)
Proof
  simp[ssa_sim_def]
QED

Theorem ssa_sim_prev_bb:
  !sigma s1 s2. ssa_sim sigma s1 s2 ==> (s1.vs_prev_bb = s2.vs_prev_bb)
Proof
  simp[ssa_sim_def]
QED

Theorem ssa_sim_identity:
  !s. ssa_sim I s s
Proof
  rw[ssa_sim_def, combinTheory.I_THM]
QED

Theorem ssa_sim_empty_vars:
  !sigma s. s.vs_vars = FEMPTY ==> ssa_sim sigma s s
Proof
  rw[ssa_sim_def, lookup_var_def, FLOOKUP_DEF]
QED

(* Like result_equiv UNIV, but OK/OK uses ssa_sim (existential sigma)
   instead of state_equiv (which requires identical variables). *)
Definition ssa_result_equiv_def:
  (ssa_result_equiv (OK s1) (OK s2) <=>
     ?sigma. ssa_sim sigma s1 s2) /\
  (ssa_result_equiv (Halt s1) (Halt s2) <=>
     execution_equiv UNIV s1 s2) /\
  (ssa_result_equiv (Abort a1 s1) (Abort a2 s2) <=>
     a1 = a2 /\ execution_equiv UNIV s1 s2) /\
  (ssa_result_equiv (IntRet v1 s1) (IntRet v2 s2) <=>
     execution_equiv UNIV s1 s2 /\ v1 = v2) /\
  (* Error message is an implementation detail; any error matches any error *)
  (ssa_result_equiv (Error _) (Error _) <=> T) /\
  (ssa_result_equiv (OK _) (Halt _) <=> F) /\
  (ssa_result_equiv (OK _) (Abort _ _) <=> F) /\
  (ssa_result_equiv (OK _) (IntRet _ _) <=> F) /\
  (ssa_result_equiv (OK _) (Error _) <=> F) /\
  (ssa_result_equiv (Halt _) (OK _) <=> F) /\
  (ssa_result_equiv (Halt _) (Abort _ _) <=> F) /\
  (ssa_result_equiv (Halt _) (IntRet _ _) <=> F) /\
  (ssa_result_equiv (Halt _) (Error _) <=> F) /\
  (ssa_result_equiv (Abort _ _) (OK _) <=> F) /\
  (ssa_result_equiv (Abort _ _) (Halt _) <=> F) /\
  (ssa_result_equiv (Abort _ _) (IntRet _ _) <=> F) /\
  (ssa_result_equiv (Abort _ _) (Error _) <=> F) /\
  (ssa_result_equiv (IntRet _ _) (OK _) <=> F) /\
  (ssa_result_equiv (IntRet _ _) (Halt _) <=> F) /\
  (ssa_result_equiv (IntRet _ _) (Abort _ _) <=> F) /\
  (ssa_result_equiv (IntRet _ _) (Error _) <=> F) /\
  (ssa_result_equiv (Error _) (OK _) <=> F) /\
  (ssa_result_equiv (Error _) (Halt _) <=> F) /\
  (ssa_result_equiv (Error _) (Abort _ _) <=> F) /\
  (ssa_result_equiv (Error _) (IntRet _ _) <=> F)
End

(* ==========================================================================
   Part 3: Renamed operand and instruction definitions
   ========================================================================== *)

(* Renamed operand: Var x becomes Var (sigma x), others unchanged *)
Definition renamed_operand_def:
  renamed_operand sigma (Var x) = Var (sigma x) /\
  renamed_operand sigma (Lit w) = Lit w /\
  renamed_operand sigma (Label l) = Label l
End

(* eval_operand agrees under ssa_sim and renamed_operand when original succeeds *)
Theorem eval_operand_renamed:
  !op sigma s1 s2 v.
    ssa_sim sigma s1 s2 /\
    eval_operand op s1 = SOME v ==>
    eval_operand (renamed_operand sigma op) s2 = SOME v
Proof
  Cases >> simp[renamed_operand_def, eval_operand_def, ssa_sim_def, lookup_var_def] >>
  rw[] >> gvs[]
QED

(* eval_operands agreement under renamed_operand + ssa_sim *)
Theorem eval_operands_renamed:
  !ops sigma s1 s2 vs.
    ssa_sim sigma s1 s2 /\
    eval_operands ops s1 = SOME vs ==>
    eval_operands (MAP (renamed_operand sigma) ops) s2 = SOME vs
Proof
  Induct >> rw[eval_operands_def, MAP] >>
  Cases_on `eval_operand h s1` >> gvs[] >>
  Cases_on `eval_operands ops s1` >> gvs[] >>
  imp_res_tac eval_operand_renamed >> simp[] >>
  first_x_assum (qspecl_then [`sigma`, `s1`, `s2`] mp_tac) >> simp[]
QED

(* An instruction pair is "renamed" if same opcode, renamed operands,
   same-length outputs, and the SSA output is fresh wrt sigma.
   NOTE: outputs are NOT MAP sigma inst1.inst_outputs — in SSA, the output
   gets a NEW version name (via push_version), which differs from sigma's
   current mapping. Sigma maps the original variable to its PREVIOUS version;
   the output introduces a fresh name. *)
Definition inst_renamed_def:
  inst_renamed sigma inst1 inst2 <=>
    inst2.inst_opcode = inst1.inst_opcode /\
    inst2.inst_id = inst1.inst_id /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs
End

(* Opcodes that produce an output variable via update_var.
   Non-output opcodes (MSTORE etc.) only modify memory/storage/logs, not vs_vars.
   Used to expose the specific sigma update in step_inst_base_renamed_sim. *)
Definition opcode_has_output_def:
  (* No output: writes, copies, control flow, assertions, misc *)
  opcode_has_output MSTORE = F /\
  opcode_has_output MSTORE8 = F /\
  opcode_has_output SSTORE = F /\
  opcode_has_output TSTORE = F /\
  opcode_has_output ISTORE = F /\
  opcode_has_output MCOPY = F /\
  opcode_has_output CALLDATACOPY = F /\
  opcode_has_output RETURNDATACOPY = F /\
  opcode_has_output CODECOPY = F /\
  opcode_has_output EXTCODECOPY = F /\
  opcode_has_output DLOADBYTES = F /\
  opcode_has_output LOG = F /\
  opcode_has_output NOP = F /\
  opcode_has_output ASSERT = F /\
  opcode_has_output ASSERT_UNREACHABLE = F /\
  opcode_has_output SELFDESTRUCT = F /\
  opcode_has_output INVALID = F /\
  (* Control flow terminators — no output *)
  opcode_has_output JMP = F /\
  opcode_has_output JNZ = F /\
  opcode_has_output DJMP = F /\
  opcode_has_output RET = F /\
  opcode_has_output RETURN = F /\
  opcode_has_output REVERT = F /\
  opcode_has_output STOP = F /\
  opcode_has_output SINK = F /\
  (* Extended terminators — no output *)
  opcode_has_output DRET = F /\
  opcode_has_output RETFMP = F /\
  (* Has output: arithmetic *)
  opcode_has_output ADD = T /\
  opcode_has_output SUB = T /\
  opcode_has_output MUL = T /\
  opcode_has_output Div = T /\
  opcode_has_output SDIV = T /\
  opcode_has_output Mod = T /\
  opcode_has_output SMOD = T /\
  opcode_has_output Exp = T /\
  opcode_has_output ADDMOD = T /\
  opcode_has_output MULMOD = T /\
  (* Has output: comparison *)
  opcode_has_output EQ = T /\
  opcode_has_output LT = T /\
  opcode_has_output GT = T /\
  opcode_has_output SLT = T /\
  opcode_has_output SGT = T /\
  opcode_has_output ISZERO = T /\
  (* Has output: bitwise *)
  opcode_has_output AND = T /\
  opcode_has_output OR = T /\
  opcode_has_output XOR = T /\
  opcode_has_output NOT = T /\
  opcode_has_output SHL = T /\
  opcode_has_output SHR = T /\
  opcode_has_output SAR = T /\
  opcode_has_output SIGNEXTEND = T /\
  opcode_has_output BYTE = T /\
  (* Has output: memory/storage/immutable reads *)
  opcode_has_output MLOAD = T /\
  opcode_has_output MEMTOP = T /\
  opcode_has_output SLOAD = T /\
  opcode_has_output TLOAD = T /\
  opcode_has_output ILOAD = T /\
  opcode_has_output DLOAD = T /\
  (* Has output: environment reads *)
  opcode_has_output CALLER = T /\
  opcode_has_output ADDRESS = T /\
  opcode_has_output CALLVALUE = T /\
  opcode_has_output CALLDATALOAD = T /\
  opcode_has_output CALLDATASIZE = T /\
  opcode_has_output GAS = T /\
  opcode_has_output ORIGIN = T /\
  opcode_has_output GASPRICE = T /\
  opcode_has_output CHAINID = T /\
  opcode_has_output COINBASE = T /\
  opcode_has_output TIMESTAMP = T /\
  opcode_has_output NUMBER = T /\
  opcode_has_output PREVRANDAO = T /\
  opcode_has_output GASLIMIT = T /\
  opcode_has_output BASEFEE = T /\
  opcode_has_output BLOBBASEFEE = T /\
  opcode_has_output RETURNDATASIZE = T /\
  opcode_has_output CODESIZE = T /\
  opcode_has_output SELFBALANCE = T /\
  opcode_has_output BALANCE = T /\
  opcode_has_output BLOCKHASH = T /\
  opcode_has_output BLOBHASH = T /\
  opcode_has_output EXTCODESIZE = T /\
  opcode_has_output EXTCODEHASH = T /\
  (* Has output: hashing, external calls, SSA *)
  opcode_has_output SHA3 = T /\
  opcode_has_output CALL = T /\
  opcode_has_output STATICCALL = T /\
  opcode_has_output DELEGATECALL = T /\
  opcode_has_output CREATE = T /\
  opcode_has_output CREATE2 = T /\
  opcode_has_output PHI = T /\
  opcode_has_output ASSIGN = T /\
  opcode_has_output PARAM = T /\
  opcode_has_output ALLOCA = T /\
  opcode_has_output GETFMP = T /\
  opcode_has_output SETFMP = F /\
  opcode_has_output DALLOCA = T /\
  opcode_has_output INITIAL_FMP = T /\
  opcode_has_output BUMP = T /\
  opcode_has_output FMP_PARAM = T /\
  opcode_has_output RETPC_PARAM = T /\
  opcode_has_output INVOKE = F /\  (* outputs unconstrained; handled separately *)
  opcode_has_output OFFSET = T
End

(* Build-time exhaustiveness audit: every opcode constructor must reduce to a
   concrete Boolean under the explicit classification equations above. *)
val _ = app (fn op_tm =>
  let
    val th = SIMP_CONV (srw_ss()) [opcode_has_output_def]
      (mk_comb(``opcode_has_output``, op_tm));
    val r = rhs (concl th)
  in
    if aconv r T orelse aconv r F then ()
    else raise Fail "opcode_has_output_def is not constructor-exhaustive"
  end) (TypeBase.constructors_of ``:opcode``);

Theorem opcode_has_output_extended_terminators[simp]:
  opcode_has_output DRET = F /\ opcode_has_output RETFMP = F
Proof
  simp[opcode_has_output_def]
QED

(* Number of syntactic outputs that step_inst_base actually binds.  Most
   producers bind one output; BUMP binds its base and bumped pointer in order. *)
Definition bound_output_count_def:
  bound_output_count op =
    if op = BUMP then (2:num) else if opcode_has_output op then 1 else 0
End

(* Update the renaming map for exactly the outputs bound by the opcode. *)
Definition output_sigma_def:
  output_sigma op outs1 outs2 sigma =
    FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma
      (ZIP (TAKE (bound_output_count op) outs1,
            TAKE (bound_output_count op) outs2))
End

(* Every semantically bound SSA output is fresh for the variables that existed
   before the instruction.  Distinct target names make sequential updates safe;
   the source output names need not be distinct. *)
Definition output_fresh_def:
  output_fresh sigma inst1 inst2 s1 <=>
    let n = bound_output_count inst1.inst_opcode in
      n <= LENGTH inst1.inst_outputs /\
      n <= LENGTH inst2.inst_outputs /\
      ALL_DISTINCT (TAKE n inst2.inst_outputs) /\
      !i x. i < n /\ lookup_var x s1 <> NONE /\
            x <> EL i inst1.inst_outputs ==>
            sigma x <> EL i inst2.inst_outputs
End

Theorem bound_output_count_BUMP[simp]:
  bound_output_count BUMP = 2
Proof
  simp[bound_output_count_def]
QED

Theorem bound_output_count_extended[simp]:
  bound_output_count GETFMP = 1 /\
  bound_output_count SETFMP = 0 /\
  bound_output_count DALLOCA = 1 /\
  bound_output_count INITIAL_FMP = 1 /\
  bound_output_count BUMP = 2 /\
  bound_output_count FMP_PARAM = 1 /\
  bound_output_count RETPC_PARAM = 1 /\
  bound_output_count LOG = 0
Proof
  simp[bound_output_count_def, opcode_has_output_def]
QED

Theorem output_sigma_zero:
  bound_output_count op = 0 ==> output_sigma op outs1 outs2 sigma = sigma
Proof
  simp[output_sigma_def]
QED

Theorem output_sigma_one:
  bound_output_count op = 1 /\ outs1 <> [] /\ outs2 <> [] ==>
  output_sigma op outs1 outs2 sigma = (HD outs1 =+ HD outs2) sigma
Proof
  Cases_on `outs1` >> Cases_on `outs2` >> simp[output_sigma_def]
QED

Theorem output_sigma_BUMP[simp]:
  output_sigma BUMP (o1::o1'::outs1) (o2::o2'::outs2) sigma =
    (o1' =+ o2') ((o1 =+ o2) sigma)
Proof
  simp[output_sigma_def, bound_output_count_def]
QED

(* ==========================================================================
   Part 4: ssa_sim preservation lemmas
   ========================================================================== *)

(* Updating the free-memory pointer to the same value on both sides preserves
   simulation.  Consumers should use this boundary rather than unfold the
   full state relation. *)
Theorem ssa_sim_fmp_update:
  !sigma s1 s2 fmp.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (s1 with vs_fmp := fmp) (s2 with vs_fmp := fmp)
Proof
  rw[ssa_sim_def, lookup_var_def]
QED

(* ssa_sim is preserved by update_var on corresponding variables,
   provided the new SSA name out2 doesn't alias sigma for any
   DEFINED variable in s1 other than out1.
   Weakened: only needs non-aliasing for variables with values in s1. *)
Theorem ssa_sim_update_var:
  !sigma s1 s2 out1 out2 v.
    ssa_sim sigma s1 s2 /\
    (!x. x <> out1 /\ lookup_var x s1 <> NONE ==> sigma x <> out2) ==>
    ssa_sim ((out1 =+ out2) sigma)
      (update_var out1 v s1) (update_var out2 v s2)
Proof
  rw[ssa_sim_def, update_var_def,
     lookup_var_def, FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `out1 = x` >> gvs[lookup_var_def, FLOOKUP_UPDATE] >>
  `FLOOKUP s1.vs_vars x <> NONE` by (Cases_on `FLOOKUP s1.vs_vars x` >> gvs[]) >>
  metis_tac[]
QED

(* DALLOCA-style updates change the common FMP and return a common value in
   corresponding fresh outputs. *)
Theorem ssa_sim_fmp_update_var:
  !sigma s1 s2 out1 out2 value fmp.
    ssa_sim sigma s1 s2 /\
    (!x. x <> out1 /\ lookup_var x s1 <> NONE ==> sigma x <> out2) ==>
    ssa_sim ((out1 =+ out2) sigma)
      (update_var out1 value (s1 with vs_fmp := fmp))
      (update_var out2 value (s2 with vs_fmp := fmp))
Proof
  rpt strip_tac >> irule ssa_sim_update_var >>
  simp[lookup_var_def] >>
  irule ssa_sim_fmp_update >> simp[]
QED

(* ssa_sim allows replacing sigma when the new sigma agrees on all defined vars *)
Theorem ssa_sim_sigma_replace:
  !sigma sigma' s1 s2.
    ssa_sim sigma s1 s2 /\
    (!x. lookup_var x s1 <> NONE ==> sigma' x = sigma x) ==>
    ssa_sim sigma' s1 s2
Proof
  rw[ssa_sim_def] >> rpt strip_tac >>
  `lookup_var x s1 <> NONE` by (Cases_on `lookup_var x s1` >> gvs[]) >>
  metis_tac[]
QED

(* FOLDL update_var preserves ssa_sim for paired output lists.
   Used for multi-output INVOKE where both sides bind the same values
   to differently-named outputs. *)
Theorem foldl_update_var_ssa_sim:
  !outs1 outs2 vals sigma s1 s2.
    ssa_sim sigma s1 s2 /\
    LENGTH outs1 = LENGTH vals /\ LENGTH outs2 = LENGTH vals /\
    ALL_DISTINCT outs2 /\
    (!i. i < LENGTH outs1 ==>
         !x. lookup_var x s1 <> NONE ==>
             x <> EL i outs1 ==> sigma x <> EL i outs2) ==>
    ssa_sim (FOLDL (\s (o1,o2). (o1 =+ o2) s) sigma (ZIP (outs1, outs2)))
      (FOLDL (\st (nm,vl). update_var nm vl st) s1 (ZIP (outs1, vals)))
      (FOLDL (\st (nm,vl). update_var nm vl st) s2 (ZIP (outs2, vals)))
Proof
  Induct_on `outs1`
  >- (rpt strip_tac >> gvs[LENGTH_NIL, ZIP_def, FOLDL])
  >> rw[] >>
  Cases_on `outs2` >> gvs[] >>
  Cases_on `vals` >> gvs[] >>
  simp[ZIP_def, FOLDL] >>
  first_x_assum irule >>
  gvs[] >>
  conj_tac
  >- (rpt strip_tac >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      Cases_on `x = h`
      >- (gvs[ALL_DISTINCT, MEM_EL] >> metis_tac[])
      >> gvs[combinTheory.APPLY_UPDATE_THM] >>
         `lookup_var x s1 <> NONE` by (
           gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
         first_x_assum (qspec_then `SUC i` mp_tac) >>
         simp[] >> metis_tac[])
  >> irule ssa_sim_update_var >> gvs[] >>
     qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >> simp[]
QED

(* ssa_sim is preserved by side-effect-only state changes that preserve vs_vars.
   Used for MSTORE, SSTORE, etc. where no variables are modified. *)
Theorem ssa_sim_non_var_update:
  !sigma s1 s2 s1' s2'.
    ssa_sim sigma s1 s2 /\
    (!x. lookup_var x s1' = lookup_var x s1) /\
    (!x. lookup_var x s2' = lookup_var x s2) /\
    s1'.vs_memory = s2'.vs_memory /\
    s1'.vs_transient = s2'.vs_transient /\
    (s1'.vs_halted <=> s2'.vs_halted) /\
    s1'.vs_returndata = s2'.vs_returndata /\
    s1'.vs_accounts = s2'.vs_accounts /\
    s1'.vs_call_ctx = s2'.vs_call_ctx /\
    s1'.vs_tx_ctx = s2'.vs_tx_ctx /\
    s1'.vs_block_ctx = s2'.vs_block_ctx /\
    s1'.vs_logs = s2'.vs_logs /\
    s1'.vs_immutables = s2'.vs_immutables /\
    s1'.vs_data_section = s2'.vs_data_section /\
    s1'.vs_labels = s2'.vs_labels /\
    s1'.vs_code = s2'.vs_code /\
    s1'.vs_params = s2'.vs_params /\
    s1'.vs_fmp = s2'.vs_fmp /\
    s1'.vs_call_entry_fmp = s2'.vs_call_entry_fmp /\
    s1'.vs_initial_fmp = s2'.vs_initial_fmp /\
    s1'.vs_return_pc_token = s2'.vs_return_pc_token /\
    s1'.vs_prev_hashes = s2'.vs_prev_hashes /\
    s1'.vs_allocas = s2'.vs_allocas /\
    s1'.vs_alloca_next = s2'.vs_alloca_next /\
    s1'.vs_current_bb = s2'.vs_current_bb /\
    s1'.vs_prev_bb = s2'.vs_prev_bb ==>
    ssa_sim sigma s1' s2'
Proof
  rw[ssa_sim_def] >> metis_tac[]
QED

(* Stepping a PHI on the SSA side maintains ssa_sim.
   The PHI reads the sigma-image of variable x (matched via prev_bb)
   and writes to fresh output out. Under the new semantics, PHI execution
   goes through eval_one_phi, not step_inst_base. *)
Theorem ssa_sim_phi_step:
  !sigma s1 s2 inst x out prev v.
    ssa_sim sigma s1 s2 /\
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    s2.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var (sigma x)) /\
    lookup_var x s1 = SOME v /\
    (!y. y <> x ==> sigma y <> out) ==>
    eval_one_phi s2 inst = SOME (out, v) /\
    ssa_sim ((x =+ out) sigma) s1 (update_var out v s2)
Proof
  rw[eval_one_phi_def] >>
  `lookup_var (sigma x) s2 = SOME v` by gvs[ssa_sim_def] >>
  gvs[eval_operand_def, lookup_var_def] >>
  rw[ssa_sim_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE, combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `x = x'` >> gvs[ssa_sim_def, lookup_var_def]
QED

(* Peel one non-terminator, non-INVOKE instruction from run_block.
   After stepping the instruction and incrementing inst_idx,
   run_block continues with the updated state. *)
(* jump_to preserves ssa_sim with the same sigma *)
Theorem jump_to_ssa_sim:
  !sigma s1 s2 lbl.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[ssa_sim_def, jump_to_def, lookup_var_def]
QED

(* halt_state preserves ssa_sim *)
Theorem halt_state_ssa_sim:
  !sigma s1 s2.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (halt_state s1) (halt_state s2)
Proof
  rw[ssa_sim_def, halt_state_def, lookup_var_def]
QED

(* set_returndata preserves ssa_sim *)
Theorem set_returndata_ssa_sim:
  !sigma s1 s2 rd.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (set_returndata rd s1) (set_returndata rd s2)
Proof
  rw[ssa_sim_def, set_returndata_def, lookup_var_def]
QED

(* revert_state preserves ssa_sim (revert doesn't change vars) *)
Theorem revert_state_ssa_sim:
  !sigma s1 s2.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (revert_state s1) (revert_state s2)
Proof
  rw[ssa_sim_def, revert_state_def, lookup_var_def]
QED

(* General non-terminator peel: for any step_inst result *)
Theorem exec_block_peel_non_term:
  !bb fuel ctx s inst.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode ==>
    exec_block fuel ctx bb s =
    case step_inst fuel ctx inst s of
      OK s' => exec_block fuel ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx)
    | Halt h => Halt h | Abort a' s' => Abort a' s'
    | IntRet vals s' => IntRet vals s' | Error e => Error e
Proof
  rpt strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def]
QED

Theorem exec_block_step_non_term:
  !bb fuel ctx s inst s'.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK s' ==>
    exec_block fuel ctx bb s =
    exec_block fuel ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    metis_tac[step_inst_non_invoke] >>
  simp[]
QED

Theorem exec_block_step_term:
  !bb fuel ctx s inst.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    exec_block fuel ctx bb s =
    case step_inst_base inst s of
      OK s'' => if s''.vs_halted then Halt s'' else OK s''
    | Halt h => Halt h | Abort a' s' => Abort a' s'
    | IntRet vals s' => IntRet vals s' | Error e => Error e
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def, step_inst_non_invoke]
QED


Theorem ssa_sim_update_inst_idx:
  !sigma s1 s2 i j.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (s1 with vs_inst_idx := i) (s2 with vs_inst_idx := j)
Proof
  rw[ssa_sim_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* ===== Sigma Congruence for Partial Agreement ===== *)

(* Weaker sigma congruence: only need agreement on defined variables.
   Since ssa_sim only constrains variables where lookup_var x s1 = SOME v,
   agreement on FDOM s1.vs_vars suffices. *)
Theorem ssa_sim_sigma_cong_live:
  !f g s1 s2.
    ssa_sim f s1 s2 /\
    (!x. x IN FDOM s1.vs_vars ==> g x = f x) ==>
    ssa_sim g s1 s2
Proof
  rw[ssa_sim_def, lookup_var_def] >>
  rpt strip_tac >>
  `x IN FDOM s1.vs_vars` by fs[flookup_thm] >>
  `g x = f x` by metis_tac[] >>
  metis_tac[]
QED

(* ===== State Patching for Pruned SSA ===== *)

(* Construct a patched state s2' that satisfies ssa_sim with a new sigma',
   regardless of what sigma the original s2 was simulating with.
   The only variables that change are IMAGE sigma' (FDOM s1.vs_vars).
   Used for state-patching approach in pruned SSA simulation. *)
Theorem ssa_sim_state_patch:
  !sigma sigma' s1 s2.
    ssa_sim sigma s1 s2 /\
    INJ sigma' (FDOM s1.vs_vars) UNIV ==>
    ?s2'.
      ssa_sim sigma' s1 s2' /\
      state_equiv (IMAGE sigma' (FDOM s1.vs_vars)) s2 s2'
Proof
  rpt strip_tac >>
  qexists_tac `s2 with vs_vars :=
    FUNION (MAP_KEYS sigma' s1.vs_vars) s2.vs_vars` >>
  conj_tac
  >- ((* ssa_sim sigma' s1 s2' *)
    fs[ssa_sim_def, lookup_var_def, FLOOKUP_FUNION] >>
    rpt strip_tac >>
    `x IN FDOM s1.vs_vars /\ s1.vs_vars ' x = v` by
      fs[flookup_thm] >>
    `sigma' x IN FDOM (MAP_KEYS sigma' s1.vs_vars)` by
      simp[MAP_KEYS_def] >>
    `(MAP_KEYS sigma' s1.vs_vars) ' (sigma' x) = v` by
      metis_tac[MAP_KEYS_def] >>
    simp[FLOOKUP_DEF])
  >- ((* state_equiv (IMAGE sigma' ...) s2 s2' *)
    simp[state_equiv_def, execution_equiv_def, lookup_var_def,
         FLOOKUP_FUNION] >>
    rpt strip_tac >>
    `v NOTIN FDOM (MAP_KEYS sigma' s1.vs_vars)` by
      simp[MAP_KEYS_def] >>
    simp[FLOOKUP_DEF])
QED

(* run_block_OK_inst_idx_0 is already available from venomExecProofsTheory *)
