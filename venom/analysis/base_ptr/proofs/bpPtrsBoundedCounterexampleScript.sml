(*
 * Counterexample: step_preserves_safety is FALSE
 *
 * step_preserves_safety says that for any non-terminator, non-ext-call
 * instruction, stepping preserves alloca_safe_access and ptrs_in_alloca_bounds.
 *
 * This is FALSE because a pointer-preserving ADD can produce a value
 * outside alloca bounds. If ptr=0w (in [0,64)) and k=9999w, then
 * ADD [Var "ptr"; Var "k"] produces ptr2=9999w, which is NOT in [0,64).
 * ptrs_in_alloca_bounds fails because the new value is OOB.
 *
 * Note: alloca_safe_access is vacuously TRUE in the post-state because
 * ptr2=9999w is NOT in any alloca region (the memory-access antecedent
 * requires off <= w2n w < off + asz). So the counterexample falsifies
 * ptrs_in_alloca_bounds, not alloca_safe_access.
 *)

Theory bpPtrsBoundedCounterexample
Ancestors
  basePtrDefs pointerConfinedDefs allocaRemapDefs venomInst
  venomExecSemantics venomWf memLocDefs venomInstProofs
  pred_set finite_map list option While sum arithmetic words

(* Function: ALLOCA 64 -> "ptr", ADD [ptr; k] -> "ptr2", MSTORE [ptr2; data] *)
Definition ce3_fn_def:
  ce3_fn : ir_function = mk_raw_function "ce3_test" [
    <| bb_label := "entry";
       bb_instructions := [
         mk_inst 0 ALLOCA [Lit (n2w 64)] ["ptr"];
         mk_inst 1 ADD [Var "ptr"; Var "k"] ["ptr2"];
         mk_inst 2 MSTORE [Var "ptr2"; Var "data"] []
       ]
    |>
  ]
End

(* State: alloca id=0, base=0, size=64; ptr=0w, ptr2=0w, k=9999w, data=0w *)
Definition ce3_state_def:
  ce3_state = (init_venom_state "entry") with <|
    vs_vars := FEMPTY |+ ("ptr", n2w 0) |+ ("ptr2", n2w 0) |+ ("k", n2w 9999) |+ ("data", n2w 0);
    vs_allocas := FEMPTY |+ (0, (0, 64));
    vs_memory := REPLICATE 64 (0w:word8);
    vs_alloca_next := 64
  |>
End

(* Post-ADD state: ptr2 updated to 0w + 9999w = 9999w *)
Definition ce3_v_def:
  ce3_v = ce3_state with <|
    vs_vars := ce3_state.vs_vars |+ ("ptr2", n2w 9999)
  |>
End

Definition ce3_roots_def:
  ce3_roots = alloca_roots ce3_fn
End

Definition ce3_inst_def:
  ce3_inst = mk_inst 1 ADD [Var "ptr"; Var "k"] ["ptr2"]
End

Definition ce3_bb_def:
  ce3_bb : basic_block = <|
    bb_label := "entry";
    bb_instructions := [
      mk_inst 0 ALLOCA [Lit (n2w 64)] ["ptr"];
      mk_inst 1 ADD [Var "ptr"; Var "k"] ["ptr2"];
      mk_inst 2 MSTORE [Var "ptr2"; Var "data"] []
    ]
  |>
End

(* ---- Helper lemmas ---- *)

val dimindex_256 = fcpLib.DIMINDEX (Arbnum.fromInt 256)

Theorem ce3_w2n_9999:
  w2n (9999w:256 word) = 9999
Proof
  simp[w2n_n2w, LESS_MOD] >>
  `dimindex(:64) < dimindex(:256)` by
    (simp[dimindex_64, dimindex_256] >> decide_tac) >>
  `dimword(:64) < dimword(:256)` by
    metis_tac[dimindex_dimword_lt_iso] >>
  `9999 < dimword(:64)` by (simp[dimword_64] >> decide_tac) >>
  decide_tac
QED

Theorem ce3_w2n_0:
  w2n (0w:256 word) = 0
Proof
  simp[w2n_n2w, LESS_MOD]
QED

Theorem ce3_w2n_32:
  w2n (32w:256 word) = 32
Proof
  simp[w2n_n2w, LESS_MOD] >>
  `dimindex(:64) < dimindex(:256)` by
    (simp[dimindex_64, dimindex_256] >> decide_tac) >>
  `dimword(:64) < dimword(:256)` by
    metis_tac[dimindex_dimword_lt_iso] >>
  `32 < dimword(:64)` by (simp[dimword_64] >> decide_tac) >>
  decide_tac
QED

Theorem ce3_mem_write_ops_mstore:
  mem_write_ops (mk_inst 2 MSTORE [Var "ptr2"; Var "data"] []) =
    SOME <|iao_ofst := Var "ptr2"; iao_size := SOME (Lit 32w);
            iao_max_size := SOME (Lit 32w)|>
Proof
  EVAL_TAC
QED

Theorem ce3_alloca_roots:
  alloca_roots ce3_fn = {"ptr"}
Proof
  simp[alloca_roots_def, ce3_fn_def, mk_raw_function_def, fn_insts_def,
       mk_inst_def, inst_output_def, EXTENSION] >>
  gen_tac >> gvs[fn_insts_blocks_def, MEM, AllCaseEqs()] >> eq_tac >> rpt strip_tac >> gvs[]
  >- (qexists `<|inst_id := 0; inst_opcode := ALLOCA; inst_operands := [Lit 64w]; inst_outputs := ["ptr"]|>` >> simp[])
  >> pop_assum mp_tac >> simp[]
QED

Theorem ce3_pointer_use_step:
  pointer_use_step ce3_fn ["ptr"] = ["ptr2"]
Proof
  EVAL_TAC
QED

Theorem ce3_pointer_use_step_step1:
  pointer_use_step_step ce3_fn ["ptr"] = SOME ["ptr"; "ptr2"]
Proof
  EVAL_TAC
QED

Theorem ce3_pointer_use_step_step2:
  pointer_use_step_step ce3_fn ["ptr"; "ptr2"] = NONE
Proof
  EVAL_TAC
QED

Theorem ce3_pointer_use_vars:
  pointer_use_vars ce3_fn ["ptr"] = ["ptr"; "ptr2"]
Proof
  simp[pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[ISL, OUTL, ce3_pointer_use_step_step1] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[ISL, OUTL, ce3_pointer_use_step_step2] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[ISL]
QED

Theorem ce3_pointer_derived_vars:
  pointer_derived_vars ce3_fn ce3_roots = {"ptr"; "ptr2"}
Proof
  simp[pointer_derived_vars_def, ce3_roots_def, ce3_alloca_roots, SET_TO_LIST_SING, ce3_pointer_use_vars, EXTENSION] >>
  gen_tac >> Cases_on `x = "ptr"` >> Cases_on `x = "ptr2"` >> simp[]
QED

Theorem ce3_step_inst_base:
  step_inst_base ce3_inst ce3_state = OK ce3_v
Proof
  EVAL_TAC >> simp[WORD_ADD_0]
QED

Theorem ce3_not_terminator:
  ¬is_terminator ce3_inst.inst_opcode
Proof
  simp[ce3_inst_def, mk_inst_def, is_terminator_def]
QED

Theorem ce3_not_ext_call_op:
  ¬is_ext_call_op ce3_inst.inst_opcode
Proof
  simp[is_ext_call_op_def, ce3_inst_def, mk_inst_def]
QED

Theorem ce3_alloca_memory_bound:
  ∀aid off asz.
    FLOOKUP ce3_state.vs_allocas aid = SOME (off, asz) ⇒
    off + asz ≤ LENGTH ce3_state.vs_memory
Proof
  strip_tac >> mp_tac ce3_state_def >>
  simp[FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
  Cases_on `aid` >> gvs[] >> decide_tac
QED

Theorem ce3_lookup_ptr:
  lookup_var "ptr" ce3_state = SOME (0w:256 word)
Proof
  EVAL_TAC
QED

Theorem ce3_lookup_ptr2:
  lookup_var "ptr2" ce3_state = SOME (0w:256 word)
Proof
  EVAL_TAC
QED

Theorem ce3_lookup_ptr2_v:
  lookup_var "ptr2" ce3_v = SOME (9999w:256 word)
Proof
  EVAL_TAC
QED

Theorem ce3_lookup_ptr_v:
  lookup_var "ptr" ce3_v = SOME (0w:256 word)
Proof
  EVAL_TAC
QED

Theorem ce3_eval_operand_lit32:
  eval_operand (Lit 32w) ce3_state = SOME (32w:256 word)
Proof
  EVAL_TAC
QED

Theorem ce3_eval_operand_lit32_v:
  eval_operand (Lit 32w) ce3_v = SOME (32w:256 word)
Proof
  EVAL_TAC
QED

(* mem_write_ops and mem_read_ops for all ce3 instructions *)
Theorem ce3_mem_write_ops_alloca:
  mem_write_ops (mk_inst 0 ALLOCA [Lit 64w] ["ptr"]) = NONE
Proof
  EVAL_TAC
QED

Theorem ce3_mem_read_ops_alloca:
  mem_read_ops (mk_inst 0 ALLOCA [Lit 64w] ["ptr"]) = NONE
Proof
  EVAL_TAC
QED

Theorem ce3_mem_write_ops_add:
  mem_write_ops (mk_inst 1 ADD [Var "ptr"; Var "k"] ["ptr2"]) = NONE
Proof
  EVAL_TAC
QED

Theorem ce3_mem_read_ops_add:
  mem_read_ops (mk_inst 1 ADD [Var "ptr"; Var "k"] ["ptr2"]) = NONE
Proof
  EVAL_TAC
QED

Theorem ce3_mem_read_ops_mstore:
  mem_read_ops (mk_inst 2 MSTORE [Var "ptr2"; Var "data"] []) = NONE
Proof
  EVAL_TAC
QED

(* ---- alloca_safe_access for ce3_state ---- *)

Theorem ce3_alloca_safe_access:
  alloca_safe_access ce3_fn ce3_roots ce3_state
Proof
  simp[alloca_safe_access_def, ce3_pointer_derived_vars] >>
  rpt strip_tac >>
  gvs[ce3_fn_def, mk_raw_function_def, MEM] >>
  gvs[ce3_mem_write_ops_alloca, ce3_mem_read_ops_alloca] >>
  gvs[ce3_mem_write_ops_add, ce3_mem_read_ops_add] >>
  gvs[ce3_mem_write_ops_mstore, ce3_mem_read_ops_mstore,
      ce3_lookup_ptr2, ce3_w2n_0, ce3_eval_operand_lit32, ce3_w2n_32,
      ce3_state_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> decide_tac
QED

(* ---- ptrs_in_alloca_bounds for ce3_state ---- *)

Theorem ce3_ptrs_in_alloca_bounds_s:
  ptrs_in_alloca_bounds ce3_fn ce3_roots ce3_state
Proof
  simp[Once ptrs_in_alloca_bounds_def, ce3_pointer_derived_vars] >>
  rpt strip_tac >> gvs[ce3_lookup_ptr, ce3_lookup_ptr2, ce3_w2n_0] >>
  simp[Once in_alloca_region_def] >- (qexistsl [`0`,`64`] >> EVAL_TAC) >>
  simp[Once in_alloca_region_def] >- (qexistsl [`0`,`64`] >> EVAL_TAC)
QED

(* ---- NOT ptrs_in_alloca_bounds for ce3_v ---- *)

Theorem ce3_not_ptrs_in_alloca_bounds_v:
  ¬ptrs_in_alloca_bounds ce3_fn ce3_roots ce3_v
Proof
  fs[ptrs_in_alloca_bounds_def, in_alloca_region_def, ce3_pointer_derived_vars] >>
  rpt strip_tac >>
  qexistsl [`"ptr2"`, `9999w`] >> simp[ce3_lookup_ptr2_v, ce3_w2n_9999] >>
  rpt strip_tac >>
  `ce3_v.vs_allocas = FEMPTY |+ (0,(0,64))` by EVAL_TAC >>
  full_simp_tac bool_ss [FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
  Cases_on `aid` >> gvs[] >> decide_tac
QED

(* ---- alloca_safe_access for ce3_v (vacuously true) ---- *)

Theorem ce3_alloca_safe_access_v:
  alloca_safe_access ce3_fn ce3_roots ce3_v
Proof
  simp[alloca_safe_access_def, ce3_pointer_derived_vars] >>
  rpt strip_tac >>
  gvs[ce3_fn_def, mk_raw_function_def, MEM] >>
  gvs[ce3_mem_write_ops_alloca, ce3_mem_read_ops_alloca] >>
  gvs[ce3_mem_write_ops_add, ce3_mem_read_ops_add] >>
  gvs[ce3_mem_write_ops_mstore, ce3_mem_read_ops_mstore,
      ce3_lookup_ptr2_v, ce3_w2n_9999, ce3_eval_operand_lit32_v,
      ce3_w2n_32, ce3_v_def, ce3_state_def,
      FLOOKUP_UPDATE, FLOOKUP_EMPTY] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> decide_tac
QED

(* ---- THE COUNTEREXAMPLE ---- *)

Theorem step_preserves_safety_counterexample:
  ∃fn roots inst bb s v.
    MEM bb fn.fn_blocks ∧ MEM inst bb.bb_instructions ∧
    step_inst_base inst s = OK v ∧
    ¬is_terminator inst.inst_opcode ∧
    ¬is_ext_call_op inst.inst_opcode ∧
    alloca_safe_access fn roots s ∧ ptrs_in_alloca_bounds fn roots s ∧
    ¬(alloca_safe_access fn roots v ∧ ptrs_in_alloca_bounds fn roots v)
Proof
  map_every qexists
    [`ce3_fn`, `ce3_roots`, `ce3_inst`, `ce3_bb`, `ce3_state`, `ce3_v`] >>
  simp[ce3_fn_def, mk_raw_function_def, ce3_inst_def, ce3_bb_def,
       ce3_step_inst_base,
       ce3_not_terminator, ce3_not_ext_call_op,
       ce3_alloca_safe_access, ce3_ptrs_in_alloca_bounds_s,
       ce3_not_ptrs_in_alloca_bounds_v, ce3_alloca_safe_access_v]
QED
