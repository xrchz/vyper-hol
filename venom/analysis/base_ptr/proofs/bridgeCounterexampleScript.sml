(*
 * Counterexample: bp_ptrs_bounded does NOT imply alloca_safe_access
 *
 * The bridge theorem bp_ptrs_bounded_imp_alloca_safe_access is FALSE:
 * there exist fn, bp, s, roots where all hypotheses hold but
 * alloca_safe_access fails.
 *
 * Root cause: alloca_safe_access checks runtime values
 * (eval_operand sz_op s = SOME sz_val ⇒ w2n w + w2n sz_val ≤ off + asz)
 * while bp_ptrs_bounded only checks compile-time structure
 * (bp_segment_from_ops gives ml_size = NONE for variable-sized ops,
 *  and memloc_within_alloca with ml_size = NONE is trivially T).
 *
 * The state s is universally quantified with no constraint on vs_vars,
 * so s can set the size variable to any value, breaking the access bound.
 *)

Theory bridgeCounterexample

Ancestors
  basePtrDefs pointerConfinedDefs allocaRemapDefs venomInst
  venomExecSemantics venomWf memLocDefs venomInstProofs
  pred_set finite_map list option While sum arithmetic words

(* Minimal function: ALLOCA producing "ptr" + MCOPY with variable size *)
Definition ce_fn_def:
  ce_fn : ir_function = mk_raw_function "ce_test" [
    <| bb_label := "entry";
       bb_instructions := [
         mk_inst 0 ALLOCA [Lit (n2w 64)] ["ptr"];
         mk_inst 1 MCOPY [Var "ptr"; Var "src"; Var "sz"] []
       ]
    |>
  ]
End

(* State: alloca at id=0, base=0, size=64; "ptr"=0w in alloca region;
   "sz"=9999w (WAY too large for a 64-byte alloca region) *)
Definition ce_state_def:
  ce_state = (init_venom_state "entry") with <|
    vs_vars := FEMPTY |+ ("ptr", n2w 0) |+ ("sz", n2w 9999) |+ ("src", n2w 0);
    vs_allocas := FEMPTY |+ (0, (0, 64));
    vs_memory := REPLICATE 64 (0w:word8);
    vs_alloca_next := 64
  |>
End

(* Base pointer analysis result: "ptr" → alloca 0 at offset 0 *)
Definition ce_bp_def:
  ce_bp : (string, ptr list) fmap =
    FEMPTY |+ ("ptr", [Ptr (Allocation 0) (SOME 0)])
End

Definition ce_roots_def:
  ce_roots = alloca_roots ce_fn
End

(* ---- Verified by EVAL ---- *)

Theorem ce_mem_write_ops_mcopy:
  mem_write_ops (mk_inst 1 MCOPY [Var "ptr"; Var "src"; Var "sz"] []) =
    SOME <|iao_ofst := Var "ptr"; iao_size := SOME (Var "sz");
            iao_max_size := SOME (Var "sz")|>
Proof
  EVAL_TAC
QED

Theorem ce_mem_read_ops_mcopy:
  mem_read_ops (mk_inst 1 MCOPY [Var "ptr"; Var "src"; Var "sz"] []) =
    SOME <|iao_ofst := Var "src"; iao_size := SOME (Var "sz");
            iao_max_size := SOME (Var "sz")|>
Proof
  EVAL_TAC
QED

Theorem ce_bp_segment_from_ops_mcopy_write:
  bp_segment_from_ops ce_bp
    <|iao_ofst := Var "ptr"; iao_size := SOME (Var "sz");
      iao_max_size := SOME (Var "sz")|> =
    <|ml_offset := SOME 0; ml_size := NONE;
      ml_alloca := SOME (Allocation 0); ml_volatile := F|>
Proof
  EVAL_TAC
QED

Theorem ce_bp_segment_from_ops_mcopy_read:
  bp_segment_from_ops ce_bp
    <|iao_ofst := Var "src"; iao_size := SOME (Var "sz");
      iao_max_size := SOME (Var "sz")|> =
    <|ml_offset := NONE; ml_size := NONE;
      ml_alloca := NONE; ml_volatile := F|>
Proof
  EVAL_TAC
QED

Theorem ce_memloc_within_alloca_write:
  memloc_within_alloca
    <|ml_offset := SOME 0; ml_size := NONE;
      ml_alloca := SOME (Allocation 0); ml_volatile := F|>
    ce_state ⇔ T
Proof
  EVAL_TAC
QED

Theorem ce_memloc_within_alloca_read:
  memloc_within_alloca
    <|ml_offset := NONE; ml_size := NONE;
      ml_alloca := NONE; ml_volatile := F|>
    ce_state ⇔ T
Proof
  EVAL_TAC
QED

Theorem ce_pointer_use_step:
  pointer_use_step ce_fn ["ptr"] = []
Proof
  EVAL_TAC
QED

(* ---- Derived facts ---- *)

Theorem ce_pointer_use_step_step:
  pointer_use_step_step ce_fn ["ptr"] = NONE
Proof
  EVAL_TAC
QED

Theorem ce_pointer_use_vars:
  pointer_use_vars ce_fn ["ptr"] = ["ptr"]
Proof
  simp[pointer_use_vars_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[ISL, OUTL, ce_pointer_use_step_step] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[ISL, OUTL, ce_pointer_use_step_step]
QED

Theorem ce_alloca_roots:
  alloca_roots ce_fn = {"ptr"}
Proof
  simp[alloca_roots_def, ce_fn_def, mk_raw_function_def, fn_insts_def,
       mk_inst_def, inst_output_def, EXTENSION] >>
  gen_tac >> gvs[fn_insts_blocks_def, MEM, AllCaseEqs()] >> eq_tac >> rpt strip_tac >> gvs[]
  >- (qexists `<|inst_id := 0; inst_opcode := ALLOCA; inst_operands := [Lit 64w]; inst_outputs := ["ptr"]|>` >> simp[])
  >> pop_assum mp_tac >> simp[]
QED

Theorem ce_pointer_derived_vars:
  pointer_derived_vars ce_fn ce_roots = {"ptr"}
Proof
  simp[pointer_derived_vars_def, ce_roots_def, ce_alloca_roots, SET_TO_LIST_SING, ce_pointer_use_vars]
QED

Theorem ce_bp_ptr_sound:
  bp_ptr_sound ce_bp ce_state
Proof
  simp[bp_ptr_sound_def] >> gen_tac >> Cases_on `v = "ptr"` >- (gvs[ce_bp_def, bp_get_ptrs_def, ptr_matches_var_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY, ce_state_def] >> EVAL_TAC) >> gvs[ce_bp_def, bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY]
QED

Theorem ce_bp_ptrs_bounded:
  bp_ptrs_bounded ce_bp ce_fn ce_state
Proof
  simp[bp_ptrs_bounded_def] >> rpt strip_tac >> gvs[ce_fn_def, mk_raw_function_def, AllCaseEqs()] >>
  gvs[mem_write_ops_def, mem_read_ops_def, mk_inst_def, AllCaseEqs(),
      ce_bp_segment_from_ops_mcopy_write, ce_bp_segment_from_ops_mcopy_read,
      IS_SOME_DEF, ce_memloc_within_alloca_write, ce_memloc_within_alloca_read]
QED

Theorem ce_pv_subset:
  pointer_derived_vars ce_fn ce_roots ⊆ {v | bp_get_ptrs ce_bp v ≠ []}
Proof
  simp[SUBSET_DEF, ce_pointer_derived_vars, bp_get_ptrs_def, ce_bp_def, FLOOKUP_UPDATE]
QED

Theorem ce_alloca_memory_bound:
  ∀aid off asz.
    FLOOKUP ce_state.vs_allocas aid = SOME (off, asz) ⇒
    off + asz ≤ LENGTH ce_state.vs_memory
Proof
  Cases_on `aid = 0n` >> strip_tac >> gvs[ce_state_def, FLOOKUP_UPDATE]
QED

(* ---- THE COUNTEREXAMPLE ---- *)

val dimindex_256 = fcpLib.DIMINDEX (Arbnum.fromInt 256)

Theorem ce_w2n_9999:
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

Theorem ce_w2n_0:
  w2n (0w:256 word) = 0
Proof
  simp[w2n_n2w, LESS_MOD]
QED

Theorem ce_not_alloca_safe_access:
  ¬alloca_safe_access ce_fn ce_roots ce_state
Proof
  strip_tac >> gvs[alloca_safe_access_def, ce_pointer_derived_vars] >>
  first_x_assum (qspec_then `<|bb_label := "entry"; bb_instructions := [mk_inst 0 ALLOCA [Lit 64w] ["ptr"]; mk_inst 1 MCOPY [Var "ptr"; Var "src"; Var "sz"] []]|>` assume_tac) >>
  first_x_assum (qspec_then `mk_inst 1 MCOPY [Var "ptr"; Var "src"; Var "sz"] []` assume_tac) >>
  first_x_assum (qspec_then `<|iao_ofst := Var "ptr"; iao_size := SOME (Var "sz"); iao_max_size := SOME (Var "sz")|>` assume_tac) >>
  first_x_assum (qspec_then `0w` assume_tac) >>
  first_x_assum (qspec_then `Var "sz"` assume_tac) >>
  first_x_assum (qspec_then `9999w` assume_tac) >>
  first_x_assum (qspec_then `0` assume_tac) >>
  first_x_assum (qspec_then `0` assume_tac) >>
  first_x_assum (qspec_then `64` assume_tac) >>
  first_x_assum mp_tac >>
  simp[ce_fn_def, mk_raw_function_def, ce_mem_write_ops_mcopy,
       ce_state_def, FLOOKUP_UPDATE,
       ce_w2n_9999, ce_w2n_0] >>
  EVAL_TAC >> decide_tac
QED

(* ---- FINAL COUNTEREXAMPLE ---- *)
Theorem bridge_counterexample:
  bp_ptr_sound ce_bp ce_state ∧
  bp_ptrs_bounded ce_bp ce_fn ce_state ∧
  pointer_derived_vars ce_fn ce_roots ⊆ {v | bp_get_ptrs ce_bp v ≠ []} ∧
  (∀aid off asz.
     FLOOKUP ce_state.vs_allocas aid = SOME (off, asz) ⇒
     off + asz ≤ LENGTH ce_state.vs_memory) ∧
  ¬alloca_safe_access ce_fn ce_roots ce_state
Proof
  metis_tac[ce_bp_ptr_sound, ce_bp_ptrs_bounded, ce_pv_subset,
            ce_alloca_memory_bound, ce_not_alloca_safe_access]
QED
