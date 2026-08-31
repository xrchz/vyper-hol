(*
 * TASK_017 executable allocation-shape validation.
 *
 * Dynamic source extents must emit DALLOCA with an SSA size operand; fixed
 * compile-time capacities must continue to emit ALLOCA.  These probes inspect
 * only emitted instruction shape, avoiding brittle complete-state equalities.
 *)

Theory allocationShape
Ancestors
  builtinAbi builtinBytes builtinCreate builtinHashing builtinSystem
  stmtLowering

Definition task17_initial_state_def:
  task17_initial_state : compile_state =
    <| cs_next_var := 0;
       cs_next_label := 0;
       cs_next_id := 0;
       cs_current_bb := "entry";
       cs_current_insts := [];
       cs_blocks := [];
       cs_data_sections := [] |>
End

Definition task17_opcodes_def:
  task17_opcodes [] = [] /\
  task17_opcodes (i::is) = i.inst_opcode :: task17_opcodes is
End

Definition task17_block_insts_def:
  task17_block_insts [] = [] /\
  task17_block_insts (b::bs) =
    b.bb_instructions ++ task17_block_insts bs
End

Definition task17_state_insts_def:
  task17_state_insts st =
    st.cs_current_insts ++ task17_block_insts st.cs_blocks
End

Definition task17_emitted_insts_def:
  task17_emitted_insts (m:compile_state -> 'a # compile_state) =
    task17_state_insts (SND (m task17_initial_state))
End

Definition task17_emitted_opcodes_def:
  task17_emitted_opcodes m = task17_opcodes (task17_emitted_insts m)
End

Theorem task17_dynamic_boundary_shape:
  task17_emitted_insts (compile_alloc_dynamic (Var "%size")) =
    [mk_inst 0 DALLOCA [Var "%size"] ["%0"]]
Proof
  EVAL_TAC
QED

Theorem task17_msg_data_shape:
  task17_emitted_opcodes compile_msg_data_to_memory =
    [CALLDATASIZE; DALLOCA; CALLDATACOPY] /\
  MEM (mk_inst 1 DALLOCA [Var "%0"] ["%1"])
      (task17_emitted_insts compile_msg_data_to_memory) /\
  ~MEM MEMTOP (task17_emitted_opcodes compile_msg_data_to_memory)
Proof
  EVAL_TAC
QED

Theorem task17_create_copy_shape:
  MEM (mk_inst 3 DALLOCA [Var "%1"] ["%2"])
      (task17_emitted_insts
         (compile_create_copy (Var "%target") (Lit 0w) NONE T)) /\
  MEM DALLOCA
      (task17_emitted_opcodes
         (compile_create_copy (Var "%target") (Lit 0w) NONE T)) /\
  ~MEM MEMTOP
      (task17_emitted_opcodes
         (compile_create_copy (Var "%target") (Lit 0w) NONE T))
Proof
  EVAL_TAC
QED

Theorem task17_create_blueprint_no_args_shape:
  MEM (mk_inst 4 DALLOCA [Var "%1"] ["%3"])
      (task17_emitted_insts
         (compile_create_blueprint (Var "%target") (Lit 0w) NONE (Lit 3w)
            NONE T)) /\
  ~MEM MEMTOP
      (task17_emitted_opcodes
         (compile_create_blueprint (Var "%target") (Lit 0w) NONE (Lit 3w)
            NONE T))
Proof
  EVAL_TAC
QED

Theorem task17_create_blueprint_args_shape:
  MEM (mk_inst 5 DALLOCA [Var "%3"] ["%4"])
      (task17_emitted_insts
         (compile_create_blueprint (Var "%target") (Lit 0w) NONE (Lit 3w)
            (SOME (Var "%args", Var "%args_len")) T)) /\
  MEM (mk_inst 4 ADD [Var "%1"; Var "%args_len"] ["%3"])
      (task17_emitted_insts
         (compile_create_blueprint (Var "%target") (Lit 0w) NONE (Lit 3w)
            (SOME (Var "%args", Var "%args_len")) T)) /\
  ~MEM MEMTOP
      (task17_emitted_opcodes
         (compile_create_blueprint (Var "%target") (Lit 0w) NONE (Lit 3w)
            (SOME (Var "%args", Var "%args_len")) T))
Proof
  EVAL_TAC
QED

Theorem task17_abi_fixed_shape:
  MEM ALLOCA
      (task17_emitted_opcodes
         (lower_abi_encode F NONE (Var "%src") AbiPrimWord 64)) /\
  ~MEM DALLOCA
      (task17_emitted_opcodes
         (lower_abi_encode F NONE (Var "%src") AbiPrimWord 64))
Proof
  EVAL_TAC
QED

Theorem task17_bytes_fixed_shape:
  MEM ALLOCA
      (task17_emitted_opcodes
         (compile_slice_memory (Var "%src") (Lit 1w) (Lit 2w) 96)) /\
  ~MEM DALLOCA
      (task17_emitted_opcodes
         (compile_slice_memory (Var "%src") (Lit 1w) (Lit 2w) 96))
Proof
  EVAL_TAC
QED

Theorem task17_hashing_fixed_shape:
  MEM ALLOCA
      (task17_emitted_opcodes (compile_keccak256_word (Var "%word"))) /\
  ~MEM DALLOCA
      (task17_emitted_opcodes (compile_keccak256_word (Var "%word")))
Proof
  EVAL_TAC
QED

(* Closed unsupported-shape probe: an AnnAssign without the preallocated local
   binding required by vyper/codegen_venom/stmt.py:Stmt.lower_AnnAssign emits
   INVALID rather than silently preserving the input state. *)
Definition task17_missing_binding_cenv_def:
  task17_missing_binding_cenv : compile_env =
    (ARB:compile_env) with ce_vars := FEMPTY
End

Theorem task17_unsupported_annassign_fails:
  MEM INVALID
    (task17_emitted_opcodes
       (compile_stmt task17_missing_binding_cenv NoLoop (BaseT (UintT 256))
          (AnnAssign "x" (BaseT (UintT 256))
             (Literal (BaseT (UintT 256)) (IntL 1)))))
Proof
  EVAL_TAC
QED

val _ = export_theory();
