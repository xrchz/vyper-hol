(* Focused executable validation for TASK 049's BUMP simulation boundary. *)

Theory task049Validation
Ancestors
  planExec asmSem
Libs
  BasicProvers wordsLib

Definition task049_bump_inst_def:
  task049_bump_inst sz =
    mk_inst 49 BUMP [Lit 0w; Lit sz] ["ptr"; "next"]
End

Definition task049_bump_plan_state_def:
  task049_bump_plan_state sz =
    (init_plan_state 0) with ps_stack := [Lit 0w; Lit sz]
End

Theorem task049_bump_source_traces:
  step_inst_base (task049_bump_inst 0w) (init_venom_state "entry") =
    OK (update_var "next" 0w
          (update_var "ptr" 0w (init_venom_state "entry"))) /\
  step_inst_base (task049_bump_inst 32w) (init_venom_state "entry") =
    OK (update_var "next" 32w
          (update_var "ptr" 0w (init_venom_state "entry"))) /\
  step_inst_base (task049_bump_inst 1w) (init_venom_state "entry") =
    OK (update_var "next" 32w
          (update_var "ptr" 0w (init_venom_state "entry"))) /\
  step_inst_base (task049_bump_inst 33w) (init_venom_state "entry") =
    OK (update_var "next" 64w
          (update_var "ptr" 0w (init_venom_state "entry"))) /\
  step_inst_base (task049_bump_inst (-1w)) (init_venom_state "entry") =
    OK (update_var "next" 0w
          (update_var "ptr" 0w (init_venom_state "entry")))
Proof
  EVAL_TAC >> simp[]
QED

Theorem task049_bump_generated_trace:
  !sz.
    generate_emit_ops (task049_bump_inst sz) 0
      (task049_bump_plan_state sz) =
      ([SOPush (Lit 31w); SOEmit "ADD";
        SOPush (Lit 5w); SOEmit "SHR";
        SOPush (Lit 5w); SOEmit "SHL";
        SODup 2; SOEmit "ADD"], task049_bump_plan_state sz) /\
    execute_plan 0
      [SOPush (Lit 31w); SOEmit "ADD";
       SOPush (Lit 5w); SOEmit "SHR";
       SOPush (Lit 5w); SOEmit "SHL";
       SODup 2; SOEmit "ADD"] =
      [AsmPush [31w]; AsmOp "ADD";
       AsmPush [5w]; AsmOp "SHR";
       AsmPush [5w]; AsmOp "SHL";
       AsmOp "DUP2"; AsmOp "ADD"]
Proof
  gen_tac >> EVAL_TAC
QED

Theorem task049_bump_asm_traces:
  !s.
    asm_steps FEMPTY FEMPTY
      (execute_plan 0
        [SOPush (Lit 31w); SOEmit "ADD";
         SOPush (Lit 5w); SOEmit "SHR";
         SOPush (Lit 5w); SOEmit "SHL";
         SODup 2; SOEmit "ADD"]) 8
      (s with <| as_stack := [(0w:bytes32); 0w]; as_pc := 0 |>) =
      AsmOK (s with <| as_stack := [(0w:bytes32); 0w]; as_pc := 8 |>) /\
    asm_steps FEMPTY FEMPTY
      (execute_plan 0
        [SOPush (Lit 31w); SOEmit "ADD";
         SOPush (Lit 5w); SOEmit "SHR";
         SOPush (Lit 5w); SOEmit "SHL";
         SODup 2; SOEmit "ADD"]) 8
      (s with <| as_stack := [(32w:bytes32); 0w]; as_pc := 0 |>) =
      AsmOK (s with <| as_stack := [(32w:bytes32); 0w]; as_pc := 8 |>) /\
    asm_steps FEMPTY FEMPTY
      (execute_plan 0
        [SOPush (Lit 31w); SOEmit "ADD";
         SOPush (Lit 5w); SOEmit "SHR";
         SOPush (Lit 5w); SOEmit "SHL";
         SODup 2; SOEmit "ADD"]) 8
      (s with <| as_stack := [(1w:bytes32); 0w]; as_pc := 0 |>) =
      AsmOK (s with <| as_stack := [(32w:bytes32); 0w]; as_pc := 8 |>) /\
    asm_steps FEMPTY FEMPTY
      (execute_plan 0
        [SOPush (Lit 31w); SOEmit "ADD";
         SOPush (Lit 5w); SOEmit "SHR";
         SOPush (Lit 5w); SOEmit "SHL";
         SODup 2; SOEmit "ADD"]) 8
      (s with <| as_stack := [(33w:bytes32); 0w]; as_pc := 0 |>) =
      AsmOK (s with <| as_stack := [(64w:bytes32); 0w]; as_pc := 8 |>) /\
    asm_steps FEMPTY FEMPTY
      (execute_plan 0
        [SOPush (Lit 31w); SOEmit "ADD";
         SOPush (Lit 5w); SOEmit "SHR";
         SOPush (Lit 5w); SOEmit "SHL";
         SODup 2; SOEmit "ADD"]) 8
      (s with <| as_stack := [((-1w):bytes32); 0w]; as_pc := 0 |>) =
      AsmOK (s with <| as_stack := [(0w:bytes32); 0w]; as_pc := 8 |>)
Proof
  gen_tac >> EVAL_TAC >>
  simp[byteTheory.set_byte_def, byteTheory.word_slice_alt_zero,
       byteTheory.byte_index_def] >>
  wordsLib.WORD_DECIDE_TAC
QED

val _ = export_theory();
