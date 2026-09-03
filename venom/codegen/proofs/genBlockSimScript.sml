(*
 * gen_block_simulation helpers
 *
 * Connects generate_block_plan to block_insts_sim:
 *   - FOLDL ↔ block_foldl equivalence
 *   - non_param_insts / get_params simplification
 *   - bb_well_formed derivation from codegen_ready_fn
 *   - Per-instruction Halt/Abort/OK simulation
 *   - clean_stack_plan simulation (cheated)
 *)


Theory genBlockSim
Ancestors
  blockSimHelpers stackOpSim stackOpAsmSim planWf prefixExec prefixSim mixedPrefixSim planSim asmSem planExec codegenRel asmIR stackPlanGen stackPlanTypes stackModel stackPlanOps venomExecSemantics venomInstProofs1 venomState venomInst venomWf venomEffects list rich_list arithmetic indexedLists instSimHelpers opcodeClass strongPrefixSim reorderSim emitInputSim planAlign doSwapSim emitSim asmOpSim spillSim allocMono cleanOpsSim planSpillBounds
Libs
  BasicProvers

(* Eliminate LET-pair from theorems like reorder_plan_wf_len *)
val delet = CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV) o
            REWRITE_RULE [LET_THM];

(* ===== FOLDL ↔ block_foldl ===== *)

(* block_foldl propagates NONE *)
Theorem block_foldl_none[local,simp]:
  !pairs gen_plan. block_foldl gen_plan NONE pairs = NONE
Proof
  Induct >> simp[block_foldl_def] >>
  Cases >> simp[block_foldl_def]
QED

(* The FOLDL in generate_block_plan is exactly block_foldl *)
Theorem foldl_eq_block_foldl:
  !pairs gen_plan acc.
    FOLDL (\acc' (i,inst). case acc' of NONE => NONE | SOME (ops,ps) =>
      case gen_plan i inst ps of NONE => NONE | SOME (step_ops, ps') =>
        SOME (ops ++ step_ops, ps'))
    acc pairs = block_foldl gen_plan acc pairs
Proof
  Induct >> simp[block_foldl_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[block_foldl_def] >>
  Cases_on `acc` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `gen_plan h0 h1 x1` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

(* ===== non_param_insts / get_params simplification ===== *)

(* When all instructions are non-parameters, non_param_insts is identity. *)
Theorem non_param_insts_all_neq:
  !bb. EVERY (\inst. ~is_param_opcode inst.inst_opcode) bb.bb_instructions ==>
       non_param_insts bb = bb.bb_instructions
Proof
  rpt strip_tac >> simp[non_param_insts_def] >>
  metis_tac[FILTER_EQ_ID]
QED

(* When the head instruction is not any parameter opcode, get_params is empty. *)
Theorem get_params_nil_hd:
  !inst rest. ~is_param_opcode inst.inst_opcode ==>
              get_params (inst :: rest) = []
Proof
  rpt strip_tac >> simp[get_params_def]
QED

(* When all instructions are non-parameters, get_params returns empty. *)
Theorem get_params_nil:
  !insts. insts <> [] /\
          EVERY (\inst. ~is_param_opcode inst.inst_opcode) insts ==>
          get_params insts = []
Proof
  Cases >> simp[] >> rpt strip_tac >>
  fs[] >> simp[get_params_def]
QED

(* ===== bb_well_formed from codegen_ready_fn ===== *)

Theorem bb_well_formed_from_ready:
  !fn bb. codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
          bb_well_formed bb
Proof
  rpt strip_tac >>
  fs[codegen_ready_fn_def, wf_function_def] >>
  res_tac
QED

(* ===== Plan decomposition for terminal opcodes ===== *)

(* When venom_to_evm_name maps to SOME name and outputs = [],
   the regular plan ends with [SOEmit name].
   This is the key structural lemma for terminal simulation. *)
(* Helper: generate_emit_ops with SOME name is trivial *)
Theorem generate_emit_ops_some_name[local]:
  !inst ltc ps name.
    venom_to_evm_name inst.inst_opcode = SOME name ==>
    generate_emit_ops inst ltc ps = ([SOEmit name], ps)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[venom_to_evm_name_def, generate_emit_ops_def]
QED

Theorem regular_plan_emit_decompose:
  !liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps name.
    venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_outputs = [] ==>
    ?prefix_ops ps_out.
      generate_regular_inst_plan liveness dfg cfg fn inst
        next_liveness is_halting next_is_term bb_label ps =
      (prefix_ops ++ [SOEmit name], ps_out)
Proof
  rpt strip_tac >>
  simp[generate_regular_inst_plan_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `inst.inst_opcode = JMP` >- fs[venom_to_evm_name_def] >>
  simp[] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  (* At this point goal has:
     (λ(emit_ops,ps7). (input_ops ++ reorder_ops ++ emit_ops, ...))
       (generate_emit_ops inst log_topic_count ps_modified)
     Rewrite generate_emit_ops using the SOME name assumption *)
  `!ltc ps_arg. generate_emit_ops inst ltc ps_arg =
                ([SOEmit name], ps_arg)` by simp[generate_emit_ops_some_name] >>
  simp[] >>
  qexists_tac `input_ops ++ reorder_ops` >> simp[]
QED

(* General decomposition: ops = prefix ++ [SOEmit name] ++ postfix.
   Works for ALL instructions with venom_to_evm_name = SOME name,
   regardless of inst_outputs.
   Subsumes regular_plan_emit_decompose (where postfix = []). *)
Theorem regular_plan_full_decompose:
  !liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps name.
    venom_to_evm_name inst.inst_opcode = SOME name ==>
    ?prefix_ops postfix_ops ps_out.
      generate_regular_inst_plan liveness dfg cfg fn inst
        next_liveness is_halting next_is_term bb_label ps =
      (prefix_ops ++ [SOEmit name] ++ postfix_ops, ps_out) /\
      EVERY is_prefix_op postfix_ops
Proof
  rpt strip_tac >>
  simp[generate_regular_inst_plan_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `inst.inst_opcode = JMP` >- fs[venom_to_evm_name_def] >>
  simp[] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `!ltc ps_arg. generate_emit_ops inst ltc ps_arg =
                ([SOEmit name], ps_arg)` by simp[generate_emit_ops_some_name] >>
  simp[] >>
  Cases_on `inst.inst_outputs = []`
  >- (
    simp[] >>
    Q.EXISTS_TAC `input_ops ++ reorder_ops` >>
    Q.EXISTS_TAC `[]` >> simp[]
  )
  >>
  simp[] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  Q.EXISTS_TAC `input_ops ++ reorder_ops` >>
  Q.EXISTS_TAC `pop_ops ++ opt_ops` >>
  simp[] >>
  suspend "prefix_op_goal"
QED

Resume regular_plan_full_decompose[prefix_op_goal]:
  conj_tac
  >- suspend "pop_part"
  >> suspend "opt_part"
QED

Resume regular_plan_full_decompose[pop_part]:
  pop_assum kall_tac >>
  pop_assum mp_tac >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  imp_res_tac popmany_plan_prefix_op
QED

Resume regular_plan_full_decompose[opt_part]:
  pop_assum mp_tac >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  imp_res_tac optimistic_swap_plan_prefix_op
QED

Finalise regular_plan_full_decompose

(* Plan decomposition for non-commutative, output-free, non-JMP instructions.
   Covers ASSERT, ASSERT_UNREACHABLE, and other non-commutative opcodes
   where venom_to_evm_name may be NONE. *)
Theorem regular_plan_noncomm_prefix_split:
  !liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps ops ps_out lo.
    generate_regular_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = (ops, ps_out) /\
    inst.inst_outputs = [] /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> INVOKE /\
    ~is_commutative inst.inst_opcode /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) ==>
    ?prefix_ops emit_ops.
      ops = prefix_ops ++ emit_ops /\
      prefix_wf lo (LENGTH ps.ps_stack) prefix_ops /\
      EVERY is_prefix_op prefix_ops
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[] >>
  Q.EXISTS_TAC `input_ops ++ reorder_ops` >>
  Q.EXISTS_TAC `emit_ops` >> simp[] >>
  (* Get prefix_wf for input_ops from emit_input_plan_wf_len *)
  qspecl_then [`compute_operands inst`, `inst.inst_opcode`,
               `next_liveness`, `ps`, `lo`]
    mp_tac emit_input_plan_wf_len >>
  (impl_tac >- gvs[]) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* Get prefix_wf for reorder_ops from reorder_plan_wf_len *)
  qspecl_then [`dfg`, `compute_operands inst`, `ps1`, `lo`]
    mp_tac (REWRITE_RULE [LET_THM] reorder_plan_wf_len) >>
  (impl_tac >- gvs[]) >>
  disch_then (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR]) >> gvs[] >>
  (* Combine: prefix_wf(input_ops) + prefix_wf(reorder_ops) => prefix_wf(input_ops ++ reorder_ops) *)
  conj_tac
  >- (
    qspecl_then [`input_ops`, `reorder_ops`, `lo`,
                 `LENGTH ps.ps_stack`]
      mp_tac prefix_wf_append >>
    (impl_tac >- gvs[]) >> simp[]
  )
  >>
  imp_res_tac prefix_wf_every_prefix_op >> gvs[]
QED

(* ===== Per-instruction step_inst result helpers ===== *)

(* NOP always returns OK *)
Theorem step_inst_nop_ok[local]:
  !fuel ctx inst vs.
    inst.inst_opcode = NOP ==> step_inst fuel ctx inst vs = OK vs
Proof
  rpt strip_tac >>
  `inst = inst with inst_opcode := NOP`
    by simp[instruction_component_equality] >>
  pop_assum SUBST1_TAC >> EVAL_TAC
QED

(* STOP always returns Halt *)
Theorem step_inst_stop_halt[local]:
  !fuel ctx inst vs.
    inst.inst_opcode = STOP ==>
    step_inst fuel ctx inst vs = Halt (halt_state vs)
Proof
  rpt strip_tac >>
  `inst = inst with inst_opcode := STOP`
    by simp[instruction_component_equality] >>
  pop_assum SUBST1_TAC >> EVAL_TAC
QED

(* ===== Prefix execution helper ===== *)

(* Shared helper: when generate_regular_inst_plan produces prefix ++ [SOEmit name],
   executing the prefix from a venom_asm_rel state yields an intermediate
   AsmOK state with the terminal op ready and observable fields preserved.
   Used by all terminal simulation cases (STOP, RETURN, SELFDESTRUCT, REVERT). *)
Theorem prefix_exec_terminal:
  !prefix name lo o2pc prog st ps vs.
    prefix_wf lo (LENGTH ps.ps_stack) prefix /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp prefix ++ [AsmOp name]) ==>
    ?st'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp prefix)) st = AsmOK st' /\
      asm_block_at prog st'.as_pc [AsmOp name] /\
      venom_asm_terminal_rel vs st'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `prefix`
  >- (
    (* Empty prefix: 0 steps, st' = st *)
    qexists_tac `st` >>
    gvs[execute_plan_def, Once asm_steps_def] >>
    imp_res_tac venom_asm_rel_implies_terminal
  ) >>
  (* Non-empty prefix *)
  rename1 `h::t` >>
  SUBGOAL_THEN ``LENGTH (st:asm_state).as_stack = LENGTH ps.ps_stack``
    STRIP_ASSUME_TAC
  >- (fs[venom_asm_rel_def] >> imp_res_tac plan_stack_rel_length >> fs[]) >>
  (* Split asm_block_at — keep execute_plan initial_fmp form *)
  qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp _ ++ _)` mp_tac >>
  REWRITE_TAC[asm_block_at_append, execute_plan_def] >>
  REWRITE_TAC[GSYM execute_plan_def] >> strip_tac >>
  (* Derive EVERY AFTER asm_block_at split to avoid decomposition *)
  drule_then assume_tac prefix_wf_every_prefix_op >>
  (* Apply prefix_sim — specialize o2pc before extracting st' *)
  drule_all (REWRITE_RULE [GSYM execute_plan_def] prefix_sim) >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexists_tac `st'` >>
  conj_tac >- ASM_REWRITE_TAC[] >>
  conj_tac >- (ASM_REWRITE_TAC[]) >>
  fs[venom_asm_terminal_rel_def, venom_asm_rel_def]
QED

(* ===== Prefix decomposition (reusable core) ===== *)

(* gen_inst_prefix_decompose: For a non-INVOKE terminal opcode with
   venom_to_evm_name = SOME name and inst_outputs = [],
   extracts the prefix from generate_inst_plan, establishes prefix_wf,
   and converts execute_plan initial_fmp to prefix ++ [AsmOp name].

   This is THE reusable decomposition for all terminal simulation cases.
   Callers choose their own prefix execution lemma:
   - prefix_exec_terminal (weak: venom_asm_terminal_rel)
   - mixed_prefix_venom_asm_rel (strong: full venom_asm_rel) *)
Theorem gen_inst_prefix_decompose:
  !liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps ops ps' name label_offsets.
    ~is_param_opcode inst.inst_opcode /\
    ~is_pre_codegen_opcode inst.inst_opcode /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> OFFSET /\
    inst.inst_opcode <> NOP /\
    inst.inst_opcode <> INVOKE /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_outputs = [] /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP label_offsets l)) /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') ==>
    ?prefix_ops.
      ops = prefix_ops ++ [SOEmit name] /\
      prefix_wf label_offsets (LENGTH ps.ps_stack) prefix_ops /\
      execute_plan initial_fmp ops = execute_plan initial_fmp prefix_ops ++ [AsmOp name]
Proof
  rpt gen_tac >> strip_tac >>
  (* generate_inst_plan -> generate_regular_inst_plan *)
  `generate_regular_inst_plan liveness dfg cfg fn inst
     next_liveness is_halting next_is_term bb_label ps = (ops, ps')` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def]) >>
  (* regular_plan_emit_decompose *)
  `?prefix_ops ps_out.
     generate_regular_inst_plan liveness dfg cfg fn inst
       next_liveness is_halting next_is_term bb_label ps =
       (prefix_ops ++ [SOEmit name], ps_out)` by
    metis_tac[regular_plan_emit_decompose] >>
  `ops = prefix_ops ++ [SOEmit name] /\ ps' = ps_out` by
    (qpat_x_assum `_ = (ops, ps')` mp_tac >>
     qpat_x_assum `_ = (prefix_ops ++ _, _)` (fn th => REWRITE_TAC[th]) >>
     strip_tac >> gvs[]) >>
  gvs[] >>
  conj_tac
  >- (qspecl_then [`liveness`, `dfg`, `cfg`, `fn`, `inst`,
       `next_liveness`, `is_halting`, `next_is_term`, `bb_label`,
       `ps`, `prefix_ops`, `[]`, `name`, `ps'`, `label_offsets`]
       mp_tac regular_plan_prefix_wf_gen >>
     ASM_REWRITE_TAC[APPEND_NIL] >> metis_tac[])
  >- simp[execute_plan_append, execute_plan_def, exec_stack_op_def]
QED

(* ===== Unified terminal setup ===== *)

(* gen_inst_terminal_setup: Uses gen_inst_prefix_decompose + prefix_exec_terminal
   to produce an intermediate AsmOK state with the terminal op ready.
   Provides venom_asm_terminal_rel (sufficient for STOP/INVALID). *)
Theorem gen_inst_terminal_setup:
  !fuel ctx label_offsets offset_to_pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps' name.
    ~is_param_opcode inst.inst_opcode /\
    ~is_pre_codegen_opcode inst.inst_opcode /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> OFFSET /\
    inst.inst_opcode <> NOP /\
    inst.inst_opcode <> INVOKE /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_outputs = [] /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP label_offsets l)) /\
    venom_asm_rel label_offsets ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    ?st'.
      asm_steps label_offsets offset_to_pc prog
        (LENGTH (execute_plan initial_fmp ops) - 1) as = AsmOK st' /\
      asm_block_at prog st'.as_pc [AsmOp name] /\
      venom_asm_terminal_rel vs st'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all gen_inst_prefix_decompose >>
  disch_then (qspec_then `initial_fmp` strip_assume_tac) >> gvs[] >>
  qspecl_then [`prefix_ops`, `name`, `label_offsets`, `offset_to_pc`,
    `prog`, `as`, `ps`, `vs`] mp_tac prefix_exec_terminal >>
  (impl_tac >- (fs[asm_block_at_append] >> ASM_REWRITE_TAC[])) >>
  strip_tac >>
  qexists_tac `st'` >>
  `LENGTH (execute_plan initial_fmp prefix_ops ++ [AsmOp name]) - 1 =
   LENGTH (execute_plan initial_fmp prefix_ops)` by simp[] >>
  gvs[]
QED

(* gen_inst_terminal_setup_strong: Like gen_inst_terminal_setup but
   provides full venom_asm_rel (not just terminal_rel).
   Needed by RETURN/REVERT/SELFDESTRUCT which access stack values.
   Extra precondition: prefix_spill_wf initial_fmp (on FRONT ops). *)
Theorem gen_inst_terminal_setup_strong:
  !fuel ctx label_offsets offset_to_pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps' name.
    ~is_param_opcode inst.inst_opcode /\
    ~is_pre_codegen_opcode inst.inst_opcode /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> OFFSET /\
    inst.inst_opcode <> NOP /\
    inst.inst_opcode <> INVOKE /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_outputs = [] /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP label_offsets l)) /\
    prefix_spill_wf initial_fmp label_offsets (FRONT ops) ps /\
    venom_asm_rel label_offsets ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    ?st' prefix_ops.
      asm_steps label_offsets offset_to_pc prog
        (LENGTH (execute_plan initial_fmp ops) - 1) as = AsmOK st' /\
      asm_block_at prog st'.as_pc [AsmOp name] /\
      ops = prefix_ops ++ [SOEmit name] /\
      prefix_wf label_offsets (LENGTH ps.ps_stack) prefix_ops /\
      venom_asm_rel label_offsets
        (apply_prefix_ops initial_fmp label_offsets prefix_ops ps) vs st'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all gen_inst_prefix_decompose >>
  disch_then (qspec_then `initial_fmp` strip_assume_tac) >> gvs[] >>
  (* Derive prefix_spill_wf initial_fmp for prefix_ops from FRONT ops hypothesis *)
  qpat_x_assum `prefix_spill_wf initial_fmp _ (FRONT _) _` mp_tac >>
  simp[FRONT_APPEND_NOT_NIL] >> strip_tac >>
  (* Use prefix_exec_terminal FIRST (needs combined asm_block_at) *)
  mp_tac prefix_exec_terminal >>
  disch_then (qspecl_then [`prefix_ops`, `name`, `label_offsets`,
    `offset_to_pc`, `prog`, `as`, `ps`, `vs`] mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  (* Derive venom_asm_rel via mixed_prefix *)
  drule_then assume_tac prefix_wf_every_prefix_op >>
  (* Split asm_block_at for prefix alone *)
  qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp _ ++ _)` mp_tac >>
  REWRITE_TAC[asm_block_at_append, execute_plan_def] >>
  REWRITE_TAC[GSYM execute_plan_def] >> strip_tac >>
  mp_tac mixed_prefix_venom_asm_rel >>
  disch_then (qspecl_then [`prefix_ops`, `initial_fmp`, `label_offsets`, `offset_to_pc`,
    `prog`, `ps`, `vs`, `as`] mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  (* Both give asm_steps ... = AsmOK _, so states equal *)
  gvs[]
QED

(* prefix_spill_wf initial_fmp for a prefix of a spill-safe sequence *)
Theorem prefix_spill_wf_prefix[local]:
  !xs ys lo ps. prefix_spill_wf initial_fmp lo (xs ++ ys) ps ==> prefix_spill_wf initial_fmp lo xs ps
Proof
  Induct >> simp[prefix_spill_wf_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

(* prefix_sim: Given prefix_ops that are well-formed prefix operations,
   execute them preserving venom_asm_rel and splitting asm_block_at.
   Caller provides prefix_ops/emit_ops decomposition and emit_ops <> []. *)
Theorem prefix_sim:
  !label_offsets offset_to_pc prog ps vs as prefix_ops emit_ops.
    prefix_wf label_offsets (LENGTH ps.ps_stack) prefix_ops /\
    EVERY is_prefix_op prefix_ops /\
    emit_ops <> [] /\
    prefix_spill_wf initial_fmp label_offsets (FRONT (prefix_ops ++ emit_ops)) ps /\
    venom_asm_rel label_offsets ps vs as /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp (prefix_ops ++ emit_ops)) ==>
    ?st_mid.
      asm_steps label_offsets offset_to_pc prog
        (LENGTH (execute_plan initial_fmp prefix_ops)) as = AsmOK st_mid /\
      venom_asm_rel label_offsets
        (apply_prefix_ops initial_fmp label_offsets prefix_ops ps) vs st_mid /\
      asm_block_at prog st_mid.as_pc (execute_plan initial_fmp emit_ops) /\
      st_mid.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp prefix_ops) /\
      LENGTH st_mid.as_stack =
        prefix_end_len label_offsets (LENGTH ps.ps_stack) prefix_ops
Proof
  rpt gen_tac >> strip_tac >>
  (* Get prefix_spill_wf initial_fmp for prefix_ops from FRONT(prefix_ops ++ emit_ops) *)
  `prefix_spill_wf initial_fmp label_offsets prefix_ops ps` by (
    qpat_x_assum `prefix_spill_wf initial_fmp _ (FRONT _) _` mp_tac >>
    simp[FRONT_APPEND_NOT_NIL] >>
    metis_tac[prefix_spill_wf_prefix]
  ) >>
  (* Split asm_block_at *)
  qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp (_ ++ _))` mp_tac >>
  REWRITE_TAC[execute_plan_append, asm_block_at_append] >> strip_tac >>
  (* Run prefix via mixed_prefix_venom_asm_rel *)
  mp_tac mixed_prefix_venom_asm_rel >>
  disch_then (qspecl_then [`prefix_ops`, `initial_fmp`, `label_offsets`, `offset_to_pc`,
    `prog`, `ps`, `vs`, `as`] mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >> Q.EXISTS_TAC `st'` >> gvs[] >>
  (* LENGTH via prefixExecTheory.prefix_sim *)
  `LENGTH as.as_stack = LENGTH ps.ps_stack` by (
    qpat_x_assum `venom_asm_rel _ ps _ as` mp_tac >>
    rewrite_tac[venom_asm_rel_def] >> strip_tac >>
    imp_res_tac plan_stack_rel_length >> simp[]) >>
  qspecl_then [`prefix_ops`, `initial_fmp`, `label_offsets`, `offset_to_pc`, `prog`,
    `as`, `LENGTH ps.ps_stack`] mp_tac prefixExecTheory.prefix_sim >>
  simp[GSYM execute_plan_def]
QED

(* ===== Memory read_byte helpers ===== *)

(* read_byte of zero-padded memory = read_byte of original *)
Theorem read_byte_pad_zero[local]:
  !i (mem : byte list) k.
    read_byte i (mem ++ REPLICATE k (0w:byte)) = read_byte i mem
Proof
  rpt gen_tac >> simp[read_byte_def] >>
  Cases_on `i < LENGTH mem`
  >- simp[EL_APPEND1]
  >- (
    `~(i < LENGTH mem)` by decide_tac >> simp[] >>
    Cases_on `i < LENGTH mem + k`
    >- (simp[] >>
        `i - LENGTH mem < k` by decide_tac >>
        simp[EL_APPEND2, EL_REPLICATE])
    >- (`~(i < LENGTH mem + k)` by decide_tac >> simp[])
  )
QED

(* read_byte of asm_expand_memory = read_byte of original *)
Theorem read_byte_expand[local]:
  !i needed (mem : byte list).
    read_byte i (asm_expand_memory needed mem) = read_byte i mem
Proof
  rpt gen_tac >> simp[asm_expand_memory_def, LET_THM] >>
  Cases_on `32 * ((needed + 31) DIV 32) <= LENGTH mem` >>
  simp[read_byte_pad_zero]
QED

(* Venom RETURN returndata = GENLIST of read_byte *)
Theorem venom_returndata_read_byte[local]:
  !off sz (mem : byte list).
    TAKE sz (DROP off mem ++ REPLICATE sz (0w:byte)) =
    GENLIST (\i. read_byte (off + i) mem) sz
Proof
  rpt gen_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ, LENGTH_GENLIST,
       LENGTH_APPEND, LENGTH_DROP] >>
  rpt strip_tac >>
  `x < MIN sz (LENGTH (DROP off mem) + sz)` by simp[MIN_DEF] >>
  simp[EL_TAKE, EL_GENLIST] >>
  simp[read_byte_def] >>
  Cases_on `off + x < LENGTH mem`
  >- (
    `x < LENGTH (DROP off mem)` by (fs[LENGTH_DROP] >> decide_tac) >>
    simp[EL_APPEND1, EL_DROP]
  )
  >- (
    simp[] >>
    `LENGTH (DROP off mem) <= x` by (fs[LENGTH_DROP] >> decide_tac) >>
    `x - LENGTH (DROP off mem) < sz` by decide_tac >>
    simp[EL_APPEND2, EL_REPLICATE]
  )
QED

(* Asm RETURN returndata = GENLIST of read_byte *)
(* Helper: element of asm_expand_memory = read_byte *)
Theorem el_asm_expand[local]:
  !i needed (mem : byte list).
    i < MAX needed (LENGTH mem) ==>
    EL i (asm_expand_memory needed mem) = read_byte i mem
Proof
  rpt strip_tac >> simp[asm_expand_memory_def, LET_THM, read_byte_def] >>
  qabbrev_tac `rounded = 32 * ((needed + 31) DIV 32)` >>
  `needed <= rounded` by
    (simp[Abbr `rounded`] >>
     `(needed + 31) = (needed + 31) DIV 32 * 32 + (needed + 31) MOD 32 /\
      (needed + 31) MOD 32 < 32` by
       (mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >> simp[]) >>
     decide_tac) >>
  Cases_on `rounded <= LENGTH mem`
  >- (simp[] >> Cases_on `i < LENGTH mem` >> simp[] >>
      fs[MAX_DEF] >> decide_tac)
  >- (simp[] >> Cases_on `i < LENGTH mem`
      >- simp[EL_APPEND1]
      >- (`i - LENGTH mem < rounded - LENGTH mem` by
            (fs[MAX_DEF] >> decide_tac) >>
          simp[EL_APPEND2, EL_REPLICATE]))
QED

Theorem asm_returndata_read_byte[local]:
  !off sz (mem : byte list).
    TAKE sz (DROP off (asm_expand_memory (off + sz) mem)) =
    GENLIST (\i. read_byte (off + i) mem) sz
Proof
  rpt gen_tac >>
  mp_tac (SPEC ``mem:byte list``
           (SPEC ``off + sz:num`` spillSimTheory.asm_expand_memory_length)) >>
  strip_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ, LENGTH_GENLIST, LENGTH_DROP,
       MIN_DEF] >>
  rpt strip_tac >> simp[EL_TAKE, EL_DROP, EL_GENLIST, el_asm_expand, MAX_DEF]
QED

(* Returndata equivalence: when read_byte agrees on [off, off+sz),
   both RETURN formulations produce the same returndata *)
Theorem returndata_agree[local]:
  !off sz (vmem : byte list) (amem : byte list).
    (!i. i < sz ==> read_byte (off + i) vmem = read_byte (off + i) amem) ==>
    TAKE sz (DROP off vmem ++ REPLICATE sz (0w:byte)) =
    TAKE sz (DROP off (asm_expand_memory (off + sz) amem))
Proof
  rpt strip_tac >>
  REWRITE_TAC[venom_returndata_read_byte, asm_returndata_read_byte] >>
  irule LIST_EQ >> simp[LENGTH_GENLIST] >>
  rpt strip_tac >> simp[EL_GENLIST]
QED

(* ===== Terminal step with returndata clearing ===== *)

(* STOP: AsmHalt, both sides clear returndata *)
Theorem terminal_stop_step:
  !lo o2pc prog st vs.
    asm_block_at prog st.as_pc [AsmOp "STOP"] /\
    venom_asm_terminal_rel vs st /\
    vs.vs_returndata = [] ==>
    ?st'.
      asm_steps lo o2pc prog 1 st = AsmHalt st' /\
      venom_asm_terminal_rel (halt_state vs) st'
Proof
  rpt strip_tac >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def] >>
  fs[asm_block_at_def] >>
  qexists_tac `st with as_returndata := []` >>
  simp[asm_step_stop] >>
  fs[venom_asm_terminal_rel_def, halt_state_def, set_returndata_def]
QED

(* INVALID: AsmFault, both sides clear returndata *)
Theorem terminal_invalid_step:
  !lo o2pc prog st vs.
    asm_block_at prog st.as_pc [AsmOp "INVALID"] /\
    venom_asm_terminal_rel vs st ==>
    ?st'.
      asm_steps lo o2pc prog 1 st = AsmFault st' /\
      venom_asm_terminal_rel
        (vs with <| vs_returndata := []; vs_halted := T |>) st'
Proof
  rpt strip_tac >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def] >>
  fs[asm_block_at_def] >>
  qexists_tac `st with as_returndata := []` >>
  simp[asm_step_invalid] >>
  fs[venom_asm_terminal_rel_def]
QED

(* ===== step_inst decomposition for terminal opcodes ===== *)

(* What step_inst RETURN produces *)
Theorem step_inst_return_halt[local]:
  !fuel ctx inst vs vs'.
    inst.inst_opcode = RETURN /\
    step_inst fuel ctx inst vs = Halt vs' ==>
    ?off_op sz_op off_val sz_val.
      inst.inst_operands = [off_op; sz_op] /\
      eval_operand off_op vs = SOME off_val /\
      eval_operand sz_op vs = SOME sz_val /\
      vs' = halt_state (set_returndata
        (TAKE (w2n sz_val) (DROP (w2n off_val) vs.vs_memory ++
         REPLICATE (w2n sz_val) 0w)) vs)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `is_terminator RETURN` >> simp[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = RETURN`
    (fn th => PURE_REWRITE_TAC[th]) >>
  every_case_tac >> gvs[halt_state_def, set_returndata_def]
QED

(* What step_inst REVERT produces *)
Theorem step_inst_revert_abort[local]:
  !fuel ctx inst vs a vs'.
    inst.inst_opcode = REVERT /\
    step_inst fuel ctx inst vs = Abort a vs' ==>
    ?off_op sz_op off_val sz_val.
      inst.inst_operands = [off_op; sz_op] /\
      eval_operand off_op vs = SOME off_val /\
      eval_operand sz_op vs = SOME sz_val /\
      a = Revert_abort /\
      vs' = revert_state (set_returndata
        (TAKE (w2n sz_val) (DROP (w2n off_val) vs.vs_memory ++
         REPLICATE (w2n sz_val) 0w)) vs)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = Abort _ _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `is_terminator REVERT` >> simp[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = REVERT`
    (fn th => PURE_REWRITE_TAC[th]) >>
  every_case_tac >> gvs[revert_state_def, set_returndata_def]
QED

(* What step_inst SELFDESTRUCT produces *)
Theorem step_inst_selfdestruct_halt[local]:
  !fuel ctx inst vs vs'.
    inst.inst_opcode = SELFDESTRUCT /\
    step_inst fuel ctx inst vs = Halt vs' ==>
    ?addr_op addr_val.
      inst.inst_operands = [addr_op] /\
      eval_operand addr_op vs = SOME addr_val /\
      vs' = halt_state (vs with vs_accounts :=
        (\a. if a = vs.vs_call_ctx.cc_address then
               lookup_account vs.vs_call_ctx.cc_address vs.vs_accounts
                 with balance := 0
             else if a = (w2w addr_val : address) then
               lookup_account (w2w addr_val) vs.vs_accounts with
                 balance :=
                   (lookup_account vs.vs_call_ctx.cc_address
                      vs.vs_accounts).balance +
                   (lookup_account (w2w addr_val) vs.vs_accounts).balance
             else vs.vs_accounts a))
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `is_terminator SELFDESTRUCT` >> simp[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = SELFDESTRUCT`
    (fn th => PURE_REWRITE_TAC[th]) >>
  every_case_tac >> gvs[halt_state_def, LET_THM]
QED

(* What step_inst RETURNDATACOPY abort produces *)
Theorem step_inst_returndatacopy_abort[local]:
  !fuel ctx inst vs a vs'.
    inst.inst_opcode = RETURNDATACOPY /\
    step_inst fuel ctx inst vs = Abort a vs' ==>
    ?dest_op src_op sz_op dest_val src_val sz_val.
      inst.inst_operands = [dest_op; src_op; sz_op] /\
      eval_operand dest_op vs = SOME dest_val /\
      eval_operand src_op vs = SOME src_val /\
      eval_operand sz_op vs = SOME sz_val /\
      w2n src_val + w2n sz_val > LENGTH vs.vs_returndata /\
      a = ExHalt_abort /\
      vs' = halt_state (set_returndata [] vs)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = Abort _ _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `is_terminator RETURNDATACOPY` >> simp[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = RETURNDATACOPY`
    (fn th => PURE_REWRITE_TAC[th]) >>
  every_case_tac >> gvs[halt_state_def, set_returndata_def] >>
  IF_CASES_TAC >> gvs[halt_state_def, set_returndata_def]
QED

(* What step_inst ASSERT_UNREACHABLE abort produces *)
Theorem step_inst_assert_unreachable_abort[local]:
  !fuel ctx inst vs a vs'.
    inst.inst_opcode = ASSERT_UNREACHABLE /\
    step_inst fuel ctx inst vs = Abort a vs' ==>
    ?cond_op.
      inst.inst_operands = [cond_op] /\
      eval_operand cond_op vs = SOME 0w /\
      a = ExHalt_abort /\
      vs' = halt_state (set_returndata [] vs)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = Abort _ _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `is_terminator ASSERT_UNREACHABLE` >> simp[] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = ASSERT_UNREACHABLE`
    (fn th => PURE_REWRITE_TAC[th]) >>
  every_case_tac
QED

(* RETURNDATACOPY terminal fault step: OOB produces AsmFault *)
Theorem terminal_returndatacopy_fault_step[local]:
  !lo o2pc prog st dest_val src_val sz_val rest_stk vs.
    asm_block_at prog st.as_pc [AsmOp "RETURNDATACOPY"] /\
    st.as_stack = dest_val :: src_val :: sz_val :: rest_stk /\
    venom_asm_terminal_rel vs st /\
    w2n src_val + w2n sz_val > LENGTH vs.vs_returndata ==>
    ?st'.
      asm_steps lo o2pc prog 1 st = AsmFault st' /\
      venom_asm_terminal_rel (halt_state (set_returndata [] vs)) st'
Proof
  rpt strip_tac >>
  SUBGOAL_THEN ``1 = SUC 0`` SUBST1_TAC THENL [simp[], ALL_TAC] >>
  simp[Once asm_steps_def, asm_steps_def] >>
  fs[asm_block_at_def] >>
  `st.as_returndata = vs.vs_returndata` by fs[venom_asm_terminal_rel_def] >>
  (* Reduce asm_step to AsmFault directly, then case wrapper trivializes *)
  `asm_step lo o2pc (AsmOp "RETURNDATACOPY") st =
   AsmFault (st with as_returndata := [])` by
    simp[asm_step_def, asm_step_op_def,
         asm_step_arith_def, asm_step_compare_def,
         asm_step_bitwise_def, asm_step_memory_def,
         asm_step_control_def, asm_step_extcall_def,
         asm_step_copy_def, asm_returndatacopy_def, LET_THM] >>
  simp[] >>
  fs[venom_asm_terminal_rel_def, halt_state_def, set_returndata_def]
QED

(* ===== Concrete asm_step equations for terminal opcodes ===== *)

(* Equation form of asm_step for RETURN (analogous to asm_step_stop) *)
Theorem asm_step_return_eq[local]:
  !lo o2pc st off sz rest.
    st.as_stack = off :: sz :: rest ==>
    asm_step lo o2pc (AsmOp "RETURN") st =
      AsmHalt (st with <| as_stack := rest;
                          as_returndata :=
                            TAKE (w2n sz) (DROP (w2n off)
                              (if w2n sz = 0 then st.as_memory
                               else asm_expand_memory (w2n off + w2n sz) st.as_memory));
                          as_memory :=
                            if w2n sz = 0 then st.as_memory
                            else asm_expand_memory (w2n off + w2n sz) st.as_memory |>)
Proof
  rpt strip_tac >>
  simp[asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_return_op_def]
QED

(* Equation form of asm_step for REVERT *)
Theorem asm_step_revert_eq[local]:
  !lo o2pc st off sz rest.
    st.as_stack = off :: sz :: rest ==>
    asm_step lo o2pc (AsmOp "REVERT") st =
      AsmRevert (st with <| as_stack := rest;
                             as_returndata :=
                               TAKE (w2n sz) (DROP (w2n off)
                                 (if w2n sz = 0 then st.as_memory
                                  else asm_expand_memory (w2n off + w2n sz) st.as_memory));
                             as_memory :=
                               if w2n sz = 0 then st.as_memory
                               else asm_expand_memory (w2n off + w2n sz) st.as_memory |>)
Proof
  rpt strip_tac >>
  simp[asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_revert_op_def]
QED

(* ===== Terminal step lemmas for RETURN/REVERT/SELFDESTRUCT ===== *)

(* RETURN terminal step: reads offset+size from stack, sets returndata.
   The returndata agreement depends on memory_rel and the RETURN range
   being outside the spill region (implied by step_mem_safe on the
   input program). *)
Theorem terminal_return_step[local]:
  !lo o2pc prog st off_val sz_val rest_stk ps vs.
    asm_block_at prog st.as_pc [AsmOp "RETURN"] /\
    st.as_stack = off_val :: sz_val :: rest_stk /\
    memory_rel ps.ps_alloc vs.vs_memory st.as_memory /\
    venom_asm_terminal_rel vs st /\
    (* RETURN read range disjoint from spill region *)
    (!i. i < w2n sz_val ==>
      ~(ps.ps_alloc.sa_spill_base <= w2n off_val + i /\
        w2n off_val + i < ps.ps_alloc.sa_next_offset)) ==>
    ?st'.
      asm_steps lo o2pc prog 1 st = AsmHalt st' /\
      venom_asm_terminal_rel
        (halt_state (set_returndata
          (TAKE (w2n sz_val) (DROP (w2n off_val) vs.vs_memory ++
           REPLICATE (w2n sz_val) 0w)) vs)) st'
Proof
  rpt strip_tac >>
  SUBGOAL_THEN ``1 = SUC 0`` SUBST1_TAC THENL [simp[], ALL_TAC] >>
  simp[Once asm_steps_def, asm_steps_def] >>
  fs[asm_block_at_def] >>
  qpat_x_assum `st.as_stack = _` (fn th =>
    assume_tac th >>
    assume_tac (MATCH_MP asm_step_return_eq th)) >>
  simp[] >>
  fs[venom_asm_terminal_rel_def, halt_state_def, set_returndata_def] >>
  Cases_on `w2n sz_val = 0` >> gvs[] >>
  ONCE_REWRITE_TAC[EQ_SYM_EQ] >>
  match_mp_tac returndata_agree >>
  rpt strip_tac >>
  fs[memory_rel_def] >>
  first_x_assum match_mp_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

(* REVERT terminal step: same structure as RETURN but produces AsmRevert *)
Theorem terminal_revert_step[local]:
  !lo o2pc prog st off_val sz_val rest_stk ps vs.
    asm_block_at prog st.as_pc [AsmOp "REVERT"] /\
    st.as_stack = off_val :: sz_val :: rest_stk /\
    memory_rel ps.ps_alloc vs.vs_memory st.as_memory /\
    venom_asm_terminal_rel vs st /\
    (* REVERT read range disjoint from spill region *)
    (!i. i < w2n sz_val ==>
      ~(ps.ps_alloc.sa_spill_base <= w2n off_val + i /\
        w2n off_val + i < ps.ps_alloc.sa_next_offset)) ==>
    ?st'.
      asm_steps lo o2pc prog 1 st = AsmRevert st' /\
      venom_asm_terminal_rel
        (revert_state (set_returndata
          (TAKE (w2n sz_val) (DROP (w2n off_val) vs.vs_memory ++
           REPLICATE (w2n sz_val) 0w)) vs)) st'
Proof
  rpt strip_tac >>
  SUBGOAL_THEN ``1 = SUC 0`` SUBST1_TAC THENL [simp[], ALL_TAC] >>
  simp[Once asm_steps_def, asm_steps_def] >>
  fs[asm_block_at_def] >>
  qpat_x_assum `st.as_stack = _` (fn th =>
    assume_tac th >>
    assume_tac (MATCH_MP asm_step_revert_eq th)) >>
  simp[] >>
  fs[venom_asm_terminal_rel_def, revert_state_def, set_returndata_def] >>
  Cases_on `w2n sz_val = 0` >> gvs[] >>
  ONCE_REWRITE_TAC[EQ_SYM_EQ] >>
  match_mp_tac returndata_agree >>
  rpt strip_tac >>
  fs[memory_rel_def] >>
  first_x_assum match_mp_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

(* SELFDESTRUCT terminal step: pops address, transfers balance.
   Simpler than RETURN/REVERT — no memory/returndata involved. *)
Theorem terminal_selfdestruct_step[local]:
  !lo o2pc prog st addr_val rest_stk vs.
    asm_block_at prog st.as_pc [AsmOp "SELFDESTRUCT"] /\
    st.as_stack = addr_val :: rest_stk /\
    venom_asm_terminal_rel vs st /\
    st.as_call_ctx = vs.vs_call_ctx /\
    st.as_accounts = vs.vs_accounts ==>
    ?st'.
      asm_steps lo o2pc prog 1 st = AsmHalt st' /\
      venom_asm_terminal_rel
        (halt_state (vs with vs_accounts :=
          (\a. if a = vs.vs_call_ctx.cc_address then
                 lookup_account vs.vs_call_ctx.cc_address vs.vs_accounts
                   with balance := 0
               else if a = (w2w addr_val : address) then
                 lookup_account (w2w addr_val) vs.vs_accounts with
                   balance :=
                     (lookup_account vs.vs_call_ctx.cc_address
                        vs.vs_accounts).balance +
                     (lookup_account (w2w addr_val) vs.vs_accounts).balance
               else vs.vs_accounts a)))
        st'
Proof
  rpt strip_tac >>
  SUBGOAL_THEN ``1 = SUC 0`` SUBST1_TAC THENL [simp[], ALL_TAC] >>
  simp[Once asm_steps_def, asm_steps_def] >>
  fs[asm_block_at_def] >>
  REWRITE_TAC[stackOpAsmSimTheory.asm_step_selfdestruct,
              asm_selfdestruct_def] >>
  ASM_REWRITE_TAC[] >>
  fs[venom_asm_terminal_rel_def, halt_state_def, LET_THM]
QED

(* ===== Simple prefix_spill_wf initial_fmp ===== *)

(* All simple stack ops trivially satisfy prefix_spill_wf:
   spill_op_wf only has non-trivial conditions for SOSpill/SORestore,
   which are excluded by is_simple_stack_op. *)
Theorem simple_prefix_spill_wf[local]:
  !ops lo ps. EVERY is_simple_stack_op ops ==> prefix_spill_wf initial_fmp lo ops ps
Proof
  Induct >> simp[prefix_spill_wf_def] >> rpt strip_tac >>
  Cases_on `h` >> gvs[is_simple_stack_op_def, spill_op_wf_def] >>
  TRY (Cases_on `o'` >> gvs[is_simple_stack_op_def, spill_op_wf_def])
QED

(* ===== Generated plan-state well-formedness ===== *)

(* Consumer-facing generated-state invariant.  Range accounting is kept
   separate from the canonical allocator consistency and logical ownership
   properties needed by generated swaps. *)
Definition generated_plan_state_wf_def:
  generated_plan_state_wf base (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)
End

Theorem generated_plan_state_wf_init[local]:
  !base ctr.
    base < dimword(:256) ==>
    generated_plan_state_wf base
      ((init_plan_state base) with ps_label_counter := ctr)
Proof
  simp[generated_plan_state_wf_def, init_plan_state_slots_bounded,
       doSwapSimTheory.spill_alloc_layout_wf_def,
       init_plan_state_def, init_spill_alloc_def]
QED

Theorem do_swap_generated_plan_state_wf:
  !base dist ps lo.
  generated_plan_state_wf base ps /\ dist < LENGTH ps.ps_stack /\
  prefix_spill_wf initial_fmp lo (FST (do_swap dist ps)) ps ==>
  generated_plan_state_wf base (SND (do_swap dist ps))
Proof
  qx_gen_tac `spill_base` >> qx_gen_tac `dist` >>
  qx_gen_tac `ps` >> qx_gen_tac `lo` >> strip_tac >>
  fs[generated_plan_state_wf_def] >>
  `plan_slots_bounded spill_base (SND (do_swap dist ps))` by (
    qspecl_then [`spill_base`, `dist`, `ps`, `FST (do_swap dist ps)`,
      `SND (do_swap dist ps)`] mp_tac do_swap_plan_slots_bounded >>
    simp[]) >>
  `doSwapSim$spill_alloc_layout_wf (SND (do_swap dist ps)).ps_alloc
       (SND (do_swap dist ps)).ps_spilled /\
   ALL_DISTINCT (SND (do_swap dist ps)).ps_stack /\
   DISJOINT (set (SND (do_swap dist ps)).ps_stack)
            (FDOM (SND (do_swap dist ps)).ps_spilled)` by (
    irule doSwapSimTheory.do_swap_structural_layout_wf >> simp[]) >>
  simp[generated_plan_state_wf_def]
QED

Theorem generated_plan_state_wf_free_active_separate[local]:
  !base ps op active free.
    generated_plan_state_wf base ps /\
    FLOOKUP ps.ps_spilled op = SOME active /\
    MEM free ps.ps_alloc.sa_free_slots ==>
    active + 32 <= free \/ free + 32 <= active
Proof
  simp[generated_plan_state_wf_def, doSwapSimTheory.spill_alloc_layout_wf_def] >>
  metis_tac[]
QED

Theorem generated_plan_state_wf_push[local]:
  !base ps op.
    generated_plan_state_wf base ps /\
    ~MEM op ps.ps_stack /\ op NOTIN FDOM ps.ps_spilled ==>
    generated_plan_state_wf base
      (ps with ps_stack := stack_push op ps.ps_stack)
Proof
  simp[generated_plan_state_wf_def, stack_push_def, ALL_DISTINCT_SNOC,
       pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem generated_plan_state_wf_pop[local]:
  !base ps n.
    generated_plan_state_wf base ps ==>
    generated_plan_state_wf base
      (ps with ps_stack := stack_pop n ps.ps_stack)
Proof
  simp[generated_plan_state_wf_def, stack_pop_def] >>
  rpt strip_tac
  >- metis_tac[ALL_DISTINCT_TAKE]
  >> fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  gen_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  `MEM x (TAKE (LENGTH ps.ps_stack - n) ps.ps_stack) ==>
   MEM x ps.ps_stack` by metis_tac[rich_listTheory.MEM_TAKE] >>
  metis_tac[]
QED

Theorem generated_plan_state_wf_remove_free[local]:
  !base ps op off.
    generated_plan_state_wf base ps /\
    FLOOKUP ps.ps_spilled op = SOME off ==>
    generated_plan_state_wf base
      (ps with <| ps_spilled := ps.ps_spilled \\ op;
                  ps_alloc := free_spill_slot off ps.ps_alloc |>)
Proof
  rpt gen_tac >> strip_tac >>
  fs[generated_plan_state_wf_def] >>
  rpt conj_tac
  >- (fs[plan_slots_bounded_def, alloc_slots_bounded_def] >>
      simp[plan_slots_bounded_def, alloc_slots_bounded_def,
           free_spill_slot_def, EVERY_SNOC,
           finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
      metis_tac[])
  >- metis_tac[doSwapSimTheory.spill_alloc_layout_wf_after_free]
  >> fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
        finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
     metis_tac[]
QED

Theorem generated_plan_state_wf_release_fold[local]:
  !dead base ps.
    generated_plan_state_wf base ps /\
    ALL_DISTINCT (MAP FST dead) /\
    (!op off. MEM (op,off) dead ==>
       FLOOKUP ps.ps_spilled op = SOME off) ==>
    generated_plan_state_wf base
      (FOLDL (\ps' (op,off).
         ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                     ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps dead)
Proof
  Induct
  >- simp[]
  >> rpt gen_tac >> PairCases_on `h` >> simp[] >> strip_tac >>
  `FLOOKUP ps.ps_spilled h0 = SOME h1` by metis_tac[] >>
  `generated_plan_state_wf base'
     (ps with <| ps_spilled := ps.ps_spilled \\ h0;
                 ps_alloc := free_spill_slot h1 ps.ps_alloc |>)` by
    metis_tac[generated_plan_state_wf_remove_free] >>
  `!op off. MEM (op,off) dead ==>
     FLOOKUP (ps.ps_spilled \\ h0) op = SOME off` by (
    rpt gen_tac >> strip_tac >>
    `op <> h0` by (
      strip_tac >>
      qpat_x_assum `~MEM h0 (MAP FST dead)` mp_tac >>
      simp[MEM_MAP] >> qexists `(op,off)` >> simp[]) >>
    simp[finite_mapTheory.DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED


Theorem all_distinct_map_fst_filter[local]:
  !(P : ('a # 'b) -> bool) xs.
    ALL_DISTINCT (MAP FST xs) ==>
    ALL_DISTINCT (MAP FST (FILTER P xs))
Proof
  gen_tac >> Induct
  >- simp[]
  >> gen_tac >> PairCases_on `h` >> simp[] >> strip_tac >>
     Cases_on `P (h0,h1)` >> gvs[] >>
     fs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED
Theorem generated_plan_state_wf_release_dead_spills[local]:
  !base next_liveness ps.
    generated_plan_state_wf base ps ==>
    generated_plan_state_wf base (release_dead_spills next_liveness ps)
Proof
  rpt gen_tac >> strip_tac >>
  simp[release_dead_spills_def] >>
  irule generated_plan_state_wf_release_fold >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      fs[MEM_FILTER, alistTheory.MEM_pair_fmap_to_alist_FLOOKUP])
  >- (irule all_distinct_map_fst_filter >>
      simp[alistTheory.ALL_DISTINCT_fmap_to_alist_keys])
  >> first_assum ACCEPT_TAC
QED

(* ===== apply_prefix_ops initial_fmp field preservation ===== *)

(* sa_spill_base is unchanged by any prefix op *)
Theorem apply_prefix_op_spill_base[local]:
  !lo op ps.
    (apply_prefix_op initial_fmp lo op ps).ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[apply_prefix_op_def, apply_simple_op_def] >>
  TRY (Cases_on `o'` >> simp[apply_simple_op_def])
QED

Theorem apply_prefix_ops_spill_base[local]:
  !lo ops ps.
    (apply_prefix_ops initial_fmp lo ops ps).ps_alloc.sa_spill_base =
    ps.ps_alloc.sa_spill_base
Proof
  Induct_on `ops` >>
  simp[apply_prefix_ops_def, apply_prefix_op_spill_base]
QED

(* ===== Per-instruction Halt simulation ===== *)

(* When step_inst returns Halt, the generated plan produces AsmHalt.
   This covers STOP, RETURN, SELFDESTRUCT, INVOKE opcodes. *)
Theorem gen_inst_halt_sim:
  !fuel ctx label_offsets offset_to_pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps'.
    codegen_ready_fn fn /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    ~is_param_opcode inst.inst_opcode /\
    (* EVM compatibility: pipeline obligation *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth: plan_state invariant *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Label resolution: pipeline obligation from compute_label_offsets *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP label_offsets l)) /\
    (* All AsmPushLabel in the executed plan have resolved labels.
       Covers fresh labels from generate_emit_ops (ASSERT/ASSERT_UNREACHABLE/INVOKE).
       Pipeline obligation: compute_label_offsets covers all labels in program. *)
    (!lbl. MEM (AsmPushLabel lbl) (execute_plan initial_fmp ops) ==>
           IS_SOME (FLOOKUP label_offsets lbl)) /\
    (* Provable from generate_inst_plan output (needs new lemma) *)
    prefix_spill_wf initial_fmp label_offsets (FRONT ops) ps /\
    (* After prefix execution, operand values are on the asm stack.
       Dischargeable from reorder correctness + venom_asm_rel stack tracking.
       NOTE: currently blocked by reorder_one_def operand order bug. *)
    (!st_mid. venom_asm_rel label_offsets
        (apply_prefix_ops initial_fmp label_offsets (FRONT ops) ps) vs st_mid ==>
      LENGTH (compute_operands inst) <= LENGTH st_mid.as_stack /\
      !i. i < LENGTH (compute_operands inst) ==>
        eval_operand (EL i (compute_operands inst)) vs =
          SOME (EL i st_mid.as_stack)) /\
    (* RETURN/REVERT: read range below fn_eom (outside spill region).
       Dischargeable: Vyper memory allocator keeps user data below fn_eom. *)
    (!off_v sz_v.
      (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
      eval_operand (EL 0 inst.inst_operands) vs = SOME off_v /\
      eval_operand (EL 1 inst.inst_operands) vs = SOME sz_v ==>
      w2n off_v + w2n sz_v <= ps.ps_alloc.sa_spill_base) /\
    (* STOP: returndata already empty (Vyper STOP at end of void fns) *)
    (inst.inst_opcode = STOP ==> vs.vs_returndata = []) /\
    venom_asm_rel label_offsets ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as'
Proof
  rpt strip_tac >>
  (* Only STOP/RETURN/SINK/SELFDESTRUCT/INVOKE can Halt *)
  imp_res_tac step_inst_halt_opcodes >>
  gvs[]
  >- suspend "stop"
  >- suspend "return"
  >- (
    (* SINK is pre_codegen_opcode — contradiction with SOME *)
    qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
    simp[generate_inst_plan_def, is_pre_codegen_opcode_def]
  )
  >- suspend "selfdestruct"
  >- suspend "invoke"
QED

Resume gen_inst_halt_sim[stop]:
  (* Derive: generate_regular_inst_plan produces (ops, ps') *)
  `generate_regular_inst_plan liveness dfg cfg fn inst
     next_liveness is_halting next_is_term bb_label ps = (ops, ps')` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def] >>
     `~is_pre_codegen_opcode STOP` by EVAL_TAC >> simp[]) >>
  `inst.inst_outputs = []` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> fs[]) >>
  `vs' = halt_state vs` by
    (imp_res_tac step_inst_stop_halt >> fs[]) >>
  gvs[] >>
  (* Use gen_inst_terminal_setup to get AsmOK intermediate *)
  qspecl_then [`fuel`, `ctx`, `label_offsets`, `offset_to_pc`, `prog`,
    `liveness`, `dfg`, `cfg`, `fn`, `inst`, `next_liveness`,
    `is_halting`, `next_is_term`, `bb_label`, `ps`, `vs`, `as`,
    `ops`, `ps'`, `"STOP"`] mp_tac gen_inst_terminal_setup >>
  (impl_tac >- (
    rpt conj_tac >> gvs[] >> TRY EVAL_TAC >> gvs[]
  )) >>
  strip_tac >>
  (* Terminal STOP step — specialize lo/o2pc *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`, `st'`, `vs`]
    mp_tac terminal_stop_step >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Compose prefix AsmOK + terminal AsmHalt *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`,
    `LENGTH (execute_plan initial_fmp ops) - 1`, `1`, `as`, `st'`, `st''`]
    mp_tac asm_steps_compose_halt >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp ops) - 1 + 1`, `st''`] >>
  simp[]
QED

Resume gen_inst_halt_sim[return]:
  (* Decompose step_inst RETURN *)
  drule_all step_inst_return_halt >> strip_tac >> gvs[] >>
  (* inst.inst_outputs = [] via inst_wf + RETURN opcode *)
  `inst.inst_outputs = ([] : string list)` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> fs[]) >>
  (* gen_inst_terminal_setup_strong -> AsmOK at prefix end *)
  qspecl_then [`fuel`, `ctx`, `label_offsets`, `offset_to_pc`, `prog`,
    `liveness`, `dfg`, `cfg`, `fn`, `inst`, `next_liveness`,
    `is_halting`, `next_is_term`, `bb_label`, `ps`, `vs`, `as`,
    `ops`, `ps'`, `"RETURN"`] mp_tac gen_inst_terminal_setup_strong >>
  (impl_tac >- (
    rpt conj_tac >> gvs[] >> TRY EVAL_TAC >> gvs[]
  )) >>
  strip_tac >>
  (* Get operand values on asm stack *)
  qpat_x_assum `!st_mid. venom_asm_rel _ _ _ st_mid ==> _` mp_tac >>
  qpat_assum `ops = _` (fn th => PURE_REWRITE_TAC[th]) >>
  simp[rich_listTheory.FRONT_APPEND] >>
  disch_then (qspec_then `st'` mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  simp[compute_operands_def] >>
  strip_tac >>
  (* Derive stack shape off_val :: sz_val :: rest *)
  SUBGOAL_THEN
    ``?rest_stk. (st':asm_state).as_stack = off_val :: sz_val :: rest_stk``
    STRIP_ASSUME_TAC
  THENL [
    Cases_on `st'.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    qpat_x_assum `!i. i < 2 ==> _`
      (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >>
    simp[],
    ALL_TAC] >>
  (* Extract memory_rel from venom_asm_rel *)
  `memory_rel (apply_prefix_ops initial_fmp label_offsets prefix_ops ps).ps_alloc
              vs.vs_memory st'.as_memory` by
    fs[venom_asm_rel_def] >>
  (* Terminal RETURN step *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`, `st'`,
    `off_val`, `sz_val`, `rest_stk`,
    `apply_prefix_ops initial_fmp label_offsets prefix_ops ps`, `vs`]
    mp_tac terminal_return_step >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (match_mp_tac (GEN_ALL venom_asm_rel_terminal) >>
        qexists_tac `label_offsets` >>
        qexists_tac `apply_prefix_ops initial_fmp label_offsets prefix_ops ps` >>
        first_assum ACCEPT_TAC)
    >- (rpt strip_tac >>
        `(apply_prefix_ops initial_fmp label_offsets prefix_ops ps).ps_alloc.sa_spill_base =
         ps.ps_alloc.sa_spill_base` by simp[apply_prefix_ops_spill_base] >>
        decide_tac)
  )) >> strip_tac >>
  (* Compose prefix AsmOK + terminal AsmHalt *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`,
    `LENGTH (execute_plan initial_fmp ops) - 1`, `1`, `as`, `st'`, `st''`]
    mp_tac asm_steps_compose_halt >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp ops) - 1 + 1`, `st''`] >>
  simp[]
QED

Resume gen_inst_halt_sim[selfdestruct]:
  (* Decompose step_inst SELFDESTRUCT *)
  drule_all step_inst_selfdestruct_halt >> strip_tac >> gvs[] >>
  (* inst.inst_outputs = [] via inst_wf + SELFDESTRUCT opcode *)
  `inst.inst_outputs = ([] : string list)` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> fs[]) >>
  (* gen_inst_terminal_setup_strong -> AsmOK at prefix end *)
  qspecl_then [`fuel`, `ctx`, `label_offsets`, `offset_to_pc`, `prog`,
    `liveness`, `dfg`, `cfg`, `fn`, `inst`, `next_liveness`,
    `is_halting`, `next_is_term`, `bb_label`, `ps`, `vs`, `as`,
    `ops`, `ps'`, `"SELFDESTRUCT"`] mp_tac gen_inst_terminal_setup_strong >>
  (impl_tac >- (
    rpt conj_tac >> gvs[] >> TRY EVAL_TAC >> gvs[]
  )) >>
  strip_tac >>
  (* Use operands_on_asm_stack hypothesis to get addr_val at TOS *)
  qpat_x_assum `!st_mid. venom_asm_rel _ _ _ st_mid ==> _` mp_tac >>
  qpat_assum `ops = _` (fn th => PURE_REWRITE_TAC[th]) >>
  simp[rich_listTheory.FRONT_APPEND] >>
  disch_then (qspec_then `st'` mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  simp[compute_operands_def] >>
  strip_tac >>
  SUBGOAL_THEN
    ``?rest_stk. (st':asm_state).as_stack = addr_val :: rest_stk``
    STRIP_ASSUME_TAC
  THENL [
    Cases_on `st'.as_stack` >> gvs[],
    ALL_TAC] >>
  (* Terminal SELFDESTRUCT step *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`, `st'`,
    `addr_val`, `rest_stk`, `vs`]
    mp_tac terminal_selfdestruct_step >>
  (* Extract call_ctx and accounts from venom_asm_rel for st' *)
  `st'.as_call_ctx = vs.vs_call_ctx /\ st'.as_accounts = vs.vs_accounts` by
    (qpat_x_assum `venom_asm_rel _ _ _ st'` mp_tac >>
     PURE_REWRITE_TAC[venom_asm_rel_def] >> strip_tac >> ASM_REWRITE_TAC[]) >>
  (impl_tac >- (
    rpt conj_tac >>
    FIRST [
      first_assum ACCEPT_TAC,
      match_mp_tac (GEN_ALL venom_asm_rel_terminal) >>
        qexists_tac `label_offsets` >>
        qexists_tac `apply_prefix_ops initial_fmp label_offsets prefix_ops ps` >>
        first_assum ACCEPT_TAC
    ]
  )) >> strip_tac >>
  (* Compose prefix AsmOK + terminal AsmHalt *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`,
    `LENGTH (execute_plan initial_fmp ops) - 1`, `1`, `as`, `st'`, `st''`]
    mp_tac asm_steps_compose_halt >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp ops) - 1 + 1`, `st''`] >>
  qpat_x_assum `addr_val = HD _` (SUBST_ALL_TAC o SYM) >>
  ASM_REWRITE_TAC[]
QED

Resume gen_inst_halt_sim[invoke]:
  cheat
QED

Finalise gen_inst_halt_sim;

(* ===== Per-instruction Abort simulation ===== *)

(* When step_inst returns Abort, the generated plan produces AsmRevert/AsmFault *)
Theorem gen_inst_abort_sim:
  !fuel ctx label_offsets offset_to_pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps' a.
    codegen_ready_fn fn /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    ~is_param_opcode inst.inst_opcode /\
    (* EVM compatibility: pipeline obligation *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth: plan_state invariant *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Label resolution: pipeline obligation from compute_label_offsets *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP label_offsets l)) /\
    (* All AsmPushLabel in the executed plan have resolved labels.
       Pipeline obligation: compute_label_offsets covers all labels in program. *)
    (!lbl. MEM (AsmPushLabel lbl) (execute_plan initial_fmp ops) ==>
           IS_SOME (FLOOKUP label_offsets lbl)) /\
    (* Provable from generate_inst_plan output (needs new lemma) *)
    prefix_spill_wf initial_fmp label_offsets (FRONT ops) ps /\
    (* Spill offsets are non-overlapping.
       Dischargeable from spill_alloc_wf invariant maintained by plan_state. *)
    (!op1 off1 op2 off2.
       FLOOKUP ps.ps_spilled op1 = SOME off1 /\
       FLOOKUP ps.ps_spilled op2 = SOME off2 /\
       op1 <> op2 ==> off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
    (* After prefix execution, operand values are on the asm stack.
       Dischargeable from reorder correctness + venom_asm_rel stack tracking.
       NOTE: currently blocked by reorder_one_def operand order bug. *)
    (!st_mid. venom_asm_rel label_offsets
        (apply_prefix_ops initial_fmp label_offsets (FRONT ops) ps) vs st_mid ==>
      LENGTH (compute_operands inst) <= LENGTH st_mid.as_stack /\
      !i. i < LENGTH (compute_operands inst) ==>
        eval_operand (EL i (compute_operands inst)) vs =
          SOME (EL i st_mid.as_stack)) /\
    (* Label operands have consistent values between eval_operand
       and operand_val (the plan-stack-based evaluation).
       Dischargeable: trivially true when vs.vs_labels = FEMPTY (normal case). *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op vs = operand_val vs label_offsets op) /\
    (* DFG operand_equiv is sound: equivalent operands have the same
       runtime value. Dischargeable from DFG construction correctness. *)
    (!op1 op2. MEM op1 (compute_operands inst) /\
               operand_equiv dfg op1 op2 ==>
               operand_val vs label_offsets op1 =
               operand_val vs label_offsets op2) /\
    (* RETURN/REVERT: read range below fn_eom (outside spill region).
       Dischargeable: Vyper memory allocator keeps user data below fn_eom. *)
    (!off_v sz_v.
      (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
      eval_operand (EL 0 inst.inst_operands) vs = SOME off_v /\
      eval_operand (EL 1 inst.inst_operands) vs = SOME sz_v ==>
      w2n off_v + w2n sz_v <= ps.ps_alloc.sa_spill_base) /\
    (* Non-spilled Var operands on the stack have depth <= 15.
       Dischargeable: invariant maintained by reduce_depth in input plan. *)
    (!op d. MEM op (compute_operands inst) /\
            is_var_operand op /\
            ~IS_SOME (FLOOKUP ps.ps_spilled op) /\
            stack_get_depth op ps.ps_stack = SOME d ==> d <= 15) /\
    (* Operands are accessible: on stack or spilled.
       Dischargeable from def_dominates_uses + plan_state invariant
       (all defined vars tracked in stack or spills). *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
          (?d. stack_get_depth op ps.ps_stack = SOME d) \/
          IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    venom_asm_rel label_offsets ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\
          asm_steps label_offsets offset_to_pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\
          asm_steps label_offsets offset_to_pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as'
Proof
  rpt strip_tac >>
  imp_res_tac step_inst_abort_opcodes >>
  gvs[]
  >- suspend "revert"
  >- suspend "invalid"
  >- (
    (* ASSERT — maps to [ISZERO; PushLabel "revert"; JUMPI]
       Abort case (cond = 0w): ISZERO yields 1w => JUMPI jumps to revert label.
       BLOCKER: Cross-block property — revert_postamble is appended in
       codegen_def. Needs:
         (1) FLOOKUP label_offsets "revert" = SOME off,
         (2) revert_postamble at that offset does [PUSH 0; PUSH 0; REVERT]
         (3) asm_steps through the postamble yields AsmRevert. *)
    cheat
  )
  >- (
    (* ASSERT_UNREACHABLE — maps to
       [SOPushLabel end_lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel end_lbl]
       where end_lbl = fresh_label "reachable" ps.

       Abort path (cond=0w):
         After prefix: cond_val=0w on TOS.
         1. AsmPushLabel end_lbl => pushes n2w off. Stack: [n2w off; 0w; rest]
         2. AsmOp "JUMPI" => cond=0w => falls through. PC -> INVALID.
         3. AsmOp "INVALID" => AsmFault (s with as_returndata := [])
         Label end_lbl not reached (only for the OK/non-abort path).

       Self-contained: end_lbl is within the same instruction's plan,
       no cross-block dependency. *)
    suspend "assert_unreachable"
  )
  >- suspend "returndatacopy"
  >- (
    (* INVOKE — recursive: step_inst uses fuel, invokes run_blocks on callee.
       Plan: [SOPushLabel ret_lbl; SOPushLabel fn_lbl; SOEmit "JUMP";
              SOLabel ret_lbl]
       INVOKE abort requires proving that the callee's execution produces
       a corresponding abort in the generated assembly. This needs
       gen_fn_simulation as an inductive hypothesis (mutual recursion
       between gen_inst_simulation and gen_fn_simulation). *)
    cheat
  )
QED

Resume gen_inst_abort_sim[revert]:
  (* Decompose step_inst REVERT *)
  drule_all step_inst_revert_abort >> strip_tac >> gvs[] >>
  (* inst.inst_outputs = [] via inst_wf + REVERT opcode *)
  `inst.inst_outputs = ([] : string list)` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> fs[]) >>
  (* gen_inst_terminal_setup_strong -> AsmOK at prefix end *)
  qspecl_then [`fuel`, `ctx`, `label_offsets`, `offset_to_pc`, `prog`,
    `liveness`, `dfg`, `cfg`, `fn`, `inst`, `next_liveness`,
    `is_halting`, `next_is_term`, `bb_label`, `ps`, `vs`, `as`,
    `ops`, `ps'`, `"REVERT"`] mp_tac gen_inst_terminal_setup_strong >>
  (impl_tac >- (
    rpt conj_tac >> gvs[] >> TRY EVAL_TAC >> gvs[]
  )) >>
  strip_tac >>
  (* Get operand values on asm stack *)
  qpat_x_assum `!st_mid. venom_asm_rel _ _ _ st_mid ==> _` mp_tac >>
  qpat_assum `ops = _` (fn th => PURE_REWRITE_TAC[th]) >>
  simp[rich_listTheory.FRONT_APPEND] >>
  disch_then (qspec_then `st'` mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  simp[compute_operands_def] >>
  strip_tac >>
  (* Derive stack shape off_val :: sz_val :: rest *)
  SUBGOAL_THEN
    ``?rest_stk. (st':asm_state).as_stack = off_val :: sz_val :: rest_stk``
    STRIP_ASSUME_TAC
  THENL [
    Cases_on `st'.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    qpat_x_assum `!i. i < 2 ==> _`
      (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >>
    simp[],
    ALL_TAC] >>
  (* Extract memory_rel from venom_asm_rel *)
  `memory_rel (apply_prefix_ops initial_fmp label_offsets prefix_ops ps).ps_alloc
              vs.vs_memory st'.as_memory` by
    fs[venom_asm_rel_def] >>
  (* Terminal REVERT step *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`, `st'`,
    `off_val`, `sz_val`, `rest_stk`,
    `apply_prefix_ops initial_fmp label_offsets prefix_ops ps`, `vs`]
    mp_tac terminal_revert_step >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (match_mp_tac (GEN_ALL venom_asm_rel_terminal) >>
        qexists_tac `label_offsets` >>
        qexists_tac `apply_prefix_ops initial_fmp label_offsets prefix_ops ps` >>
        first_assum ACCEPT_TAC)
    >- (rpt strip_tac >>
        `(apply_prefix_ops initial_fmp label_offsets prefix_ops ps).ps_alloc.sa_spill_base =
         ps.ps_alloc.sa_spill_base` by simp[apply_prefix_ops_spill_base] >>
        decide_tac)
  )) >> strip_tac >>
  (* Compose prefix AsmOK + terminal AsmRevert *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`,
    `LENGTH (execute_plan initial_fmp ops) - 1`, `1`, `as`, `st'`, `st''`]
    mp_tac asm_steps_compose_revert >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp ops) - 1 + 1`, `st''`] >>
  simp[]
QED

Resume gen_inst_abort_sim[invalid]:
  (* INVALID: generate_inst_plan -> generate_regular_inst_plan *)
  `generate_regular_inst_plan liveness dfg cfg fn inst
     next_liveness is_halting next_is_term bb_label ps = (ops, ps')` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def] >>
     `~is_pre_codegen_opcode INVALID` by EVAL_TAC >> simp[]) >>
  `inst.inst_outputs = []` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> fs[]) >>
  (* INVALID: abort state clears returndata *)
  `a = ExHalt_abort /\
   vs' = vs with <| vs_returndata := []; vs_halted := T |>` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[Once step_inst_def] >>
     qpat_x_assum `inst.inst_opcode = INVALID`
       (fn th => assume_tac th >> PURE_REWRITE_TAC[th]) >>
     simp[is_terminator_def] >>
     ONCE_REWRITE_TAC[step_inst_base_def] >>
     qpat_x_assum `inst.inst_opcode = INVALID`
       (fn th => PURE_REWRITE_TAC[th]) >>
     simp[halt_state_def, set_returndata_def]) >>
  gvs[] >>
  (* Use gen_inst_terminal_setup to get AsmOK intermediate *)
  qspecl_then [`fuel`, `ctx`, `label_offsets`, `offset_to_pc`, `prog`,
    `liveness`, `dfg`, `cfg`, `fn`, `inst`, `next_liveness`,
    `is_halting`, `next_is_term`, `bb_label`, `ps`, `vs`, `as`,
    `ops`, `ps'`, `"INVALID"`] mp_tac gen_inst_terminal_setup >>
  (impl_tac >- (
    rpt conj_tac >> gvs[] >> TRY EVAL_TAC >> gvs[]
  )) >>
  strip_tac >>
  (* Terminal INVALID step — specialize lo/o2pc *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`, `st'`, `vs`]
    mp_tac terminal_invalid_step >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Compose prefix AsmOK + terminal AsmFault *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`,
    `LENGTH (execute_plan initial_fmp ops) - 1`, `1`, `as`, `st'`, `st''`]
    mp_tac asm_steps_compose_fault >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp ops) - 1 + 1`, `st''`] >>
  simp[]
QED

Resume gen_inst_abort_sim[returndatacopy]:
  (* Decompose step_inst RETURNDATACOPY *)
  drule_all step_inst_returndatacopy_abort >> strip_tac >> gvs[] >>
  (* inst.inst_outputs = [] via inst_wf + RETURNDATACOPY *)
  `inst.inst_outputs = ([] : string list)` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> fs[]) >>
  (* gen_inst_terminal_setup_strong -> AsmOK at prefix end *)
  qspecl_then [`fuel`, `ctx`, `label_offsets`, `offset_to_pc`, `prog`,
    `liveness`, `dfg`, `cfg`, `fn`, `inst`, `next_liveness`,
    `is_halting`, `next_is_term`, `bb_label`, `ps`, `vs`, `as`,
    `ops`, `ps'`, `"RETURNDATACOPY"`] mp_tac gen_inst_terminal_setup_strong >>
  (impl_tac >- (
    rpt conj_tac >> gvs[] >> TRY EVAL_TAC >> gvs[]
  )) >>
  strip_tac >>
  (* Get operand values on asm stack *)
  qpat_x_assum `!st_mid. venom_asm_rel _ _ _ st_mid ==> _` mp_tac >>
  qpat_assum `ops = _` (fn th => PURE_REWRITE_TAC[th]) >>
  simp[rich_listTheory.FRONT_APPEND] >>
  disch_then (qspec_then `st'` mp_tac) >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  simp[compute_operands_def] >>
  strip_tac >>
  (* Derive stack shape dest :: src :: sz :: rest *)
  SUBGOAL_THEN
    ``?rest_stk. (st':asm_state).as_stack =
       dest_val :: src_val :: sz_val :: rest_stk``
    STRIP_ASSUME_TAC
  THENL [
    Cases_on `st'.as_stack` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    Cases_on `t'` >> gvs[] >>
    qpat_x_assum `!i. i < 3 ==> _`
      (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th) >>
                mp_tac (Q.SPEC `2` th)) >>
    simp[],
    ALL_TAC] >>
  (* Terminal RETURNDATACOPY fault step *)
  `st'.as_returndata = vs.vs_returndata` by
    (qpat_x_assum `venom_asm_rel _ _ _ st'` mp_tac >>
     PURE_REWRITE_TAC[venom_asm_rel_def] >> strip_tac >> ASM_REWRITE_TAC[]) >>
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`, `st'`,
    `dest_val`, `src_val`, `sz_val`, `rest_stk`, `vs`]
    mp_tac terminal_returndatacopy_fault_step >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (match_mp_tac (GEN_ALL venom_asm_rel_terminal) >>
        qexists_tac `label_offsets` >>
        qexists_tac `apply_prefix_ops initial_fmp label_offsets prefix_ops ps` >>
        first_assum ACCEPT_TAC)
  )) >> strip_tac >>
  (* Compose prefix AsmOK + terminal AsmFault *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`,
    `LENGTH (execute_plan initial_fmp ops) - 1`, `1`, `as`, `st'`, `st''`]
    mp_tac asm_steps_compose_fault >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp ops) - 1 + 1`, `st''`] >>
  simp[]
QED

(* 3-step terminal: PushLabel end_lbl; JUMPI (falls through, cond=0w); INVALID *)
Theorem terminal_pushlabel_jumpi_invalid[local]:
  !lo o2pc prog st end_lbl off rest_stk vs.
    asm_block_at prog st.as_pc
      [AsmPushLabel end_lbl; AsmOp "JUMPI"; AsmOp "INVALID";
       AsmLabel end_lbl] /\
    st.as_stack = 0w :: rest_stk /\
    FLOOKUP lo end_lbl = SOME off /\
    venom_asm_terminal_rel vs st ==>
    ?st'.
      asm_steps lo o2pc prog 3 st = AsmFault st' /\
      venom_asm_terminal_rel
        (vs with <| vs_returndata := []; vs_halted := T |>) st'
Proof
  rpt strip_tac >>
  fs[asm_block_at_def] >>
  `EL st.as_pc prog = AsmPushLabel end_lbl` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `EL (st.as_pc + 1) prog = AsmOp "JUMPI"` by
    (first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  `EL (st.as_pc + 2) prog = AsmOp "INVALID"` by
    (first_x_assum (qspec_then `2` mp_tac) >> simp[]) >>
  Q.EXISTS_TAC `st with <| as_pc := st.as_pc + 2;
    as_stack := rest_stk; as_returndata := [] |>` >>
  `asm_step lo o2pc (AsmPushLabel end_lbl) st =
   AsmOK (asm_next (st with as_stack := n2w off :: st.as_stack))` by
    simp[asm_step_pushlabel_ok] >>
  (* PushLabel *)
  `3 = SUC 2` by DECIDE_TAC >> pop_assum SUBST1_TAC >>
  rewrite_tac[Once asm_steps_def] >> simp[asm_next_def] >>
  (* JUMPI fallthrough (cond=0w) *)
  `2 = SUC 1` by DECIDE_TAC >> pop_assum SUBST1_TAC >>
  rewrite_tac[Once asm_steps_def] >>
  simp[asm_step_jumpi, asm_jumpi_def, asm_next_def] >>
  (* INVALID *)
  `1 = SUC 0` by DECIDE_TAC >> pop_assum SUBST1_TAC >>
  rewrite_tac[asm_steps_def] >>
  simp[asm_step_invalid] >>
  fs[venom_asm_terminal_rel_def]
QED

Resume gen_inst_abort_sim[assert_unreachable]:
  (* Decompose step_inst *)
  qspecl_then [`fuel`, `ctx`, `inst`, `vs`, `a`, `vs'`]
    mp_tac step_inst_assert_unreachable_abort >>
  (impl_tac >- fs[]) >> strip_tac >> gvs[] >>
  (* inst.inst_outputs = [], compute_operands *)
  `inst.inst_outputs = ([] : string list)` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_opcode` >> fs[]) >>
  `compute_operands inst = [cond_op]` by simp[compute_operands_def] >>
  (* Unfold generate_inst_plan *)
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, generate_regular_inst_plan_def,
       LET_THM, compute_operands_def] >>
  PURE_REWRITE_TAC[EVAL ``is_pre_codegen_opcode ASSERT_UNREACHABLE``,
    EVAL ``is_commutative ASSERT_UNREACHABLE``] >> simp[] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  simp[generate_emit_ops_def, venom_to_evm_name_def, LET_THM] >>
  Cases_on `fresh_label "reachable"
    (ps4 with ps_stack := stack_pop 1 ps4.ps_stack)` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `fresh_label _ _ = (end_lbl, _)` >>
  (* prefix_wf and EVERY is_prefix_op for input_ops ++ reorder_ops *)
  `prefix_wf label_offsets (LENGTH ps.ps_stack)
     (input_ops ++ reorder_ops) /\
   EVERY is_prefix_op (input_ops ++ reorder_ops)` by
    suspend "prefix_wf" >>
  (* prefix_spill_wf initial_fmp *)
  `prefix_spill_wf initial_fmp label_offsets (input_ops ++ reorder_ops) ps` by (
    qpat_x_assum `prefix_spill_wf initial_fmp _ (FRONT _) _` mp_tac >>
    rewrite_tac[rich_listTheory.FRONT_APPEND, NOT_NIL_CONS] >>
    metis_tac[prefix_spill_wf_prefix]) >>
  (* prefix_sim *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`, `ps`, `vs`, `as`,
    `input_ops ++ reorder_ops`,
    `[SOPushLabel end_lbl; SOEmit "JUMPI";
      SOEmit "INVALID"; SOLabel end_lbl]`]
    mp_tac prefix_sim >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* HD st_mid.as_stack = 0w *)
  `HD st_mid.as_stack = 0w` by suspend "hd_zero" >>
  (* FLOOKUP label_offsets end_lbl *)
  `IS_SOME (FLOOKUP label_offsets end_lbl)` by (
    qpat_x_assum `!lbl. MEM (AsmPushLabel lbl) _ ==> _`
      (qspec_then `end_lbl` mp_tac) >>
    simp[execute_plan_def, exec_stack_op_def]) >>
  `?off. FLOOKUP label_offsets end_lbl = SOME off` by
    (Cases_on `FLOOKUP label_offsets end_lbl` >> fs[]) >>
  (* st_mid.as_stack = 0w :: rest *)
  `st_mid.as_stack = 0w :: TL st_mid.as_stack` by
    suspend "as_stack_decompose" >>
  (* terminal_pushlabel_jumpi_invalid *)
  `venom_asm_terminal_rel vs st_mid` by (
    irule venom_asm_rel_terminal >>
    Q.EXISTS_TAC `label_offsets` >>
    Q.EXISTS_TAC `apply_prefix_ops initial_fmp label_offsets
      (input_ops ++ reorder_ops) ps` >>
    first_assum ACCEPT_TAC) >>
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`, `st_mid`,
    `end_lbl`, `off`, `TL st_mid.as_stack`, `vs`]
    mp_tac terminal_pushlabel_jumpi_invalid >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_x_assum `asm_block_at _ st_mid.as_pc (execute_plan initial_fmp _)` mp_tac >>
    simp[execute_plan_def, exec_stack_op_def])) >> strip_tac >>
  (* Compose *)
  qspecl_then [`label_offsets`, `offset_to_pc`, `prog`,
    `LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops))`, `3`,
    `as`, `st_mid`] mp_tac asm_steps_compose_fault >>
  disch_then (qspec_then `st'` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  Q.EXISTS_TAC
    `LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops)) + 3` >>
  Q.EXISTS_TAC `st'` >>
  simp[halt_state_def, set_returndata_def]
QED

(* prefix_wf: emit_input_plan + reorder_plan both produce prefix_wf ops *)
Resume gen_inst_abort_sim[prefix_wf]:
  (* emit_input_plan gives prefix_wf for input_ops *)
  `prefix_wf label_offsets (LENGTH ps.ps_stack) input_ops /\
   prefix_end_len label_offsets (LENGTH ps.ps_stack) input_ops =
   LENGTH ps1.ps_stack` by (
    qspecl_then [`[cond_op]`, `ASSERT_UNREACHABLE`,
                 `next_liveness`, `ps`, `label_offsets`]
      mp_tac emit_input_plan_wf_len >>
    simp[]) >>
  (* reorder_plan gives prefix_wf for reorder_ops *)
  `prefix_wf label_offsets (LENGTH ps1.ps_stack) reorder_ops` by (
    qspecl_then [`dfg`, `[cond_op]`, `ps1`, `label_offsets`]
      mp_tac (delet reorder_plan_wf_len) >>
    simp[]) >>
  conj_tac
  >- (qspecl_then [`input_ops`, `reorder_ops`, `label_offsets`,
        `LENGTH ps.ps_stack`] mp_tac prefix_wf_append >>
      (impl_tac >- fs[]) >> simp[])
  >> (imp_res_tac prefix_wf_every_prefix_op >> fs[EVERY_APPEND])
QED

(* apply_prefix_ops initial_fmp depends only on ps_stack and ps_spilled.
   Two states agreeing on those fields produce the same result. *)
Theorem apply_prefix_ops_ext_stack_spilled[local]:
  !ops lo ps1 ps2.
    ps1.ps_stack = ps2.ps_stack /\
    ps1.ps_spilled = ps2.ps_spilled ==>
    (apply_prefix_ops initial_fmp lo ops ps1).ps_stack =
      (apply_prefix_ops initial_fmp lo ops ps2).ps_stack /\
    (apply_prefix_ops initial_fmp lo ops ps1).ps_spilled =
      (apply_prefix_ops initial_fmp lo ops ps2).ps_spilled
Proof
  Induct >> simp[apply_prefix_ops_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  Cases_on `h` >>
  simp[apply_prefix_op_def, apply_simple_op_def,
       stack_push_def, stack_pop_def, stack_swap_def,
       stack_peek_def, stack_poke_def, spill_lookup_def] >>
  TRY (Cases_on `o'` >> simp[apply_simple_op_def, stack_push_def])
QED

(* stack_get_depth after stack_push: the pushed operand is at depth 0 *)
Theorem stack_get_depth_push[local]:
  !op stk. stack_get_depth op (stack_push op stk) = SOME 0
Proof
  rw[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def]
QED

(* stack_find returns an index where the predicate holds *)
Theorem stack_find_el[local]:
  !P l d. stack_find P l = SOME d ==> P (EL d l)
Proof
  Induct_on `l` >> simp[stack_find_def] >> rpt strip_tac >>
  every_case_tac >> gvs[ADD1, EL_CONS]
QED

(* stack_get_depth gives the depth of an operand matching stack_peek *)
Theorem stack_get_depth_peek[local]:
  !op stk d. stack_get_depth op stk = SOME d ==> stack_peek d stk = op
Proof
  rw[stack_get_depth_def, stack_peek_def] >>
  imp_res_tac stack_find_el >>
  imp_res_tac stack_find_bound >>
  qspecl_then [`d`, `stk`] mp_tac EL_REVERSE >>
  simp[] >> strip_tac >>
  `PRE (LENGTH stk - d) = LENGTH stk - (d + 1)` by decide_tac >>
  gvs[]
QED

(* After shallow do_dup, the operand is at depth 0 *)
Theorem do_dup_shallow_depth[local]:
  !op dist ps.
    stack_get_depth op ps.ps_stack = SOME dist /\ dist <= 15 ==>
    stack_get_depth op (SND (do_dup dist ps)).ps_stack = SOME 0
Proof
  rw[do_dup_def] >>
  imp_res_tac stack_get_depth_peek >>
  simp[stack_dup_def, GSYM stack_push_def, stack_get_depth_push]
QED

(* --- Helpers for do_dup deep-case contradiction --- *)

(* prefix_spill_wf initial_fmp decomposition at last element *)
Theorem prefix_spill_wf_snoc[local]:
  !ops op lo ps.
    prefix_spill_wf initial_fmp lo (ops ++ [op]) ps <=>
    prefix_spill_wf initial_fmp lo ops ps /\
    spill_op_wf (apply_prefix_ops initial_fmp lo ops ps) op
Proof
  Induct >> simp[prefix_spill_wf_def, apply_prefix_ops_def] >>
  rpt gen_tac >> metis_tac[]
QED

(* FRANGE can only shrink through SORestore-only sequences *)
Theorem frange_restore_only_mono[local]:
  !ops lo ps off.
    EVERY (\op. ?off'. op = SORestore off') ops /\
    off IN FRANGE (apply_prefix_ops initial_fmp lo ops ps).ps_spilled ==>
    off IN FRANGE ps.ps_spilled
Proof
  Induct >> simp[apply_prefix_ops_def] >>
  rpt gen_tac >> Cases_on `h` >> simp[] >>
  strip_tac >> rename1 `SORestore n` >>
  `off IN FRANGE (apply_prefix_op initial_fmp lo (SORestore n) ps).ps_spilled` by
    metis_tac[] >>
  pop_assum mp_tac >>
  simp[apply_prefix_op_def, LET_THM] >>
  metis_tac[finite_mapTheory.FRANGE_DOMSUB_SUBSET,
            pred_setTheory.SUBSET_DEF]
QED

(* If off has unique pre-image k in f, DOMSUB k removes off from FRANGE *)
Theorem domsub_unique_removes_from_frange[local]:
  !f k (off:num).
    FLOOKUP f k = SOME off /\
    (!k'. k' <> k ==> FLOOKUP f k' <> SOME off) ==>
    off NOTIN FRANGE (f \\ k)
Proof
  rpt strip_tac >>
  fs[finite_mapTheory.FRANGE_FLOOKUP, finite_mapTheory.FLOOKUP_DEF,
     finite_mapTheory.DOMSUB_FAPPLY_THM, finite_mapTheory.FDOM_DOMSUB] >>
  Cases_on `x = k` >> gvs[]
QED

(* After SORestore off, if off had unique pre-image, off leaves FRANGE *)
Theorem restore_unique_clears_frange[local]:
  !off ps lo.
    (?op. FLOOKUP ps.ps_spilled op = SOME off) /\
    (!op1 op2. FLOOKUP ps.ps_spilled op1 = SOME off /\
               FLOOKUP ps.ps_spilled op2 = SOME off ==> op1 = op2) ==>
    off NOTIN FRANGE (apply_prefix_op initial_fmp lo (SORestore off) ps).ps_spilled
Proof
  rpt strip_tac >>
  `FLOOKUP ps.ps_spilled (spill_lookup off ps.ps_spilled) = SOME off` by (
    simp[spill_lookup_def] >> SELECT_ELIM_TAC >> metis_tac[]) >>
  qpat_x_assum `off IN FRANGE _` mp_tac >>
  simp[apply_prefix_op_def, LET_THM, finite_mapTheory.FRANGE_FLOOKUP] >>
  rpt strip_tac >>
  rename1 `FLOOKUP (_ \\ _) k = SOME off` >>
  qpat_x_assum `FLOOKUP (_ \\ _) _ = _` mp_tac >>
  simp[finite_mapTheory.DOMSUB_FLOOKUP_THM]
QED

(* FUPDATE preserves "not in FRANGE" for different values *)
Theorem fupdate_not_in_frange[local]:
  !(f:'a |-> num) k v off.
    off NOTIN FRANGE f /\ off <> v ==>
    off NOTIN FRANGE (f |+ (k, v))
Proof
  rw[finite_mapTheory.FRANGE_FUPDATE_DOMSUB] >>
  metis_tac[finite_mapTheory.FRANGE_DOMSUB_SUBSET,
            pred_setTheory.SUBSET_DEF]
QED

(* After prefix_spill_wf initial_fmp SOSpill sequence, an offset not originally in
   FRANGE and not equal to any spilled offset stays out of FRANGE *)
Theorem spill_seq_not_in_frange[local]:
  !ops lo ps off.
    EVERY (\op. ?off'. op = SOSpill off' /\ off' <> off) ops /\
    prefix_spill_wf initial_fmp lo ops ps /\
    off NOTIN FRANGE ps.ps_spilled ==>
    off NOTIN FRANGE (apply_prefix_ops initial_fmp lo ops ps).ps_spilled
Proof
  Induct >> simp[apply_prefix_ops_def, prefix_spill_wf_def] >>
  rpt gen_tac >> Cases_on `h` >> simp[] >> strip_tac >>
  first_x_assum irule >> simp[] >>
  `(apply_prefix_op initial_fmp lo (SOSpill n) ps).ps_spilled =
   ps.ps_spilled |+ (stack_peek 0 ps.ps_stack, n)` by
    simp[apply_prefix_op_def] >>
  pop_assum SUBST1_TAC >>
  irule fupdate_not_in_frange >> simp[]
QED

(* If off has unique pre-image k, and we FUPDATE (k', v) with v <> off,
   then off still has unique pre-image k *)
Theorem fupdate_preserves_unique_preimage[local]:
  !(f:'a |-> num) k off k' v.
    (!x. FLOOKUP f x = SOME off ==> x = k) /\
    v <> off ==>
    (!x. FLOOKUP (f |+ (k', v)) x = SOME off ==> x = k)
Proof
  rpt strip_tac >>
  qpat_x_assum `FLOOKUP (f |+ _) _ = _` mp_tac >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `k' = x` >> simp[]
QED

(* After a SOSpill sequence with all offsets <> off,
   off's unique-preimage property is preserved *)
Theorem spill_seq_preserves_unique_preimage[local]:
  !ops lo ps off k.
    EVERY (\op. ?off'. op = SOSpill off' /\ off' <> off) ops /\
    (!x. FLOOKUP ps.ps_spilled x = SOME off ==> x = k) ==>
    (!x. FLOOKUP (apply_prefix_ops initial_fmp lo ops ps).ps_spilled x = SOME off ==>
         x = k)
Proof
  Induct >> simp[apply_prefix_ops_def] >>
  rpt gen_tac >> Cases_on `h` >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then
    [`lo`, `apply_prefix_op initial_fmp lo (SOSpill n) ps`, `off`, `k`] mp_tac) >>
  simp[] >> disch_then match_mp_tac >>
  rpt strip_tac >>
  qpat_x_assum `FLOOKUP _ _ = SOME off` mp_tac >>
  simp[apply_prefix_op_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `stack_peek 0 ps.ps_stack = x` >> simp[]
QED

(* spill_seq_first_off_unique and do_dup_deep_not_spill_wf deleted:
   replaced by depth <= 15 precondition approach. *)

(* Helper: emit_one_input alignment from prefix_spill_wf.
   With depth <= 15 precondition, all do_dup calls have dist <= 15. *)
Theorem emit_one_input_ss_align_from_spill_wf[local]:
  !opc next_liveness op ps ops ps' lo.
    emit_one_input opc next_liveness op ps = (ops, ps') /\
    (!op1 off1 op2 off2.
       FLOOKUP ps.ps_spilled op1 = SOME off1 /\
       FLOOKUP ps.ps_spilled op2 = SOME off2 /\
       op1 <> op2 ==> off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
    prefix_spill_wf initial_fmp lo ops ps /\
    ~(?l. op = Label l /\ opc = INVOKE) /\
    (* Non-spilled Var operands on the stack have depth <= 15 *)
    (!s d. op = Var s /\ ~IS_SOME (FLOOKUP ps.ps_spilled (Var s)) /\
           stack_get_depth (Var s) ps.ps_stack = SOME d ==> d <= 15) ==>
    (apply_prefix_ops initial_fmp lo ops ps).ps_stack = ps'.ps_stack /\
    (apply_prefix_ops initial_fmp lo ops ps).ps_spilled = ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
  simp[emit_one_input_def, LET_THM] >>
  Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)`
  >- (
    (* Restore case *)
    simp[] >>
    Cases_on `do_restore op ps` >>
    rename1 `do_restore op ps = (restore_ops, ps1)` >> simp[] >>
    `(apply_prefix_ops initial_fmp lo restore_ops ps).ps_stack = ps1.ps_stack /\
     (apply_prefix_ops initial_fmp lo restore_ops ps).ps_spilled = ps1.ps_spilled` by
      (irule do_restore_ss_align >> metis_tac[]) >>
    Cases_on `op` >> fs[is_var_operand_def]
    >- (
      (* Var v after restore: op is at TOS, so dist = 0 *)
      (* Derive stack_get_depth from do_restore before case splitting *)
      `stack_get_depth (Var s) ps1.ps_stack = SOME 0` by (
        qpat_x_assum `do_restore _ _ = _` mp_tac >>
        simp[do_restore_def, LET_THM] >>
        Cases_on `FLOOKUP ps.ps_spilled (Var s)` >> simp[] >>
        strip_tac >> gvs[] >> simp[stack_get_depth_push]) >>
      Cases_on `MEM s next_liveness` >> simp[]
      >- (
        Cases_on `do_dup 0 ps1` >>
        rename1 `do_dup 0 ps1 = (dup_ops, ps2)` >>
        simp[] >> strip_tac >> gvs[] >>
        gvs[do_dup_def, stack_dup_def, stack_peek_def] >>
        simp[apply_prefix_ops_append] >>
        qmatch_goalsub_abbrev_tac `apply_prefix_ops initial_fmp lo _ ps_mid` >>
        simp[apply_prefix_ops_def, apply_prefix_op_def,
             apply_simple_op_def] >>
        `ps_mid.ps_stack = ps1.ps_stack` by simp[Abbr `ps_mid`] >>
        gvs[]
      )
      >> (strip_tac >> gvs[])
    )
  )
  >> (
    (* No-restore case *)
    simp[] >>
    Cases_on `op` >> fs[is_var_operand_def]
    >- ( (* Lit *)
      strip_tac >> gvs[apply_prefix_ops_def,
        apply_prefix_op_def, apply_simple_op_def, stack_push_def]
    )
    >- ( (* Var, not spilled *)
      Cases_on `MEM s next_liveness` >> simp[]
      >- (
        Cases_on `stack_get_depth (Var s) ps.ps_stack` >> simp[]
        >- simp[apply_prefix_ops_def]
        >- (
          rename1 `stack_get_depth _ _ = SOME dist` >>
          Cases_on `do_dup dist ps` >>
          rename1 `do_dup dist ps = (dup_ops, ps2)` >>
          simp[] >> strip_tac >> gvs[] >>
          (* From precondition: dist <= 15 *)
          `dist <= 15` by (first_x_assum irule >> simp[]) >>
          metis_tac[do_dup_align]
        )
      )
      >- simp[apply_prefix_ops_def]
    )
    >- ( (* Label *)
      Cases_on `opc = INVOKE`
      >- gvs[]
      >> (simp[] >> strip_tac >> gvs[apply_prefix_ops_def,
          apply_prefix_op_def, apply_simple_op_def, stack_push_def])
    )
  )
QED

(* After emit_one_input (non-INVOKE), the operand is accessible on the
   output plan stack, provided the accessibility precondition holds. *)
Theorem emit_one_input_on_stack[local]:
  !opc next_liveness op ps ops ps'.
    emit_one_input opc next_liveness op ps = (ops, ps') /\
    opc <> INVOKE /\
    (is_var_operand op ==>
       (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
       IS_SOME (FLOOKUP ps.ps_spilled op)) ==>
    ?d. stack_get_depth op ps'.ps_stack = SOME d /\ d <= 15
Proof
  rpt strip_tac >>
  qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
  simp[emit_one_input_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  Cases_on `op`
  >- ((* Lit *) simp[] >> strip_tac >> gvs[stack_get_depth_push])
  >- (suspend "var_case")
  >> (* Label *) simp[] >> strip_tac >> gvs[stack_get_depth_push]
QED

Resume emit_one_input_on_stack[var_case]:
  simp[is_var_operand_def] >>
  Cases_on `FLOOKUP ps.ps_spilled (Var s)` >>
  simp[do_restore_def] >>
  Cases_on `MEM s next_liveness` >> simp[]
  >- suspend "unspilled_live"
  >- suspend "unspilled_dead"
  >- suspend "spilled_live"
  >> suspend "spilled_dead"
QED

Resume emit_one_input_on_stack[unspilled_live]:
  `?d. stack_get_depth (Var s) ps.ps_stack = SOME d /\ d <= 15` by
    (gvs[is_var_operand_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  `ps' = SND (do_dup d ps)` by (Cases_on `do_dup d ps` >> gvs[]) >>
  gvs[] >> Q.EXISTS_TAC `0` >> simp[] >>
  match_mp_tac do_dup_shallow_depth >> simp[]
QED

Resume emit_one_input_on_stack[unspilled_dead]:
  strip_tac >> gvs[is_var_operand_def]
QED

Resume emit_one_input_on_stack[spilled_live]:
  simp[stack_get_depth_push] >> strip_tac >> gvs[] >>
  Q.EXISTS_TAC `0` >> simp[] >>
  match_mp_tac do_dup_shallow_depth >> simp[stack_get_depth_push]
QED

Resume emit_one_input_on_stack[spilled_dead]:
  strip_tac >> gvs[stack_get_depth_push]
QED

Finalise emit_one_input_on_stack;

(* hd_zero: cond_op value (0w) is at HD of asm stack after prefix.
   Uses emit_one_input alignment + reorder_single_op_val_on_tos_deep. *)
Resume gen_inst_abort_sim[hd_zero]:
  (* emit_input_plan for single operand = emit_one_input *)
  `emit_one_input ASSERT_UNREACHABLE next_liveness cond_op ps =
   (input_ops, ps1)` by (
    qpat_x_assum `emit_input_plan _ _ _ _ = _` mp_tac >>
    rewrite_tac[emit_input_plan_def, LET_THM] >>
    CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
    simp[]) >>
  (* prefix_spill_wf initial_fmp for input_ops *)
  `prefix_spill_wf initial_fmp label_offsets input_ops ps` by (
    match_mp_tac prefix_spill_wf_prefix >>
    Q.EXISTS_TAC `reorder_ops` >> first_assum ACCEPT_TAC) >>
  suspend "main"
QED

Resume gen_inst_abort_sim[main]:
  (* emit_one_input alignment *)
  `(apply_prefix_ops initial_fmp label_offsets input_ops ps).ps_stack = ps1.ps_stack /\
   (apply_prefix_ops initial_fmp label_offsets input_ops ps).ps_spilled = ps1.ps_spilled`
  by (
    match_mp_tac emit_one_input_ss_align_from_spill_wf >>
    Q.EXISTS_TAC `ASSERT_UNREACHABLE` >>
    Q.EXISTS_TAC `next_liveness` >>
    Q.EXISTS_TAC `cond_op` >>
    rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- simp[]
    >- (rpt strip_tac >> gvs[is_var_operand_def])) >>
  (* plan_stack_rel from venom_asm_rel *)
  `plan_stack_rel label_offsets vs
    (apply_prefix_ops initial_fmp label_offsets (input_ops ++ reorder_ops) ps).ps_stack
    st_mid.as_stack` by
    (qpat_x_assum `venom_asm_rel _ (apply_prefix_ops initial_fmp _ _ _) _ st_mid`
       mp_tac >> simp[venom_asm_rel_def]) >>
  (* connect to reorder via alignment *)
  `(apply_prefix_ops initial_fmp label_offsets (input_ops ++ reorder_ops) ps).ps_stack =
   (apply_prefix_ops initial_fmp label_offsets reorder_ops ps1).ps_stack` by (
    rewrite_tac[apply_prefix_ops_append] >>
    irule (cj 1 apply_prefix_ops_ext_stack_spilled) >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  (* depth bound via emit_one_input_on_stack *)
  qspecl_then [`ASSERT_UNREACHABLE`, `next_liveness`, `cond_op`, `ps`,
               `input_ops`, `ps1`] mp_tac emit_one_input_on_stack >>
  simp[] >> (impl_tac
  >- (strip_tac >>
      Cases_on `FLOOKUP ps.ps_spilled cond_op`
      >- (qpat_x_assum `is_var_operand cond_op ==> _` mp_tac >>
          simp[] >> strip_tac >>
          Q.EXISTS_TAC `d` >> simp[] >>
          first_x_assum match_mp_tac >> simp[])
      >> (disj2_tac >> simp[]))) >> strip_tac >>
  (* nonempty via reorder_one_wf_len + length chain *)
  `st_mid.as_stack <> []` by (
    `reorder_one dfg [cond_op] 0 cond_op ps1 = (reorder_ops, ps4)` by (
      qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
      simp[reorder_plan_def, combinTheory.o_DEF,
           indexedListsTheory.MAPi_def, LET_THM] >>
      pairarg_tac >> simp[]) >>
    `1 <= LENGTH ps4.ps_stack` by (
      qspecl_then [`dfg`, `[cond_op]`, `0`, `cond_op`, `ps1`,
        `label_offsets`] mp_tac (delet reorder_one_wf_len) >>
      simp[]) >>
    `LENGTH st_mid.as_stack = LENGTH ps4.ps_stack` by (
      qpat_x_assum `LENGTH st_mid.as_stack = _` mp_tac >>
      rewrite_tac[prefix_end_len_append] >>
      qspecl_then [`dfg`, `[cond_op]`, `ps1`, `label_offsets`]
        mp_tac (delet reorder_plan_wf_len) >>
      qspecl_then [`[cond_op]`, `ASSERT_UNREACHABLE`,
                   `next_liveness`, `ps`, `label_offsets`]
        mp_tac emit_input_plan_wf_len >>
      simp[]) >>
    Cases_on `st_mid.as_stack` >> fs[]) >>
  (* reorder puts cond_op value at TOS *)
  `operand_val vs label_offsets cond_op = SOME (HD st_mid.as_stack)` by (
    match_mp_tac reorder_single_op_val_on_tos >>
    Q.EXISTS_TAC `dfg` >> Q.EXISTS_TAC `ps1` >>
    Q.EXISTS_TAC `reorder_ops` >> Q.EXISTS_TAC `ps4` >>
    rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- (Q.EXISTS_TAC `d` >> simp[])
    >- gs[]
    >- first_assum ACCEPT_TAC
    >> (rpt strip_tac >>
        qpat_x_assum `!op2. operand_equiv _ _ _ ==> _` drule >> simp[])) >>
  (* conclude *)
  gvs[]
QED

(* as_stack_decompose: nonempty + HD = 0w implies list decomposition.
   Depends on plan_stack_rel nonempty from the applied plan state. *)
Resume gen_inst_abort_sim[as_stack_decompose]:
  (* prefix_end_len chain: input part *)
  `prefix_end_len label_offsets (LENGTH ps.ps_stack) input_ops =
   LENGTH ps1.ps_stack` by (
    qspecl_then [`[cond_op]`, `ASSERT_UNREACHABLE`,
                 `next_liveness`, `ps`, `label_offsets`]
      mp_tac emit_input_plan_wf_len >>
    simp[]) >>
  (* prefix_end_len chain: reorder part *)
  `prefix_end_len label_offsets (LENGTH ps1.ps_stack) reorder_ops =
   LENGTH ps4.ps_stack` by (
    qspecl_then [`dfg`, `[cond_op]`, `ps1`, `label_offsets`]
      mp_tac (delet reorder_plan_wf_len) >>
    simp[]) >>
  (* 1 <= LENGTH ps4.ps_stack via reorder_one_wf_len *)
  `1 <= LENGTH ps4.ps_stack` by (
    `reorder_one dfg [cond_op] 0 cond_op ps1 = (reorder_ops, ps4)` by (
      qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
      simp[reorder_plan_def, combinTheory.o_DEF,
           indexedListsTheory.MAPi_def, LET_THM] >>
      pairarg_tac >> simp[]) >>
    qspecl_then [`dfg`, `[cond_op]`, `0`, `cond_op`, `ps1`,
      `label_offsets`]
      mp_tac (delet reorder_one_wf_len) >>
    simp[]) >>
  (* Chain: LENGTH st_mid.as_stack = LENGTH ps4.ps_stack *)
  `LENGTH st_mid.as_stack = LENGTH ps4.ps_stack` by
    fs[prefix_end_len_append] >>
  (* Conclude *)
  Cases_on `st_mid.as_stack` >> fs[]
QED

Finalise gen_inst_abort_sim;

(* clean_ops_sim moved to cleanOpsSimScript.sml
   (planAlign ancestor breaks prefix_exec_terminal in this file) *)

(* ===== Per-instruction OK simulation helpers ===== *)

(* NOP: state unchanged, 0 asm steps *)
Theorem gen_inst_sim_nop:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps'.
    inst.inst_opcode = NOP /\
    venom_asm_rel lo ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      vs' = vs /\ ops = [] /\ ps' = ps /\
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as'
Proof
  rpt strip_tac >>
  (* NOP: generate_inst_plan gives ([], ps) *)
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def] >> strip_tac >> gvs[] >>
  (* step_inst NOP = OK vs *)
  imp_res_tac step_inst_nop_ok >> gvs[] >>
  qexistsl_tac [`0`, `as`] >> simp[asm_steps_def]
QED

(* PARAM: only vs_vars changes, plan stack/spill unchanged.
   Requires that the output variable is fresh w.r.t. the plan state. *)
Theorem gen_inst_sim_param:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps'.
    inst.inst_opcode = PARAM /\
    venom_asm_rel lo ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    (* Fresh output: not on plan stack or in spilled *)
    (!out. MEM out inst.inst_outputs ==>
           ~MEM (Var out) ps.ps_stack /\
           Var out NOTIN FDOM ps.ps_spilled) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          step_mem_safe ps.ps_alloc vs vs' ==>
      ops = [] /\ ps' = ps /\
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as'
Proof
  rpt gen_tac >> strip_tac >>
  (* generate_inst_plan for PARAM gives ([], ps) *)
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_param_opcode_def] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  qexistsl [`0`, `as`] >> simp[asm_steps_def] >>
  (* step_inst for PARAM: vs' = update_var out val vs *)
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_def, step_inst_base_def] >>
  TRY CASE_TAC >> simp[] >>
  TRY CASE_TAC >> simp[] >>
  TRY CASE_TAC >> simp[] >>
  TRY CASE_TAC >> simp[] >>
  TRY CASE_TAC >> simp[] >>
  TRY CASE_TAC >> simp[] >>
  strip_tac >> gvs[] >>
  (* venom_asm_rel preserved: out is fresh *)
  irule venom_asm_rel_update_var >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `op` >> simp[] >>
      CCONTR_TAC >> gvs[])
  >- (irule MONO_EVERY >>
      Q.EXISTS_TAC `\op. op <> Var h` >>
      conj_tac >- (Cases >> simp[]) >>
      fs[EVERY_MEM] >> metis_tac[])
QED


(* ===== Operand count bound ===== *)

(* For SOME-name non-INVOKE opcodes, compute_operands = inst.inst_operands
   (because JMP/DJMP/JNZ/INVOKE/LOG all have venom_to_evm_name = NONE). *)
Theorem compute_operands_eq_operands[local]:
  !inst name.
    venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_opcode <> INVOKE ==>
    compute_operands inst = inst.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  simp[compute_operands_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[venom_to_evm_name_def]
QED

(* ===== SSA freshness propagation through prefix ops ===== *)

(* A single prefix op cannot introduce a Var y into the plan stack
   if Var y was not already there or in spilled.
   Needs:
   - spill_op_wf for SORestore (Hilbert choice picks from FDOM)
   - stack_op_wf for SODup/SOSwap (index validity) *)
Theorem apply_prefix_op_preserves_not_mem[local]:
  !lo op ps y.
    is_prefix_op op /\
    spill_op_wf ps op /\
    FST (stack_op_wf lo op (LENGTH ps.ps_stack)) /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) (apply_prefix_op initial_fmp lo op ps).ps_stack /\
    Var y NOTIN FDOM (apply_prefix_op initial_fmp lo op ps).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >>
  gvs[is_prefix_op_def, apply_prefix_op_def, stack_op_wf_def,
      apply_simple_op_def, stack_push_def, stack_pop_def,
      stack_swap_def, spill_op_wf_def, spill_lookup_def, LET_THM,
      listTheory.MEM_SNOC, stack_peek_def] >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (Cases_on `o'` >>
       gvs[apply_simple_op_def, stack_push_def, listTheory.MEM_SNOC] >>
       NO_TAC) >>
  TRY (imp_res_tac rich_listTheory.MEM_TAKE >> gvs[] >> NO_TAC) >>
  (* SOSwap: extract from LUPDATE *)
  TRY (imp_res_tac listTheory.MEM_LUPDATE_E >> gvs[] >>
       imp_res_tac listTheory.MEM_LUPDATE_E >> gvs[]) >>
  (* SORestore: SELECT gives FDOM membership *)
  TRY (`FLOOKUP ps.ps_spilled (@op. FLOOKUP ps.ps_spilled op = SOME n)
        = SOME n` by (SELECT_ELIM_TAC >> metis_tac[]) >>
       fs[finite_mapTheory.FLOOKUP_DEF]) >>
  (* All remaining: ~MEM (EL k l) l with k < LENGTH l.
     Derive MEM from EL_MEM, then contradiction with ~MEM. *)
  qpat_x_assum `~MEM _ _` mp_tac >> simp[] >>
  irule listTheory.EL_MEM >> simp[]
QED

(* LENGTH invariant for apply_prefix_op initial_fmp *)
Theorem apply_prefix_op_stack_length[local]:
  !lo op ps.
    is_prefix_op op ==>
    LENGTH (apply_prefix_op initial_fmp lo op ps).ps_stack =
      SND (stack_op_wf lo op (LENGTH ps.ps_stack))
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[is_prefix_op_def, apply_prefix_op_def, stack_op_wf_def,
      apply_simple_op_def, stack_push_def, stack_pop_def,
      stack_swap_def, spill_lookup_def, LET_THM] >>
  Cases_on `o'` >> gvs[apply_simple_op_def, stack_push_def, stack_op_wf_def]
QED

(* Extension to a list of prefix ops.
   prefix_wf ensures stack_op_wf for each step;
   prefix_spill_wf initial_fmp ensures spill_op_wf for each step. *)
Theorem apply_prefix_ops_preserves_not_mem[local]:
  !ops lo ps y.
    EVERY is_prefix_op ops /\
    prefix_wf lo (LENGTH ps.ps_stack) ops /\
    prefix_spill_wf initial_fmp lo ops ps /\
    ~MEM (Var y) ps.ps_stack /\
    Var y NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var y) (apply_prefix_ops initial_fmp lo ops ps).ps_stack /\
    Var y NOTIN FDOM (apply_prefix_ops initial_fmp lo ops ps).ps_spilled
Proof
  Induct >>
  simp[apply_prefix_ops_def, prefix_spill_wf_def, prefix_wf_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then
    [`lo`, `apply_prefix_op initial_fmp lo h ps`, `y`] mp_tac) >>
  simp[apply_prefix_op_stack_length] >>
  disch_then match_mp_tac >>
  qspecl_then [`lo`, `h`, `ps`, `y`] mp_tac
    apply_prefix_op_preserves_not_mem >>
  gvs[]
QED

(* Releasing dead spills (freeing spill slots for variables not in the live
   set) preserves the venom-assembly state correspondence. The dead-spill
   release only modifies the plan state's spill map and allocator; the
   stack and memory layout visible to the assembly are unchanged. *)
Theorem venom_asm_rel_release_dead_spills:
  !lo next_liveness ps vs as.
    venom_asm_rel lo ps vs as ==>
    venom_asm_rel lo (release_dead_spills next_liveness ps) vs as
Proof
  rpt gen_tac >> strip_tac >> gvs[venom_asm_rel_def] >>
  `!dead (ps0:plan_state).
     (FOLDL (\ps' (op:operand, off:num).
       ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc |>)
       ps0 dead).ps_stack = ps0.ps_stack` by (
    Induct >> simp[] >>
    rpt gen_tac >> PairCases_on `h` >> simp[free_spill_slot_def]) >>
  `!dead (ps0:plan_state) lo' vs' am.
     plan_spill_rel lo' vs' ps0.ps_spilled am ==>
     plan_spill_rel lo' vs'
       (FOLDL (\ps' (op:operand, off:num).
         ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                     ps_alloc := free_spill_slot off ps'.ps_alloc |>)
         ps0 dead).ps_spilled am` by (
    Induct >> simp[] >>
    rpt strip_tac >> Cases_on `h` >> simp[] >>
    first_x_assum match_mp_tac >>
    simp[] >> irule plan_spill_rel_remove_entry >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[release_dead_spills_def, LET_THM] >>
  conj_tac >- (simp[release_dead_spills_def, LET_THM] >> first_x_assum match_mp_tac >> simp[]) >>
  simp[memory_rel_def, release_dead_spills_spill_base, release_dead_spills_next_offset] >> metis_tac[memory_rel_def]
QED

(* Canonical high-water witness: package the exact pre-state and prefix
   hypotheses used by the generated-state preservation boundary. *)
Theorem do_swap_headroom_generated_premises[local]:
  generated_plan_state_wf 0 headroom_ps /\
  prefix_spill_wf initial_fmp FEMPTY
    (FST (do_swap 17 headroom_ps)) headroom_ps
Proof
  mp_tac do_swap_headroom_witness_facts >> strip_tac >>
  `plan_slots_bounded 0 headroom_ps` by
    (fs[doSwapSimTheory.spill_alloc_wf_def] >>
     simp[plan_slots_bounded_def, alloc_slots_bounded_def,
          headroom_ps_def, headroom_alloc_def, init_plan_state_def] >>
     simp[EVERY_MEM] >> gen_tac >> strip_tac >>
     qpat_x_assum `!off. MEM off headroom_ps.ps_alloc.sa_free_slots ==> _`
       (qspec_then `off` mp_tac) >>
     simp[headroom_ps_def, headroom_alloc_def]) >>
  drule doSwapSimTheory.spill_alloc_wf_layout >>
  disch_then assume_tac >>
  conj_tac
  >- (simp[generated_plan_state_wf_def] >>
      ASM_REWRITE_TAC[] >>
      simp[headroom_ps_def, headroom_stack_def, init_plan_state_def]) >>
  first_assum ACCEPT_TAC
QED

(* The canonical prefix remains layout-safe at allocator saturation, even
   though the strict readiness predicate correctly fails in the post-state. *)
Theorem do_swap_headroom_layout_boundary[local]:
  generated_plan_state_wf 0 headroom_ps /\
  prefix_spill_wf initial_fmp FEMPTY
    (FST (do_swap 17 headroom_ps)) headroom_ps /\
  generated_plan_state_wf 0 (SND (do_swap 17 headroom_ps)) /\
  ~doSwapSim$spill_alloc_wf
    (SND (do_swap 17 headroom_ps)).ps_alloc
    (SND (do_swap 17 headroom_ps)).ps_spilled
Proof
  mp_tac do_swap_headroom_generated_premises >> strip_tac >>
  mp_tac doSwapSimTheory.do_swap_headroom_post_layout >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  conj_tac
  >- first_assum ACCEPT_TAC >>
  conj_tac
  >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (fs[generated_plan_state_wf_def, plan_slots_bounded_def,
          alloc_slots_bounded_def,
          doSwapSimTheory.spill_alloc_layout_wf_def] >>
      simp[EVERY_MEM]) >>
  first_assum ACCEPT_TAC
QED

(* Checked interface probe for bounded generated spill prefixes: the bounded
   invariant permits an active spill offset to remain in sa_free_slots.  After
   overwriting that operand's map entry, a later spill may reuse the old slot. *)
Theorem bounded_prefix_old_spill_overlap_probe[local]:
  128 < dimword(:256) ==>
  let ps = (init_plan_state 0) with <|
        ps_stack := [Lit (2w:bytes32); Lit (1w:bytes32)];
        ps_spilled := FEMPTY |+ (Lit (1w:bytes32),64);
        ps_alloc := <| sa_free_slots := [64;128];
                       sa_next_offset := 160; sa_spill_base := 0 |> |>;
      ps1 = apply_prefix_op 0 FEMPTY (SOSpill 128) ps;
      ps2 = apply_prefix_op 0 FEMPTY (SOSpill 64) ps1
  in plan_slots_bounded 0 ps /\
     prefix_spill_wf 0 FEMPTY [SOSpill 128; SOSpill 64] ps /\
     FLOOKUP ps1.ps_spilled (Lit (1w:bytes32)) = SOME 128 /\
     FLOOKUP ps2.ps_spilled (Lit (2w:bytes32)) = SOME 64 /\
     ~generated_plan_state_wf 0 ps
Proof
  rpt strip_tac >> EVAL_TAC >>
  fs[generated_plan_state_wf_def, doSwapSimTheory.spill_alloc_layout_wf_def]
QED

Theorem step_inst_non_invoke_preserves_initial_fmp:
  !fuel ctx inst s s'.
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_initial_fmp = s.vs_initial_fmp
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_preserves_all >> simp[]
QED

(* Comprehensive per-instruction OK simulation.
   Stronger than venomToAsmProps.gen_inst_simulation:
   - requires inst_wf, operand bound, label resolution, prefix_spill_wf
   - provides PC tracking (as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops))
   These extra preconditions are derivable at block level from
   codegen_ready_fn + MEM inst bb.bb_instructions. *)
Theorem gen_inst_ok_sim:
  !fuel ctx lo o2pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label base ps vs as ops ps'.
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val vs lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op vs) /\
    (* Spill well-formedness for prefix ops.
       Dischargeable: provable from generate_inst_plan output
       (plan generator produces spill-well-formed prefixes). *)
    prefix_spill_wf initial_fmp lo (FRONT ops) ps /\
    venom_asm_rel lo ps vs as /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          step_mem_safe ps.ps_alloc vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt strip_tac >>
  `plan_slots_bounded base' ps` by fs[generated_plan_state_wf_def] >>
  (* Dispatch on generate_inst_plan cases *)
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_inst_plan_def, is_param_opcode_def] >>
  strip_tac >>
  (* is_pre_codegen eliminated by SOME <> NONE *)
  (* Now case split on opcode *)
  Cases_on `inst.inst_opcode = PHI` >- (gvs[] >> suspend "phi") >>
  Cases_on `inst.inst_opcode = OFFSET` >- (gvs[] >> suspend "offset") >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "param") >>
  Cases_on `inst.inst_opcode = FMP_PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "fmp_param") >>
  Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (gvs[is_param_opcode_def] >> suspend "retpc_param") >>
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- (gvs[is_param_opcode_def] >> suspend "initial_fmp") >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (gvs[is_param_opcode_def] >> suspend "bump") >>
  `~is_param_opcode inst.inst_opcode` by simp[is_param_opcode_iff] >>
  gvs[] >>
  Cases_on `inst.inst_opcode = NOP`
  >- (
    gvs[] >> imp_res_tac step_inst_nop_ok >> gvs[] >>
    qexistsl_tac [`0`, `as`] >> simp[asm_steps_def, execute_plan_def]
  ) >>
  (* Regular instruction: dispatch by opcode family *)
  Cases_on `inst.inst_opcode = INVOKE` >- (gvs[] >> suspend "invoke") >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >- (
    (* NONE case: ASSIGN, ISTORE, JMP, JNZ, DJMP, LOG, ASSERT, etc. *)
    gvs[] >> suspend "none"
  ) >>
  rename1 `venom_to_evm_name _ = SOME name` >>
  (* SOME name case: 3-phase plan (prefix + emit + postfix) *)
  gvs[] >>
  suspend "some_name"
QED

Resume gen_inst_ok_sim[phi]:
  (* Extract vs' from step_inst PHI = OK vs' *)
  `?out prev val_op v.
     inst.inst_outputs = [out] /\
     vs.vs_prev_bb = SOME prev /\
     resolve_phi prev inst.inst_operands = SOME val_op /\
     eval_operand val_op vs = SOME v /\
     vs' = update_var out v vs` by (
    qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
    simp[Once step_inst_def] >>
    `inst.inst_opcode <> INVOKE` by simp[] >> simp[] >>
    simp[step_inst_base_def] >>
    `?h. inst.inst_outputs = [h]` by (
      qpat_x_assum `inst_wf _` mp_tac >>
      simp[inst_wf_def] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      Cases_on `t` >> simp[]) >>
    simp[] >>
    Cases_on `vs.vs_prev_bb` >> simp[] >>
    Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
    Cases_on `eval_operand x' vs` >> simp[] >>
    strip_tac >> gvs[] >>
    metis_tac[]) >>
  gvs[] >>
  (* Unfold generate_phi_plan and case split *)
  qpat_x_assum `generate_phi_plan _ _ _ = _` mp_tac >>
  simp[generate_phi_plan_def, LET_THM] >>
  suspend "phi_cases"
QED

Resume gen_inst_ok_sim[phi_cases]:
  strip_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
              ps.ps_stack`
  >- (
    (* NONE case: ops = [], ps' = ps *)
    gvs[] >>
    Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `as` >>
    simp[asm_steps_def, execute_plan_def] >>
    irule venom_asm_rel_update_var >>
    gvs[EVERY_MEM] >>
    rpt strip_tac >> res_tac >> gvs[]
  )
  >- (
    (* SOME dist case: stack has a phi var at depth x *)
    gvs[] >> pairarg_tac >> gvs[] >>
    (* Case split on whether the phi var is still live *)
    qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
    IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
    >- suspend "phi_live"
    >- (
      (* Dead case: poke only, 0 asm steps *)
      simp[execute_plan_def, exec_stack_op_def] >>
      Q.EXISTS_TAC `0` >> Q.EXISTS_TAC `as` >>
      simp[asm_steps_def] >>
      irule venom_asm_rel_poke_update_var >> simp[] >>
      (* dist < LENGTH ps.ps_stack from stack_get_phi_depth *)
      qpat_x_assum `stack_get_phi_depth _ _ = SOME _` mp_tac >>
      simp[stack_get_phi_depth_def] >>
      strip_tac >> drule stack_find_bound >> simp[]
    )
  )
QED

Resume gen_inst_ok_sim[phi_live]:
  (* derive x < LENGTH ps.ps_stack from stack_get_phi_depth *)
  qpat_x_assum `stack_get_phi_depth _ _ = SOME _`
    (fn th => assume_tac th >>
              mp_tac (REWRITE_RULE [stack_get_phi_depth_def] th)) >>
  strip_tac >>
  drule stack_find_bound >> rewrite_tac[LENGTH_REVERSE] >> strip_tac >>
  (* derive prefix_wf via do_dup_wf_len *)
  qspecl_then [`x`, `ps`, `lo`] mp_tac do_dup_wf_len >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[LET_THM] >> strip_tac >>
  (* simplify execute_plan initial_fmp suffix and FRONT *)
  rewrite_tac[execute_plan_append,
    EVAL ``execute_plan initial_fmp [SOPoke 0 (Var out)]``, APPEND_NIL] >>
  rewrite_tac[FRONT_APPEND_NOT_NIL, EVAL ``[SOPoke 0 (Var out)] <> []``] >>
  rewrite_tac[FRONT_DEF] >>
  suspend "phi_live_main"
QED

Resume gen_inst_ok_sim[phi_live_main]:
  (* Use prefix_sim with prefix=dup_ops, emit=[SOPoke 0 (Var out)] *)
  qpat_x_assum `prefix_wf lo _ dup_ops`
    (fn th => assume_tac th >>
              assume_tac (MATCH_MP prefix_wf_every_prefix_op th)) >>
  qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
    `dup_ops`, `[SOPoke 0 (Var out)]`] mp_tac prefix_sim >>
  (impl_tac >- (ASM_REWRITE_TAC[] >> EVAL_TAC)) >>
  strip_tac >>
  suspend "phi_live_align"
QED

Resume gen_inst_ok_sim[phi_live_align]:
  Q.EXISTS_TAC `LENGTH (execute_plan initial_fmp dup_ops)` >>
  Q.EXISTS_TAC `st_mid` >>
  ASM_REWRITE_TAC[] >>
  suspend "phi_live_do_dup_align"
QED

(* Helper: do_dup (shallow) + poke 0 preserves venom_asm_rel *)
Theorem do_dup_poke_venom_asm_rel[local]:
  !lo ps vs (as:asm_state) x out v dup_ops ps''.
    venom_asm_rel lo (apply_prefix_ops initial_fmp lo dup_ops ps) vs as /\
    do_dup x ps = (dup_ops, ps'') /\
    x <= 15 /\
    x < LENGTH ps.ps_stack /\
    operand_val vs lo (stack_peek x ps.ps_stack) = SOME v /\
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
      case op of Var x => x <> out | _ => T)
    ==>
    venom_asm_rel lo
      (ps'' with ps_stack := stack_poke 0 (Var out) ps''.ps_stack)
      (update_var out v vs) as
Proof
  rpt strip_tac >>
  (* unfold do_dup for shallow case *)
  qpat_x_assum `do_dup _ _ = _` mp_tac >>
  simp[do_dup_def] >> strip_tac >> gvs[] >>
  (* alignment gives apply_prefix_ops initial_fmp = record update *)
  qspecl_then [`x'`, `ps`, `[SODup (x' + 1)]`,
    `ps with ps_stack := stack_dup x' ps.ps_stack`]
    mp_tac do_dup_align >>
  simp[do_dup_def] >> strip_tac >>
  (* Rewrite venom_asm_rel to eliminate apply_prefix_ops initial_fmp *)
  fs[] >>
  (* apply venom_asm_rel_poke_update_var via forward reasoning *)
  qspecl_then [`lo`,
    `ps with ps_stack := stack_dup x' ps.ps_stack`,
    `vs`, `as`, `out`, `v`, `0`]
    mp_tac venom_asm_rel_poke_update_var >>
  (* Collapse nested record update in conclusion *)
  simp[stack_dup_def, LENGTH_SNOC,
       stack_peek_def, EL_LENGTH_SNOC, EVERY_SNOC] >>
  disch_then match_mp_tac >>
  `LENGTH ps.ps_stack - (x' + 1) = LENGTH ps.ps_stack - 1 - x'`
    by decide_tac >>
  pop_assum (fn eq => rewrite_tac[eq]) >>
  rewrite_tac[GSYM stack_peek_def] >>
  conj_tac >- ASM_REWRITE_TAC[] >>
  `MEM (stack_peek x' ps.ps_stack) ps.ps_stack` by (
    rewrite_tac[stack_peek_def] >> match_mp_tac EL_MEM >>
    decide_tac) >>
  qpat_x_assum `EVERY _ ps.ps_stack` mp_tac >>
  simp[EVERY_MEM]
QED

Resume gen_inst_ok_sim[phi_live_do_dup_align]:
  (* PC arithmetic (second conjunct) *)
  conj_asm1_tac >> TRY decide_tac >>
  (* Case split x <= 15 *)
  Cases_on `x <= 15`
  >- (
    qspecl_then [`lo`, `ps`, `vs`, `st_mid`, `x`, `out`, `v`,
      `dup_ops`, `ps''`] mp_tac do_dup_poke_venom_asm_rel >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    rewrite_tac[])
  >- (
    (* Deep case: x > 15, needs do_dup_align_gen *)
    cheat)
QED

Resume gen_inst_ok_sim[offset]:
  cheat
QED

Resume gen_inst_ok_sim[param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[step_inst_base_def, compute_operands_def, eval_operand_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED

Resume gen_inst_ok_sim[fmp_param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  gvs[step_inst_base_def, compute_operands_def, eval_operand_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED

Resume gen_inst_ok_sim[retpc_param]:
  qexistsl [`0`, `as`] >> simp[asm_steps_def, execute_plan_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >> gvs[] >>
  gvs[step_inst_base_def, compute_operands_def, eval_operand_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  rpt conj_tac
  >- (irule plan_stack_rel_update_var >> fs[venom_asm_rel_def])
  >- (irule plan_spill_rel_update_var >> fs[venom_asm_rel_def])
  >> fs[venom_asm_rel_def, update_var_def]
QED


(* Consumer-shaped simulation boundary for optimistic_swap_plan. *)
Theorem optimistic_swap_plan_postfix_sim[local]:
  !base dfg inst next_liveness next_is_term ps ops ps'
   initial_fmp lo o2pc prog vs st.
    generated_plan_state_wf base ps /\
    optimistic_swap_plan dfg inst next_liveness next_is_term ps = (ops,ps') /\
    prefix_spill_wf initial_fmp lo (FRONT ops) ps /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      generated_plan_state_wf base ps'
Proof
  rpt strip_tac >>
  qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  TRY (strip_tac >> gvs[] >> qexists `st` >>
       simp[execute_plan_def, asm_steps_def] >> NO_TAC) >>
  CASE_TAC >> simp[] >> strip_tac >> gvs[]
  >- (qexists `st` >> simp[execute_plan_def, asm_steps_def]) >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_bound] >>
  `prefix_spill_wf initial_fmp lo ops ps` by
    (fs[generated_plan_state_wf_def] >>
     metis_tac[doSwapSimTheory.do_swap_prefix_spill_wf_from_front]) >>
  `generated_plan_state_wf base' ps'` by
    (qspecl_then [`base'`, `x`, `ps`, `lo`] mp_tac
       do_swap_generated_plan_state_wf >>
     ASM_REWRITE_TAC[]) >>
  qspecl_then [`x`, `ps`, `ops`, `ps'`, `lo`, `o2pc`, `prog`, `vs`, `st`]
    mp_tac doSwapSimTheory.do_swap_venom_asm_rel_layout >>
  impl_tac
  >- (fs[generated_plan_state_wf_def] >> ASM_REWRITE_TAC[]) >>
  strip_tac >> qexists_tac `st'` >> ASM_REWRITE_TAC[] >> decide_tac
QED

Theorem generated_do_swap_initial_fmp_front_transport[local]:
  !base dist source target ops target' initial_fmp lo.
    generated_plan_state_wf base target /\
    do_swap dist target = (ops,target') /\
    dist < LENGTH target.ps_stack /\
    prefix_spill_wf initial_fmp lo (FRONT (SOInitialFmp :: ops)) source ==>
    prefix_spill_wf initial_fmp lo ops target
Proof
  rpt strip_tac >>
  fs[generated_plan_state_wf_def] >>
  metis_tac[doSwapSimTheory.do_swap_initial_fmp_front_transport]
QED
Theorem initial_fmp_dead_popmany[local]:
  !out ps.
    popmany_plan [Var out]
      (ps with ps_stack := SNOC (Var out) ps.ps_stack) =
    ([SOPop 1], ps)
Proof
  rpt gen_tac >>
  `stack_get_depth (Var out) (SNOC (Var out) ps.ps_stack) = SOME 0` by
    simp[GSYM stack_push_def, stack_get_depth_push] >>
  simp[popmany_plan_def, is_contiguous_top_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF, popmany_individual_def, stack_pop_def,
       FOLDL, LENGTH_SNOC] >>
  Cases_on `ps` >> simp[SNOC_APPEND, TAKE_APPEND1,
                        plan_state_component_equality]
QED

Theorem initial_fmp_generated_postfix_sim[local]:
  !lo o2pc prog initial_fmp next_liveness tail ps_emit ps9 ps' vs as.
    prefix_wf lo (LENGTH ps_emit.ps_stack) tail /\
    prefix_spill_wf initial_fmp lo tail ps_emit /\
    EVERY is_prefix_op tail /\
    apply_prefix_ops initial_fmp lo tail ps_emit = ps9 /\
    ps' = release_dead_spills next_liveness ps9 /\
    venom_asm_rel lo ps_emit vs as /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp tail) ==>
    ?as'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp tail)) as =
        AsmOK as' /\
      venom_asm_rel lo ps' vs as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp tail)
Proof
  rpt strip_tac >>
  qspecl_then [`tail`, `initial_fmp`, `lo`, `o2pc`, `prog`,
    `ps_emit`, `vs`, `as`] mp_tac mixed_prefix_venom_asm_rel >>
  (impl_tac >- ASM_REWRITE_TAC[]) >>
  strip_tac >>
  `venom_asm_rel lo ps9 vs st'` by gvs[] >>
  qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  irule venom_asm_rel_release_dead_spills >> ASM_REWRITE_TAC[]
QED

Theorem initial_fmp_emit_update_var_bridge[local]:
  !lo o2pc prog ps vs as initial_fmp out.
    venom_asm_rel lo ps vs as /\
    ~MEM (Var out) ps.ps_stack /\
    Var out NOTIN FDOM ps.ps_spilled /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp [SOInitialFmp]) ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack := SNOC (Var out) ps.ps_stack)
        (update_var out vs.vs_initial_fmp vs) as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt strip_tac >>
  qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`, `initial_fmp`]
    mp_tac initial_fmp_push_venom_asm_rel >>
  (impl_tac >-
    (qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
     simp[execute_plan_def, exec_stack_op_def])) >>
  strip_tac >> qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  gvs[venom_asm_rel_def, update_var_def] >>
  conj_tac
  >- (`plan_stack_rel lo (update_var out vs.vs_initial_fmp vs)
          (SNOC (Lit vs.vs_initial_fmp) ps.ps_stack) st'.as_stack` by
        (irule plan_stack_rel_update_var >>
         simp[EVERY_MEM] >> rpt strip_tac >>
         Cases_on `op` >> gvs[] >> metis_tac[]) >>
      qpat_x_assum `plan_stack_rel lo (update_var out vs.vs_initial_fmp vs)
          (SNOC (Lit vs.vs_initial_fmp) ps.ps_stack) st'.as_stack` mp_tac >>
      simp[update_var_def, plan_stack_rel_def, LENGTH_SNOC] >> strip_tac >>
      rw[plan_stack_rel_def, LENGTH_SNOC] >>
      first_x_assum (qspec_then `i` mp_tac) >>
      Cases_on `i` >>
      simp[REVERSE_SNOC, operand_val_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE])
  >- (`plan_spill_rel lo (update_var out vs.vs_initial_fmp vs)
          ps.ps_spilled st'.as_memory` by
        (irule plan_spill_rel_update_var >>
         simp[] >> rpt strip_tac >> Cases_on `op` >> gvs[] >>
         metis_tac[]) >>
      gvs[update_var_def])
QED

Resume gen_inst_ok_sim[initial_fmp]:
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       is_commutative_def, generate_emit_ops_def] >>
  `?out. inst.inst_outputs = [out]` by (
    Cases_on `inst.inst_outputs` >> fs[] >> Cases_on `t` >> fs[]) >>
  gvs[] >> rpt strip_tac >>
  `~MEM (Var out) ps.ps_stack` by (
    qpat_x_assum `EVERY _ ps.ps_stack`
      (fn th => assume_tac (REWRITE_RULE [EVERY_MEM] th)) >>
    strip_tac >>
    qpat_x_assum `!op. MEM op ps.ps_stack ==> _`
      (qspec_then `Var out` mp_tac) >>
    simp[]) >>
  `Var out NOTIN FDOM ps.ps_spilled` by (
    strip_tac >> qpat_x_assum `!op. op IN FDOM _ ==> _`
      (qspec_then `Var out` mp_tac) >> simp[]) >>
  Cases_on `is_halting`
  >- (reverse (Cases_on `MEM out next_liveness`)
      >- (gvs[initial_fmp_dead_popmany] >>
          qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
            `initial_fmp`, `out`] mp_tac initial_fmp_emit_update_var_bridge >>
          (impl_tac >- ASM_REWRITE_TAC[]) >> strip_tac >>
          qexistsl [`1`, `as'`] >> ASM_REWRITE_TAC[] >>
          conj_tac
          >- (irule venom_asm_rel_release_dead_spills >>
              simp[stack_push_def, stack_pop_def]) >>
          simp[execute_plan_def, exec_stack_op_def]) >>
      gvs[initial_fmp_dead_popmany] >>
      pairarg_tac >> gvs[] >>
      `generated_plan_state_wf base'
         (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))` by
        (simp[stack_pop_def] >> irule generated_plan_state_wf_push >>
         ASM_REWRITE_TAC[]) >>
      qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
        `initial_fmp`, `out`] mp_tac initial_fmp_emit_update_var_bridge >>
      (impl_tac >-
        (ASM_REWRITE_TAC[] >>
         qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
         simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons])) >>
      strip_tac >>
      `prefix_spill_wf initial_fmp lo (FRONT opt_ops)
         (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))` by
        (Cases_on `opt_ops`
         >- simp[prefix_spill_wf_def] >>
         qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
         simp[optimistic_swap_plan_def] >>
         rpt (IF_CASES_TAC >> gvs[]) >>
         CASE_TAC >> gvs[] >> strip_tac >>
         `x < LENGTH
            (stack_push (Var out) (stack_pop 0 ps.ps_stack))` by
           metis_tac[stack_get_depth_bound] >>
         `prefix_spill_wf initial_fmp lo (h::t)
            (ps with ps_stack :=
               stack_push (Var out) (stack_pop 0 ps.ps_stack))` by
           (irule generated_do_swap_initial_fmp_front_transport >>
            simp[SF SFY_ss] >>
            qexistsl [`x`, `ps9`] >> ASM_REWRITE_TAC[] >>
            qpat_x_assum `x < LENGTH (stack_push _ _)` mp_tac >>
            simp[stack_push_def, stack_pop_def]) >>
         `h::t = FRONT (h::t) ++ [LAST (h::t)]` by
           simp[APPEND_FRONT_LAST] >>
         metis_tac[prefix_spill_wf_prefix]) >>
      `venom_asm_rel lo
         (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))
         (update_var out vs.vs_initial_fmp vs) as'` by
        (qpat_x_assum `venom_asm_rel lo (ps with ps_stack := SNOC _ _) _ _`
           mp_tac >> simp[stack_push_def, stack_pop_def]) >>
      `asm_block_at prog as'.as_pc (execute_plan initial_fmp opt_ops)` by
        (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
         simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
         ASM_REWRITE_TAC[]) >>
      drule optimistic_swap_plan_postfix_sim >>
      disch_then drule >> disch_then drule >> disch_then drule >>
      disch_then drule >> strip_tac >>
      first_x_assum (qspec_then `o2pc` strip_assume_tac) >>
      `venom_asm_rel lo (release_dead_spills next_liveness ps9)
         (update_var out vs.vs_initial_fmp vs) st'` by
        (irule venom_asm_rel_release_dead_spills >> ASM_REWRITE_TAC[]) >>
      qexistsl [`1 + LENGTH (execute_plan initial_fmp opt_ops)`, `st'`] >>
      gvs[asm_steps_add, execute_plan_def, exec_stack_op_def]) >>
  Cases_on `MEM out next_liveness`
  >- (gvs[initial_fmp_dead_popmany, popmany_plan_def] >>
      pairarg_tac >> gvs[] >>
      `generated_plan_state_wf base'
         (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))` by
        (simp[stack_pop_def] >> irule generated_plan_state_wf_push >>
         ASM_REWRITE_TAC[]) >>
      qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
        `initial_fmp`, `out`] mp_tac initial_fmp_emit_update_var_bridge >>
      (impl_tac >-
        (ASM_REWRITE_TAC[] >>
         qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
         simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons])) >>
      strip_tac >>
      `prefix_spill_wf initial_fmp lo (FRONT opt_ops)
         (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))` by
        (Cases_on `opt_ops`
         >- simp[prefix_spill_wf_def] >>
         qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
         simp[optimistic_swap_plan_def] >>
         rpt (IF_CASES_TAC >> gvs[]) >>
         CASE_TAC >> gvs[] >> strip_tac >>
         `x < LENGTH
            (stack_push (Var out) (stack_pop 0 ps.ps_stack))` by
           metis_tac[stack_get_depth_bound] >>
         `prefix_spill_wf initial_fmp lo (h::t)
            (ps with ps_stack :=
               stack_push (Var out) (stack_pop 0 ps.ps_stack))` by
           (irule generated_do_swap_initial_fmp_front_transport >>
            simp[SF SFY_ss] >>
            qexistsl [`x`, `ps9`] >> ASM_REWRITE_TAC[] >>
            qpat_x_assum `x < LENGTH (stack_push _ _)` mp_tac >>
            simp[stack_push_def, stack_pop_def]) >>
         `h::t = FRONT (h::t) ++ [LAST (h::t)]` by
           simp[APPEND_FRONT_LAST] >>
         metis_tac[prefix_spill_wf_prefix]) >>
      `venom_asm_rel lo
         (ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack))
         (update_var out vs.vs_initial_fmp vs) as'` by
        (qpat_x_assum `venom_asm_rel lo (ps with ps_stack := SNOC _ _) _ _`
           mp_tac >> simp[stack_push_def, stack_pop_def]) >>
      `asm_block_at prog as'.as_pc (execute_plan initial_fmp opt_ops)` by
        (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
         simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
         ASM_REWRITE_TAC[]) >>
      drule optimistic_swap_plan_postfix_sim >>
      disch_then drule >> disch_then drule >> disch_then drule >>
      disch_then drule >> strip_tac >>
      first_x_assum (qspec_then `o2pc` strip_assume_tac) >>
      `venom_asm_rel lo (release_dead_spills next_liveness ps9)
         (update_var out vs.vs_initial_fmp vs) st'` by
        (irule venom_asm_rel_release_dead_spills >> ASM_REWRITE_TAC[]) >>
      qexistsl [`1 + LENGTH (execute_plan initial_fmp opt_ops)`, `st'`] >>
      gvs[asm_steps_add, execute_plan_def, exec_stack_op_def]) >>
  gvs[initial_fmp_dead_popmany, stack_push_def, stack_pop_def] >>
  qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
    `initial_fmp`, `out`] mp_tac initial_fmp_emit_update_var_bridge >>
  (impl_tac >-
    (ASM_REWRITE_TAC[] >>
     qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
     simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons])) >>
  strip_tac >>
  `asm_block_at prog as'.as_pc (execute_plan initial_fmp [SOPop 1])` by
    (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
     simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
     ASM_REWRITE_TAC[]) >>
  qspecl_then [`lo`, `o2pc`, `prog`, `initial_fmp`, `next_liveness`,
    `[SOPop 1]`,
    `ps with ps_stack := stack_push (Var out) (stack_pop 0 ps.ps_stack)`,
    `ps`, `release_dead_spills next_liveness ps`,
    `update_var out vs.vs_initial_fmp vs`, `as'`]
    mp_tac initial_fmp_generated_postfix_sim >>
  impl_tac
  >- (ASM_REWRITE_TAC[] >>
      simp[prefix_wf_def, stack_op_wf_def, is_prefix_op_def,
           prefix_spill_wf_def, spill_op_wf_def,
           apply_prefix_ops_def, apply_prefix_op_def, apply_simple_op_def,
           stack_push_def, stack_pop_def, SNOC_APPEND, TAKE_APPEND1,
           plan_state_component_equality] >>
      qpat_x_assum `venom_asm_rel lo (ps with ps_stack := SNOC _ _) _ _`
        mp_tac >> simp[SNOC_APPEND]) >>
  strip_tac >>
  qexistsl [`1 + LENGTH (execute_plan initial_fmp [SOPop 1])`, `as''`] >>
  gvs[asm_steps_add, execute_plan_def, exec_stack_op_def]
QED

Resume gen_inst_ok_sim[bump]:
  cheat
QED

Resume gen_inst_ok_sim[invoke]:
  cheat
QED

Resume gen_inst_ok_sim[none]:
  Cases_on `inst.inst_opcode` >>
  gvs[venom_to_evm_name_def, is_pre_codegen_opcode_def,
      is_unlowered_fmp_opcode_def,
      is_unlowered_internal_call_opcode_def,
      is_raw_fmp_opcode_def, is_fmp_param_opcode_def]
  >> TRY (`inst.inst_opcode <> ISTORE /\
           inst.inst_opcode <> JMP /\
           inst.inst_opcode <> JNZ /\
           inst.inst_opcode <> DJMP /\
           inst.inst_opcode <> ASSIGN /\
           inst.inst_opcode <> LOG /\
           inst.inst_opcode <> ASSERT /\
           inst.inst_opcode <> ASSERT_UNREACHABLE` by simp[] >>
          qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
          simp[step_inst_non_invoke, Once step_inst_base_def] >>
          every_case_tac >> simp[] >> NO_TAC)
  >- suspend "istore"
  >- suspend "jmp"
  >- suspend "jnz"
  >- suspend "djmp"
  >- suspend "assign"
  >- suspend "log"
  >- suspend "assert_ok"
  >> suspend "assert_unreachable_ok"
QED

Resume gen_inst_ok_sim[istore]:
  cheat
QED

Resume gen_inst_ok_sim[jmp]:
  cheat
QED

Resume gen_inst_ok_sim[jnz]:
  cheat
QED

Resume gen_inst_ok_sim[djmp]:
  cheat
QED

Resume gen_inst_ok_sim[assign]:
  qpat_x_assum `inst_wf inst` mp_tac >>
  qpat_x_assum `inst.inst_opcode = ASSIGN`
    (fn opc_th => rewrite_tac [opc_th] >> assume_tac opc_th) >>
  simp[inst_wf_def] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule step_inst_non_invoke >> disch_then (fn th => simp[th]) >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  strip_tac >>
  Cases_on `eval_operand h vs` >> gvs[] >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       is_commutative_def, venom_to_evm_name_def, generate_emit_ops_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  strip_tac >> gvs[] >>
  Cases_on `is_halting` >> Cases_on `MEM h' next_liveness` >> gvs[] >>
  TRY pairarg_tac >> gvs[]
  >- suspend "assign_live_nohalt"
  >- suspend "assign_dead_nohalt"
  >- suspend "assign_live_halt"
  >> suspend "assign_dead_halt"
QED

Resume gen_inst_ok_sim[assign_live_nohalt]:
  cheat
QED

Resume gen_inst_ok_sim[assign_dead_nohalt]:
  gvs[compute_operands_def] >>
  cheat
QED

Resume gen_inst_ok_sim[assign_live_halt]:
  cheat
QED

Resume gen_inst_ok_sim[assign_dead_halt]:
  gvs[compute_operands_def] >>
  (* pop_ops = [SOPop 1], ps8 = ... *)
  qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
  simp[popmany_plan_def, LET_THM, stack_get_depth_def, stack_push_def,
       REVERSE_SNOC, stack_find_def, is_contiguous_top_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF, popmany_individual_def, do_swap_def,
       stack_pop_def, FOLDL] >>
  strip_tac >> gvs[] >>
  `prefix_wf lo (LENGTH ps.ps_stack) input_ops /\
    prefix_end_len lo (LENGTH ps.ps_stack) input_ops = LENGTH ps1.ps_stack /\
    prefix_wf lo (LENGTH ps1.ps_stack) reorder_ops /\
    prefix_end_len lo (LENGTH ps1.ps_stack) reorder_ops = LENGTH ps4.ps_stack` by
    (qspecl_then [`[h]`, `ASSIGN`, `next_liveness`, `ps`, `lo`]
       mp_tac emit_input_plan_wf_len >>
     (impl_tac >- simp[]) >>
     (impl_tac >- (rpt strip_tac >> gvs[])) >>
     strip_tac >>
     qspecl_then [`dfg`, `[h]`, `ps1`, `lo`] mp_tac
       (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)
          (REWRITE_RULE [LET_THM] reorder_plan_wf_len)) >>
     (impl_tac >- gvs[]) >> gvs[]) >>
  (* prefix_spill_wf initial_fmp FULL from FRONT *)
  `prefix_spill_wf initial_fmp lo (input_ops ++ reorder_ops ++ [SOPop 1]) ps` by (
    qsuff_tac `prefix_spill_wf initial_fmp lo ((input_ops ++ reorder_ops) ++ [SOPop 1]) ps`
    >- simp[] >>
    rewrite_tac[prefix_spill_wf_snoc] >>
    conj_tac >- gvs[FRONT_APPEND_NOT_NIL]
    >- simp[spill_op_wf_def]) >>
  `1 <= LENGTH ps4.ps_stack` by
    (`(reorder_ops,ps4) =
       (\(ops,ps'). ([] ++ ops,ps')) (reorder_one dfg [h] 0 h ps1)` by
      (qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
       simp[Once reorder_plan_def, indexedListsTheory.MAPi_def] >>
       Cases_on `reorder_one dfg [h] 0 h ps1` >> simp[]) >>
     Cases_on `reorder_one dfg [h] 0 h ps1` >> gvs[] >>
     mp_tac (Q.SPECL [`dfg`,`[h]`,`0`,`h`,`ps1`,`lo`] reorder_one_wf_len) >>
     simp[]) >>
  `prefix_wf lo (LENGTH ps.ps_stack) (input_ops ++ reorder_ops ++ [SOPop 1])` by
    (`prefix_wf lo (LENGTH ps.ps_stack) (input_ops ++ reorder_ops)` by
       (irule prefix_wf_append >> gvs[]) >>
     `prefix_end_len lo (LENGTH ps.ps_stack) (input_ops ++ reorder_ops) =
      LENGTH ps4.ps_stack` by (simp[prefix_end_len_append] >> gvs[]) >>
     drule prefix_wf_append >>
     disch_then (qspec_then `[SOPop 1]` mp_tac) >>
     simp[prefix_wf_def, stack_op_wf_def, LET_THM]) >>
  qpat_x_assum `prefix_wf lo (LENGTH ps.ps_stack) input_ops`
    (fn th => assume_tac th >>
              assume_tac (MATCH_MP prefix_wf_every_prefix_op th)) >>
  qpat_x_assum `prefix_wf lo (LENGTH ps1.ps_stack) reorder_ops`
    (fn th => assume_tac th >>
              assume_tac (MATCH_MP prefix_wf_every_prefix_op th)) >>
  `EVERY is_prefix_op (input_ops ++ reorder_ops ++ [SOPop 1])` by
    (gvs[EVERY_APPEND] >> EVAL_TAC) >>
  mp_tac mixed_prefix_venom_asm_rel >>
  disch_then (qspecl_then [`input_ops ++ reorder_ops ++ [SOPop 1]`,
    `initial_fmp`,`lo`,`o2pc`,`prog`,`ps`,`vs`,`as`] mp_tac) >>
  (impl_tac >- gvs[EVERY_APPEND]) >>
  disch_then strip_assume_tac >>
  qexistsl [`LENGTH (execute_plan initial_fmp (input_ops ++ reorder_ops ++ [SOPop 1]))`,
            `st'`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (
    irule venom_asm_rel_release_dead_spills >>
    irule venom_asm_rel_update_var >>
    `~MEM (Var h') ps.ps_stack` by
      (strip_tac >> gvs[EVERY_MEM] >> res_tac >> gvs[]) >>
    `Var h' NOTIN FDOM ps.ps_spilled` by
      (strip_tac >> res_tac >> gvs[]) >>
    drule_all apply_prefix_ops_preserves_not_mem >> strip_tac >> gvs[] >>
    qsuff_tac
      `(apply_prefix_ops initial_fmp lo (input_ops ++ reorder_ops ++ [SOPop 1]) ps).ps_spilled =
       (ps4 with ps_stack :=
         TAKE (LENGTH ps4.ps_stack - 1)
           (SNOC (Var h')
              (TAKE (LENGTH ps4.ps_stack - 1) ps4.ps_stack))).ps_spilled /\
       (apply_prefix_ops initial_fmp lo (input_ops ++ reorder_ops ++ [SOPop 1]) ps).ps_stack =
       (ps4 with ps_stack :=
         TAKE (LENGTH ps4.ps_stack - 1)
           (SNOC (Var h')
              (TAKE (LENGTH ps4.ps_stack - 1) ps4.ps_stack))).ps_stack /\
       (apply_prefix_ops initial_fmp lo (input_ops ++ reorder_ops ++ [SOPop 1]) ps).ps_alloc =
       (ps4 with ps_stack :=
         TAKE (LENGTH ps4.ps_stack - 1)
           (SNOC (Var h')
              (TAKE (LENGTH ps4.ps_stack - 1) ps4.ps_stack))).ps_alloc` >- (
      strip_tac >>
      conj_tac >- (
        rpt strip_tac >>
        qpat_x_assum `Var h' NOTIN FDOM (apply_prefix_ops initial_fmp _ _ _).ps_spilled`
          mp_tac >> gvs[] >> strip_tac >>
        Cases_on `op` >> gvs[] >> CCONTR_TAC >> gvs[]) >>
      conj_tac >- (
        qpat_x_assum `~MEM (Var h') (apply_prefix_ops initial_fmp _ _ _).ps_stack`
          mp_tac >> gvs[] >> strip_tac >>
        simp[EVERY_MEM] >> rpt strip_tac >>
        Cases_on `op` >> simp[] >> CCONTR_TAC >> gvs[] >>
        metis_tac[MEM]) >>
      qpat_x_assum `venom_asm_rel lo (apply_prefix_ops initial_fmp _ _ _) vs st'`
        mp_tac >>
      simp[venom_asm_rel_def] >> gvs[] >> metis_tac[]) >>
    simp[apply_prefix_ops_append, sopop_align] >> cheat)
  >- gvs[Once ADD_COMM]
QED

Resume gen_inst_ok_sim[log]:
  cheat
QED

Resume gen_inst_ok_sim[assert_ok]:
  cheat
QED

Resume gen_inst_ok_sim[assert_unreachable_ok]:
  cheat
QED

Resume gen_inst_ok_sim[some_name]:
  (* Decompose ops = prefix_ops ++ [SOEmit name] ++ postfix_ops *)
  qspecl_then [`liveness`, `dfg`, `cfg`, `fn`, `inst`, `next_liveness`,
    `is_halting`, `next_is_term`, `bb_label`, `ps`, `name`]
    mp_tac regular_plan_full_decompose >>
  (impl_tac >- ASM_REWRITE_TAC[]) >> strip_tac >>
  `ops = prefix_ops ++ [SOEmit name] ++ postfix_ops /\ ps' = ps_out` by
    (qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = (ops, ps')` mp_tac >>
     qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ =
       (prefix_ops ++ _ ++ _, _)` (fn th => REWRITE_TAC[th]) >>
     strip_tac >> gvs[]) >>
  gvs[] >>
  (* Derive prefix_wf for prefix_ops *)
  `prefix_wf lo (LENGTH ps.ps_stack) prefix_ops /\
   EVERY is_prefix_op prefix_ops` by (
    qspecl_then [`liveness`, `dfg`, `cfg`, `fn`, `inst`, `next_liveness`,
      `is_halting`, `next_is_term`, `bb_label`, `ps`, `prefix_ops`,
      `postfix_ops`, `name`, `ps'`, `lo`]
      mp_tac regular_plan_prefix_wf_gen >>
    ASM_REWRITE_TAC[]) >>
  (* Apply prefix_sim to get AsmOK st_mid *)
  qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`,
    `prefix_ops`, `[SOEmit name] ++ postfix_ops`]
    mp_tac prefix_sim >>
  impl_tac
  >- (
    ASM_REWRITE_TAC[] >>
    conj_tac >- simp[] >>
    qpat_x_assum `prefix_spill_wf initial_fmp _ _ _` mp_tac >>
    simp[FRONT_APPEND] >>
    Cases_on `postfix_ops` >> simp[]
  ) >>
  strip_tac >>
  (* Split asm_block_at for [AsmOp name] + postfix *)
  qpat_x_assum `asm_block_at prog st_mid.as_pc
    (execute_plan initial_fmp ([SOEmit name] ++ postfix_ops))` mp_tac >>
  rewrite_tac[execute_plan_append, execute_plan_def, exec_stack_op_def] >>
  simp[] >> strip_tac >>
  imp_res_tac asm_block_at_append >>
  (* Now have: asm_block_at prog st_mid.as_pc [AsmOp name]
     and asm_block_at prog (st_mid.as_pc + 1) (execute_plan initial_fmp postfix_ops) *)
  (* Emit step + postfix + compose *)
  cheat
QED

Finalise gen_inst_ok_sim

(* ===== Prepare params plan simulation (entry block) ===== *)

(* When get_params returns [], prepare_params_plan returns ([], ps) *)
Theorem prepare_params_plan_nil:
  !liveness fn ps.
    get_params (HD fn.fn_blocks).bb_instructions = [] ==>
    prepare_params_plan liveness fn ps = ([], ps)
Proof
  rpt strip_tac >> simp[prepare_params_plan_def]
QED

(* ===== generate_block_plan decomposition ===== *)

(* When all instructions are non-PARAM, generate_block_plan decomposes
   into: label + clean_ops + instruction FOLDL (as block_foldl).
   This is the key structural lemma connecting to block_insts_sim. *)
Theorem gen_block_plan_decompose:
  !liveness dfg cfg fn bb ps block_ops ps'.
    EVERY (\inst. ~is_param_opcode inst.inst_opcode) bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    generate_block_plan liveness dfg cfg fn bb ps = SOME (block_ops, ps') ==>
    ?clean_ops ps2 inst_ops.
      ((LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\
        clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2)) \/
       (LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
        clean_ops = [] /\ ps2 = ps)) /\
      block_foldl
        (\i inst ps_cur.
           generate_inst_plan liveness dfg cfg fn inst
             (if i + 1 < LENGTH bb.bb_instructions
              then live_vars_at liveness bb.bb_label (i + 1)
              else live_vars_at liveness bb.bb_label
                     (LENGTH bb.bb_instructions))
             (bb_is_halting bb)
             (if i + 1 < LENGTH bb.bb_instructions
              then is_terminator (EL (i + 1) bb.bb_instructions).inst_opcode
              else F)
             bb.bb_label ps_cur)
        (SOME ([], ps2))
        (MAPi (\i inst. (i, inst)) bb.bb_instructions) =
        SOME (inst_ops, ps') /\
      block_ops = [SOLabel bb.bb_label] ++ clean_ops ++ inst_ops
Proof
  rpt strip_tac >>
  `non_param_insts bb = bb.bb_instructions`
    by metis_tac[non_param_insts_all_neq] >>
  `get_params bb.bb_instructions = []` by metis_tac[get_params_nil] >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >>
  Cases_on `bb = HD fn.fn_blocks` >> fs[]
  >- suspend "entry"
  >- suspend "non_entry"
QED

Resume gen_block_plan_decompose[entry]:
  `prepare_params_plan liveness fn ps = ([], ps)` by
    (irule prepare_params_plan_nil >> ASM_REWRITE_TAC[]) >>
  simp[] >>
  Cases_on `LENGTH (cfg_preds_of cfg (HD fn.fn_blocks).bb_label) = 1`
  >- (
    Cases_on `clean_stack_plan liveness cfg fn (HD fn.fn_blocks) ps` >>
    rename1 `clean_stack_plan _ _ _ _ _ = (cln_ops, ps2)` >>
    simp[] >>
    FULL_SIMP_TAC bool_ss [foldl_eq_block_foldl] >>
    Cases_on `block_foldl
      (\i inst ps_cur. generate_inst_plan liveness dfg cfg fn inst
         (if i + 1 < LENGTH (HD fn.fn_blocks).bb_instructions
          then live_vars_at liveness (HD fn.fn_blocks).bb_label (i + 1)
          else live_vars_at liveness (HD fn.fn_blocks).bb_label
                 (LENGTH (HD fn.fn_blocks).bb_instructions))
         (bb_is_halting (HD fn.fn_blocks))
         (i + 1 < LENGTH (HD fn.fn_blocks).bb_instructions /\
          is_terminator
            (EL (i + 1) (HD fn.fn_blocks).bb_instructions).inst_opcode)
         (HD fn.fn_blocks).bb_label ps_cur)
      (SOME ([], ps2))
      (MAPi (\i inst. (i, inst)) (HD fn.fn_blocks).bb_instructions)` >>
    simp[] >>
    Cases_on `x` >> simp[] >>
    strip_tac >> gvs[] >>
    qexistsl_tac [`cln_ops`, `ps2`, `q`] >> simp[]
  ) >>
  simp[] >>
  FULL_SIMP_TAC bool_ss [foldl_eq_block_foldl] >>
  Cases_on `block_foldl
    (\i inst ps_cur. generate_inst_plan liveness dfg cfg fn inst
       (if i + 1 < LENGTH (HD fn.fn_blocks).bb_instructions
        then live_vars_at liveness (HD fn.fn_blocks).bb_label (i + 1)
        else live_vars_at liveness (HD fn.fn_blocks).bb_label
               (LENGTH (HD fn.fn_blocks).bb_instructions))
       (bb_is_halting (HD fn.fn_blocks))
       (i + 1 < LENGTH (HD fn.fn_blocks).bb_instructions /\
        is_terminator
          (EL (i + 1) (HD fn.fn_blocks).bb_instructions).inst_opcode)
       (HD fn.fn_blocks).bb_label ps_cur)
    (SOME ([], ps))
    (MAPi (\i inst. (i, inst)) (HD fn.fn_blocks).bb_instructions)` >>
  simp[] >>
  Cases_on `x` >> simp[]
QED

Resume gen_block_plan_decompose[non_entry]:
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1`
  >- (
    (* single predecessor *)
    Cases_on `clean_stack_plan liveness cfg fn bb ps` >>
    rename1 `clean_stack_plan _ _ _ _ _ = (cln_ops, ps2)` >>
    simp[] >>
    FULL_SIMP_TAC bool_ss [foldl_eq_block_foldl] >>
    Cases_on `block_foldl
      (\i inst ps_cur. generate_inst_plan liveness dfg cfg fn inst
         (if i + 1 < LENGTH bb.bb_instructions
          then live_vars_at liveness bb.bb_label (i + 1)
          else live_vars_at liveness bb.bb_label (LENGTH bb.bb_instructions))
         (bb_is_halting bb)
         (i + 1 < LENGTH bb.bb_instructions /\
          is_terminator (EL (i + 1) bb.bb_instructions).inst_opcode)
         bb.bb_label ps_cur)
      (SOME ([], ps2))
      (MAPi (\i inst. (i, inst)) bb.bb_instructions)` >>
    simp[] >>
    Cases_on `x` >> simp[] >>
    strip_tac >> gvs[] >>
    qexistsl_tac [`cln_ops`, `ps2`, `q`] >> simp[]
  ) >>
  (* no single predecessor *)
  simp[] >>
  FULL_SIMP_TAC bool_ss [foldl_eq_block_foldl] >>
  Cases_on `block_foldl
    (\i inst ps_cur. generate_inst_plan liveness dfg cfg fn inst
       (if i + 1 < LENGTH bb.bb_instructions
        then live_vars_at liveness bb.bb_label (i + 1)
        else live_vars_at liveness bb.bb_label (LENGTH bb.bb_instructions))
       (bb_is_halting bb)
       (i + 1 < LENGTH bb.bb_instructions /\
        is_terminator (EL (i + 1) bb.bb_instructions).inst_opcode)
       bb.bb_label ps_cur)
    (SOME ([], ps))
    (MAPi (\i inst. (i, inst)) bb.bb_instructions)` >>
  simp[] >>
  Cases_on `x` >> simp[]
QED

Finalise gen_block_plan_decompose;
