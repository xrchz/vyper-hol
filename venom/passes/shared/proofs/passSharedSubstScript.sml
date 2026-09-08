(*
 * Pass Shared Operand Substitution Proofs
 *
 * Proves that operand substitution (single-variable and fmap-based)
 * preserves step_inst semantics.
 *
 * TOP-LEVEL:
 *   subst_operand_eval           — single substitution preserves eval_operand
 *   subst_op_map_eval            — map substitution preserves eval_operand
 *   subst_operand_eval_operands  — single substitution preserves eval_operands
 *   subst_op_map_eval_operands   — map substitution preserves eval_operands
 *   subst_operands_correct       — single substitution preserves step_inst
 *   subst_operands_map_correct   — map substitution preserves step_inst
 *)

Theory passSharedSubst
Ancestors
  passSharedDefs venomExecSemantics venomWf venomState venomInst
Libs
  listTheory rich_listTheory

(* ===================================================================== *)
(* ===== Operand eval preservation ===================================== *)
(* ===================================================================== *)

Theorem subst_operand_eval:
  !old new_op op s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operand (subst_operand old new_op op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_operand_def, eval_operand_def]
QED

Theorem subst_op_map_eval:
  !subs op s.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) ==>
    eval_operand (subst_op_map subs op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_op_map_def, eval_operand_def] >>
  CASE_TAC >> rw[] >> res_tac >> simp[eval_operand_def]
QED

Theorem subst_operand_eval_operands:
  !old new_op ops s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operands (MAP (subst_operand old new_op) ops) s =
    eval_operands ops s
Proof
  ntac 2 strip_tac >> Induct >>
  rw[eval_operands_def] >> imp_res_tac subst_operand_eval >> rw[]
QED

Theorem subst_op_map_eval_operands:
  !subs ops s.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) ==>
    eval_operands (MAP (subst_op_map subs) ops) s =
    eval_operands ops s
Proof
  strip_tac >> Induct >>
  rw[eval_operands_def] >> imp_res_tac subst_op_map_eval >> rw[]
QED

(* ===================================================================== *)
(* ===== step_inst_base operand irrelevance ============================ *)
(* ===================================================================== *)

Theorem extract_labels_map[local]:
  !ops g.
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) ==>
    extract_labels (MAP g ops) = extract_labels ops
Proof
  Induct >> simp[extract_labels_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h`
  >- (rename1 `Lit c` >>
      `!lbl. g (Lit c) <> Label lbl` by
        (first_x_assum (qspec_then `Lit c` mp_tac) >> simp[]) >>
      Cases_on `g (Lit c)` >> gvs[extract_labels_def])
  >- (rename1 `Var vn` >>
      `!lbl. g (Var vn) <> Label lbl` by
        (first_x_assum (qspec_then `Var vn` mp_tac) >> simp[]) >>
      Cases_on `g (Var vn)` >> gvs[extract_labels_def])
  >- (simp[extract_labels_def] >> res_tac >> simp[])
QED

val ops_tac =
  rpt strip_tac >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  TRY (Cases_on `t` >> simp[]);

Triviality exec_pure1_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_pure1 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_pure1 h inst s
Proof simp[exec_pure1_def] >> ops_tac
QED
Triviality exec_pure2_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_pure2 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_pure2 h inst s
Proof simp[exec_pure2_def] >> ops_tac
QED
Triviality exec_pure3_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_pure3 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_pure3 h inst s
Proof simp[exec_pure3_def] >> ops_tac
QED
Triviality exec_read0_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_read0 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_read0 h inst s
Proof simp[exec_read0_def] >> ops_tac
QED
Triviality exec_read1_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_read1 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_read1 h inst s
Proof simp[exec_read1_def] >> ops_tac
QED
Triviality exec_write2_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_write2 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_write2 h inst s
Proof simp[exec_write2_def] >> ops_tac
QED

val exec_map_thms = [exec_pure1_map, exec_pure2_map, exec_pure3_map,
                     exec_read0_map, exec_read1_map, exec_write2_map];

(* ===================================================================== *)
(* ===== Positional operand equivalence ================================ *)
(* ===================================================================== *)

(* Per-element eval_operand agreement implies eval_operands agreement *)
Theorem eval_operands_positional:
  !ops1 ops2 st. LENGTH ops1 = LENGTH ops2 /\
    (!i. i < LENGTH ops1 ==>
         eval_operand (EL i ops1) st = eval_operand (EL i ops2) st) ==>
    eval_operands ops1 st = eval_operands ops2 st
Proof
  Induct >> simp[eval_operands_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `ops2` >> gvs[eval_operands_def] >>
  `eval_operand h st = eval_operand h' st` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `eval_operands ops1 st = eval_operands t st` by (
    first_x_assum irule >> simp[] >>
    rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  simp[]
QED

(* Positional exec_* thms: arbitrary new_ops with per-element eval agreement *)
fun exec_pos_prove def =
  rpt strip_tac >>
  `eval_operands new_ops st = eval_operands inst.inst_operands st` by
    (irule eval_operands_positional >> simp[]) >>
  simp[def] >>
  pop_assum mp_tac >> simp[eval_operands_def] >>
  Cases_on `new_ops` >> Cases_on `inst.inst_operands` >> gvs[eval_operands_def] >>
  TRY (Cases_on `t` >> Cases_on `t'` >> gvs[eval_operands_def]) >>
  TRY (Cases_on `t''` >> Cases_on `t` >> gvs[eval_operands_def] >>
       TRY (Cases_on `t'` >> Cases_on `t''` >> gvs[eval_operands_def])) >>
  TRY (Cases_on `t` >> Cases_on `t''` >> gvs[eval_operands_def] >>
       TRY (Cases_on `t'` >> Cases_on `t` >> gvs[eval_operands_def])) >>
  rpt strip_tac >> gvs[] >>
  rpt (BasicProvers.EVERY_CASE_TAC >> gvs[]);

Triviality exec_pure1_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_pure1 f (inst with inst_operands := new_ops) st = exec_pure1 f inst st
Proof
  exec_pos_prove exec_pure1_def
QED

Triviality exec_pure2_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_pure2 f (inst with inst_operands := new_ops) st = exec_pure2 f inst st
Proof
  exec_pos_prove exec_pure2_def
QED

Triviality exec_pure3_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_pure3 f (inst with inst_operands := new_ops) st = exec_pure3 f inst st
Proof
  rpt strip_tac >>
  `eval_operands new_ops st = eval_operands inst.inst_operands st` by
    (irule eval_operands_positional >> simp[]) >>
  simp[exec_pure3_def] >>
  pop_assum mp_tac >> simp[eval_operands_def] >>
  Cases_on `new_ops` >> Cases_on `inst.inst_operands` >>
  gvs[eval_operands_def] >>
  TRY (Cases_on `t` >> Cases_on `t'` >> gvs[eval_operands_def]) >>
  TRY (Cases_on `t''` >> Cases_on `t` >> gvs[eval_operands_def] >>
       TRY (Cases_on `t'` >> Cases_on `t''` >> gvs[eval_operands_def])) >>
  TRY (Cases_on `t` >> Cases_on `t''` >> gvs[eval_operands_def] >>
       TRY (Cases_on `t'` >> Cases_on `t` >> gvs[eval_operands_def])) >>
  rpt strip_tac >> gvs[] >>
  rpt (BasicProvers.EVERY_CASE_TAC >> gvs[])
QED

Triviality exec_read0_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_read0 f (inst with inst_operands := new_ops) st = exec_read0 f inst st
Proof
  exec_pos_prove exec_read0_def
QED

Triviality exec_read1_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_read1 f (inst with inst_operands := new_ops) st = exec_read1 f inst st
Proof
  exec_pos_prove exec_read1_def
QED

Triviality exec_write2_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_write2 f (inst with inst_operands := new_ops) st = exec_write2 f inst st
Proof
  exec_pos_prove exec_write2_def
QED

val exec_pos_thms = [exec_pure1_pos, exec_pure2_pos, exec_pure3_pos,
                     exec_read0_pos, exec_read1_pos, exec_write2_pos];

Triviality exec_create_inst_operands[local]:
  !inst ops s v o' sz salt.
    exec_create (inst with inst_operands := ops) s v o' sz salt =
    exec_create inst s v o' sz salt
Proof rw[exec_create_def]
QED
Triviality exec_ext_call_inst_operands[local]:
  !inst ops s g a v ao as' ro rs is_s.
    exec_ext_call (inst with inst_operands := ops) s g a v ao as' ro rs is_s =
    exec_ext_call inst s g a v ao as' ro rs is_s
Proof rw[exec_ext_call_def]
QED
Triviality exec_delegatecall_inst_operands[local]:
  !inst ops s g a ao as' ro rs.
    exec_delegatecall (inst with inst_operands := ops) s g a ao as' ro rs =
    exec_delegatecall inst s g a ao as' ro rs
Proof rw[exec_delegatecall_def]
QED

val exec_inst_operands_thms = [exec_create_inst_operands,
  exec_ext_call_inst_operands, exec_delegatecall_inst_operands];

Triviality eval_operands_map_thm[local]:
  !g ops s.
    (!op. eval_operand (g op) s = eval_operand op s) ==>
    eval_operands (MAP g ops) s = eval_operands ops s
Proof
  ntac 2 strip_tac >> Induct_on `ops` >> rw[eval_operands_def]
QED

val label_op_tac =
  ONCE_ASM_REWRITE_TAC[step_inst_base_def] >>
  simp[extract_labels_map] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  TRY (BasicProvers.EVERY_CASE_TAC >> gvs[] >>
       TRY (first_x_assum (qspec_then `Lit c` mp_tac) >> simp[]) >>
       TRY (first_x_assum (qspec_then `Var vn` mp_tac) >> simp[]) >>
       NO_TAC);

val opcode_cases_tac =
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def];


Theorem parse_dret_shape_subst_operand[local]:
  !old new_op inst.
    IS_SOME (parse_dret_shape inst) ==>
    parse_dret_shape
      (inst with inst_operands :=
         MAP (subst_operand old new_op) inst.inst_operands) =
    parse_dret_shape inst
Proof
  rpt strip_tac >> Cases_on `inst.inst_operands` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def] >> Cases_on `h` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def, subst_operand_def]
QED

Theorem parse_dret_shape_subst_op_map[local]:
  !subs inst.
    IS_SOME (parse_dret_shape inst) ==>
    parse_dret_shape
      (inst with inst_operands := MAP (subst_op_map subs) inst.inst_operands) =
    parse_dret_shape inst
Proof
  rpt strip_tac >> Cases_on `inst.inst_operands` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def] >> Cases_on `h` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def, subst_op_map_def]
QED

Triviality step_inst_base_dret_map[local]:
  !g inst s.
    inst.inst_opcode = DRET /\
    parse_dret_shape
      (inst with inst_operands := MAP g inst.inst_operands) =
      parse_dret_shape inst /\
    eval_operands (MAP g inst.inst_operands) s =
      eval_operands inst.inst_operands s ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
  gvs[]
QED

Theorem step_inst_base_operands_irrelevant_safe[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    inst.inst_opcode <> DRET /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands = []`
  >- (`(inst with inst_operands := []) = inst` by
        simp[instruction_component_equality] >>
      gvs[])
  >> CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
  simp (exec_map_thms @ exec_inst_operands_thms @ [eval_operands_map_thm]) >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  TRY (Cases_on `t` >> simp[]) >>
  TRY (FIRST [Cases_on `t'`, Cases_on `t`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
  >- (qmatch_goalsub_abbrev_tac `lhs = rhs` >>
      Cases_on `inst.inst_opcode` >>
      gvs[Abbr `lhs`, Abbr `rhs`, is_alloca_op_def])
QED

Triviality step_inst_base_jnz_map[local]:
  !g inst s.
    inst.inst_opcode = JNZ /\
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  (* pos 1: case on operand, then TOP_CASE_TAC for g(non-Label) *)
  Cases_on `h'` >> simp[] >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[] >>
       BasicProvers.TOP_CASE_TAC >> gvs[] >>
       BasicProvers.TOP_CASE_TAC >> gvs[] >> NO_TAC) >>
  (* pos 2: Cases_on t' reuses h' and t *)
  Cases_on `t'` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  TRY (BasicProvers.TOP_CASE_TAC >> gvs[] >>
       BasicProvers.TOP_CASE_TAC >> gvs[] >>
       BasicProvers.TOP_CASE_TAC >> gvs[] >> NO_TAC) >>
  Cases_on `t` >> simp[]
QED

Theorem step_inst_base_operands_irrelevant_label[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) /\
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >> gvs[]
  >- label_op_tac
  >- (irule step_inst_base_jnz_map >> simp[])
  (* DJMP: extract_labels preserved, then ASM_REWRITE *)
  >- (`!ops. extract_labels (MAP g ops) = extract_labels ops` by
        (strip_tac >> irule extract_labels_map >> simp[]) >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      Cases_on `inst.inst_operands` >> simp[])
QED

Theorem step_inst_base_operands_irrelevant[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    inst.inst_opcode <> DRET /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
            inst.inst_opcode = DJMP`
  >- (irule step_inst_base_operands_irrelevant_label >> simp[])
  >> (irule step_inst_base_operands_irrelevant_safe >> gvs[])
QED

(* ===================================================================== *)
(* ===== INVOKE decode helper ========================================== *)
(* ===================================================================== *)

Theorem decode_invoke_map[local]:
  !f inst.
    (!lbl. f (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. f op <> Label lbl)) ==>
    decode_invoke (inst with inst_operands := MAP f inst.inst_operands) =
    case decode_invoke inst of
      NONE => NONE
    | SOME (callee, args) => SOME (callee, MAP f args)
Proof
  rpt strip_tac >>
  simp[decode_invoke_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[]
  >- (rename1 `Lit c` >>
      `!lbl. f (Lit c) <> Label lbl` by
        (first_x_assum (qspec_then `Lit c` mp_tac) >> simp[]) >>
      Cases_on `f (Lit c)` >> gvs[])
  >- (rename1 `Var vn` >>
      `!lbl. f (Var vn) <> Label lbl` by
        (first_x_assum (qspec_then `Var vn` mp_tac) >> simp[]) >>
      Cases_on `f (Var vn)` >> gvs[])
QED

(* ===================================================================== *)
(* ===== step_inst substitution correctness ============================ *)
(* ===================================================================== *)

Theorem subst_operands_correct:
  !fuel ctx inst s old new_op v.
    lookup_var old s = SOME v /\
    eval_operand new_op s = SOME v /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG /\
    (inst.inst_opcode = DRET ==> IS_SOME (parse_dret_shape inst)) /\
    (!lbl. new_op <> Label lbl) ==>
    step_inst fuel ctx (subst_operands old new_op inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `!op. eval_operand (subst_operand old new_op op) s =
        eval_operand op s` by (
    rpt strip_tac >> irule subst_operand_eval >>
    gvs[eval_operand_def]) >>
  `!lbl. subst_operand old new_op (Label lbl) = Label lbl` by
    simp[subst_operand_def] >>
  `!op. (!lbl. op <> Label lbl) ==>
        !lbl. subst_operand old new_op op <> Label lbl` by (
    Cases >> simp[subst_operand_def] >> rw[]) >>
  simp[subst_operands_def] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_then assume_tac decode_invoke_map >>
      imp_res_tac eval_operands_map_thm >>
      simp[step_inst_def] >>
      rpt (CASE_TAC >> simp[])) >>
  Cases_on `inst.inst_opcode = DRET`
  >- (simp[step_inst_non_invoke] >>
      irule step_inst_base_dret_map >>
      simp[parse_dret_shape_subst_operand, eval_operands_map_thm]) >>
  imp_res_tac step_inst_base_operands_irrelevant >>
  simp[step_inst_non_invoke]
QED

Theorem subst_operands_map_correct:
  !fuel ctx inst s subs.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                IS_SOME (eval_operand new_op s) /\
                eval_operand new_op s = eval_operand (Var v) s /\
                (!lbl. new_op <> Label lbl)) /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG /\
    (inst.inst_opcode = DRET ==> IS_SOME (parse_dret_shape inst)) ==>
    step_inst fuel ctx (subst_operands_map subs inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `!op. eval_operand (subst_op_map subs op) s =
        eval_operand op s` by (
    rpt strip_tac >> irule subst_op_map_eval >> metis_tac[]) >>
  `!lbl. subst_op_map subs (Label lbl) = Label lbl` by
    rw[subst_op_map_def] >>
  `!op. (!lbl. op <> Label lbl) ==>
        !lbl. subst_op_map subs op <> Label lbl` by (
    Cases >> simp[subst_op_map_def] >> rw[] >>
    rename1 `FLOOKUP subs vn` >> CASE_TAC >> simp[] >>
    rename1 `FLOOKUP subs vn = SOME nop` >>
    first_x_assum drule >> simp[]) >>
  simp[subst_operands_map_def] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_then assume_tac decode_invoke_map >>
      imp_res_tac eval_operands_map_thm >>
      simp[step_inst_def] >>
      rpt (CASE_TAC >> simp[])) >>
  Cases_on `inst.inst_opcode = DRET`
  >- (simp[step_inst_non_invoke] >>
      irule step_inst_base_dret_map >>
      simp[parse_dret_shape_subst_op_map, eval_operands_map_thm]) >>
  imp_res_tac step_inst_base_operands_irrelevant >>
  simp[step_inst_non_invoke]
QED

(* Helper: subst_op_map preserves all-Label lists (from inst_wf DJMP) *)
Triviality subst_op_map_preserves_labels:
  !ops subs. EVERY (\op. IS_SOME (get_label op)) ops ==>
    MAP (subst_op_map subs) ops = ops
Proof
  Induct >> rw[] >> Cases_on `h` >> gvs[get_label_def, subst_op_map_def]
QED

(* Helper: if MAP (subst_op_map subs) preserves operands, subst is identity *)
Triviality subst_operands_map_id:
  !subs inst. MAP (subst_op_map subs) inst.inst_operands = inst.inst_operands ==>
    subst_operands_map subs inst = inst
Proof
  rw[subst_operands_map_def] >> Cases_on `inst` >>
  gvs[venomInstTheory.instruction_fn_updates,
      venomInstTheory.instruction_accessors]
QED

(* Stronger version: inst_wf handles structural positions, only PHI excluded.
   Strategy: structural opcodes (PARAM, FMP_PARAM, RETPC_PARAM, ALLOCA, LOG,
   JMP, JNZ, DJMP, INVOKE) handled by inst_wf + definition unfolding.
   OFFSET is exec_pure2 (positional), handled by step_inst_base_operands_irrelevant_safe.
   All other non-PHI opcodes handled by step_inst_base_operands_irrelevant_safe
   (which only needs eval_operand equivalence). *)
Theorem subst_operands_map_correct_wf:
  !fuel ctx inst s subs.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) /\
    inst_wf inst /\
    inst.inst_opcode <> PHI ==>
    step_inst fuel ctx (subst_operands_map subs inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `!op. eval_operand (subst_op_map subs op) s =
        eval_operand op s` by
    (rpt strip_tac >> irule subst_op_map_eval >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- (`IS_SOME (parse_dret_shape inst)` by gvs[inst_wf_def] >>
      simp[subst_operands_map_def, step_inst_non_invoke] >>
      irule step_inst_base_dret_map >>
      simp[parse_dret_shape_subst_op_map, eval_operands_map_thm]) >>
  (* Non-structural opcodes *)
  Cases_on `inst.inst_opcode <> PARAM /\
            inst.inst_opcode <> FMP_PARAM /\
            inst.inst_opcode <> RETPC_PARAM /\
            ~is_alloca_op inst.inst_opcode /\
            inst.inst_opcode <> LOG /\
            inst.inst_opcode <> JMP /\
            inst.inst_opcode <> JNZ /\
            inst.inst_opcode <> DJMP /\
            inst.inst_opcode <> INVOKE`
  >- (simp[subst_operands_map_def, step_inst_non_invoke] >>
      irule step_inst_base_operands_irrelevant_safe >> gvs[])
  >>
  (* Structural: inst_wf resolves operand shapes *)
  gvs[is_alloca_op_def] >> gvs[inst_wf_def] >>
  (* Trivial: all Lit/Label operands => subst is identity *)
  TRY (`subst_operands_map subs inst = inst` by
         (irule subst_operands_map_id >> simp[subst_op_map_def]) >>
       simp[] >> NO_TAC) >>
  gvs[subst_operands_map_def, subst_op_map_def]
  >- ((* ALLOCA: resolve is_alloca_op *)
    `inst.inst_opcode = ALLOCA` by
      (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
    gvs[inst_wf_def, subst_op_map_def, step_inst_def, exec_alloca_def] >>
    simp[Once step_inst_base_def, SimpLHS] >>
    simp[Once step_inst_base_def, SimpRHS] >> simp[exec_alloca_def])
  >- ((* LOG *)
    `rest <> []` by (Cases_on `rest` >> gvs[]) >>
    simp[step_inst_non_invoke] >>
    simp[Once step_inst_base_def] >>
    simp[Once step_inst_base_def] >>
    simp[GSYM listTheory.MAP_DROP, listTheory.EL_MAP,
         rich_listTheory.MAP_HD] >>
    `eval_operands (MAP (subst_op_map subs) (DROP 2 rest)) s =
     eval_operands (DROP 2 rest) s` by
      (irule eval_operands_map_thm >> metis_tac[]) >> simp[])
  >- ((* JNZ *)
    simp[step_inst_non_invoke] >>
    simp[Once step_inst_base_def] >>
    simp[Once step_inst_base_def])
  >- ((* DJMP *)
    imp_res_tac subst_op_map_preserves_labels >>
    simp[step_inst_non_invoke] >>
    simp[Once step_inst_base_def] >>
    simp[Once step_inst_base_def])
  >- ((* INVOKE *)
    simp[step_inst_def, decode_invoke_def] >>
    `eval_operands (MAP (subst_op_map subs) args) s =
     eval_operands args s` by
      (irule eval_operands_map_thm >> metis_tac[]) >>
    simp[] >> rpt (CASE_TAC >> simp[]))
QED

(* ===================================================================== *)
(* ===== General positional operand replacement ======================== *)
(* ===================================================================== *)

(* ML tactic: find the eval_operand universal hypothesis and instantiate at
   indices 0..max_idx. Uses ASSUME (non-consuming) so the original stays. *)
fun inst_eval_tac (asl, g) = let
  val eval_hyp = valOf (List.find (fn a =>
    is_forall a andalso
    can (find_term (fn t => (fst(dest_const t) = "eval_operand") handle _ => false)) a andalso
    not (can (find_term (fn t => (fst(dest_const t) = "Label") handle _ => false)) a)
    ) asl)
  val th = ASSUME eval_hyp
  fun inst_at n = ASSUME_TAC (SIMP_RULE (srw_ss()) []
    (SPEC (numSyntax.mk_numeral (Arbnum.fromInt n)) th))
  fun go n = if n > 12 then ALL_TAC else inst_at n >> go (n+1)
in go 0 (asl, g) end handle _ => ALL_TAC (asl, g);

val wf_opcode_finish_tac =
  Cases_on `inst.inst_opcode` >>
  ASM_REWRITE_TAC[] >>
  gvs[is_alloca_op_def];
Triviality step_inst_base_RET_eval_operands[local]:
  !inst new_ops st.
    inst.inst_opcode = RET /\
    eval_operands new_ops st = eval_operands inst.inst_operands st ==>
    step_inst_base (inst with inst_operands := new_ops) st =
    step_inst_base inst st
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[]
QED

val ret_long_finish_tac =
  irule step_inst_base_RET_eval_operands >> simp[];


val long_safe_finish_tac =
  Cases_on `inst` >>
  gvs[venomInstTheory.instruction_fn_updates,
      venomInstTheory.instruction_accessors] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >>
  simp[exec_read0_def, eval_operands_def] >>
  simp (exec_pos_thms @ exec_inst_operands_thms);

Triviality step_inst_base_CALL_pos[local]:
  !inst new_ops st.
    inst.inst_opcode = CALL /\
    LENGTH inst.inst_operands = 7 /\
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) st =
         eval_operand (EL i inst.inst_operands) st) ==>
    step_inst_base (inst with inst_operands := new_ops) st =
    step_inst_base inst st
Proof
  rpt gen_tac >> strip_tac >>
  gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  inst_eval_tac >> gvs[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >>
  simp[exec_ext_call_inst_operands]
QED

val call_long_finish_tac =
  qpat_x_assum `inst.inst_opcode = CALL` assume_tac >>
  irule step_inst_base_CALL_pos >> simp[];

val long_or_call_finish_tac =
  call_long_finish_tac ORELSE long_safe_finish_tac;

Triviality step_inst_base_pos_safe_long[local]:
  !inst new_ops st.
    inst_wf inst /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\
    6 < LENGTH inst.inst_operands /\
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (inst.inst_opcode = DRET ==>
      parse_dret_shape (inst with inst_operands := new_ops) =
      parse_dret_shape inst) /\
    eval_operands new_ops st = eval_operands inst.inst_operands st /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) st =
         eval_operand (EL i inst.inst_operands) st) ==>
    step_inst_base (inst with inst_operands := new_ops) st =
    step_inst_base inst st
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inst_wf inst`
    (fn th => ASSUME_TAC (REWRITE_RULE [inst_wf_def] th)) >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_alloca_op_def]
  >- long_safe_finish_tac
  >- ret_long_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac >>
  gvs[]
QED

val wf_opcode_contra_tac =
  qsuff_tac `F` >- simp[] >>
  qpat_x_assum `inst_wf inst` (mp_tac o REWRITE_RULE [inst_wf_def]) >>
  Cases_on `inst.inst_opcode` >>
  ASM_REWRITE_TAC[] >>
  gvs[is_alloca_op_def];

val pos_opcode_finish_tac =
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >>
  simp (exec_pos_thms @ exec_inst_operands_thms) >>
  rpt (BasicProvers.EVERY_CASE_TAC >> gvs[]);

Triviality step_inst_base_pos_safe[local]:
  !inst new_ops st.
    inst_wf inst /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (inst.inst_opcode = DRET ==>
      parse_dret_shape (inst with inst_operands := new_ops) =
      parse_dret_shape inst) /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    step_inst_base (inst with inst_operands := new_ops) st =
    step_inst_base inst st
Proof
  rpt strip_tac >>
  `eval_operands new_ops st = eval_operands inst.inst_operands st` by
    (irule eval_operands_positional >> simp[]) >>
  Cases_on `6 < LENGTH inst.inst_operands` >-
   (irule step_inst_base_pos_safe_long >> simp[]) >>
  qpat_x_assum `inst_wf inst`
    (fn th => ASSUME_TAC (REWRITE_RULE [inst_wf_def] th)) >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_alloca_op_def] >>
  gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  inst_eval_tac >> gvs[]
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
QED

(*
 * step_inst_operands_equiv: replacing operands with evaluation-equivalent
 * ones preserves step_inst semantics.
 *
 * Hypotheses:
 *   - inst_wf: well-formed instruction (gives operand count/shape)
 *   - LENGTH: new_ops same length as original
 *   - eval agreement: per-element eval_operand agreement
 *   - label preservation: Label operands structurally preserved
 *   - HD preservation for LOG: first operand (topic count Lit) preserved
 *   - excluded: PHI (not executable), ALLOCA/PALLOCA/CALLOCA (need Lit),
 *     PARAM (needs Lit)
 *)
Theorem step_inst_operands_equiv:
  !fuel ctx inst new_ops st.
    inst_wf inst /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    inst.inst_opcode <> PHI /\
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (inst.inst_opcode = DRET ==>
      parse_dret_shape (inst with inst_operands := new_ops) =
      parse_dret_shape inst) /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) st = eval_operand (EL i inst.inst_operands) st) /\
    (!i. i < LENGTH inst.inst_operands ==>
         !lbl. EL i inst.inst_operands = Label lbl ==> EL i new_ops = Label lbl) /\
    (inst.inst_opcode = LOG ==> HD new_ops = HD inst.inst_operands) ==>
    step_inst fuel ctx (inst with inst_operands := new_ops) st =
    step_inst fuel ctx inst st
Proof
  rpt strip_tac >>
  (* INVOKE: decode label + eval_operands on args *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[inst_wf_def] >>
      Cases_on `new_ops` >> gvs[] >>
      `h = Label lbl` by
        (qpat_x_assum `!i. i < _ ==> !lbl'. _ = Label lbl' ==> _`
           (qspec_then `0` mp_tac) >> simp[]) >>
      gvs[] >>
      `eval_operands t st = eval_operands args st` by (
        irule eval_operands_positional >> simp[] >>
        rpt strip_tac >>
        qpat_x_assum `!j. j < SUC _ ==> eval_operand _ _ = _`
          (qspec_then `SUC i` mp_tac) >> simp[]) >>
      simp[step_inst_def, decode_invoke_def] >>
      rpt (CASE_TAC >> simp[])) >>
  simp[step_inst_non_invoke] >>
  (* Non-structural: use ML-level step_inst_base_pos_safe *)
  Cases_on `inst.inst_opcode <> LOG /\ inst.inst_opcode <> JMP /\
            inst.inst_opcode <> JNZ /\ inst.inst_opcode <> DJMP`
  >- (irule step_inst_base_pos_safe >> simp[]) >>
  (* Structural opcodes: LOG, JMP, JNZ, DJMP *)
  gvs[] >> gvs[inst_wf_def]
  >- ( (* LOG: Lit tc :: rest *)
      Cases_on `new_ops` >> gvs[] >>
      `eval_operand (HD t) st = eval_operand (HD rest) st` by (
        qpat_x_assum `!i. _ ==> eval_operand _ _ = _`
          (qspec_then `1` mp_tac) >> simp[] >>
        Cases_on `t` >> Cases_on `rest` >> gvs[]) >>
      `eval_operand (EL 1 t) st = eval_operand (EL 1 rest) st` by (
        qpat_x_assum `!i. _ ==> eval_operand _ _ = _`
          (qspec_then `2` mp_tac) >> simp[]) >>
      `eval_operands (DROP 2 t) st = eval_operands (DROP 2 rest) st` by (
        irule eval_operands_positional >> simp[LENGTH_DROP] >>
        rpt strip_tac >>
        `EL i (DROP 2 t) = EL (i + 2) t` by (irule EL_DROP >> simp[]) >>
        `EL i (DROP 2 rest) = EL (i + 2) rest` by (irule EL_DROP >> simp[]) >>
        simp[] >>
        qpat_x_assum `!i. _ ==> eval_operand _ _ = _`
          (qspec_then `SUC (i + 2)` mp_tac) >> simp[]) >>
      simp[Once step_inst_base_def, SimpLHS] >>
      simp[Once step_inst_base_def, SimpRHS])
  >- ( (* JMP: [Label lbl] *)
      Cases_on `new_ops` >> gvs[] >>
      simp[Once step_inst_base_def, SimpLHS] >>
      simp[Once step_inst_base_def, SimpRHS])
  >- ( (* JNZ: [c; Label l1; Label l2] *)
      `EL 1 new_ops = Label l1` by (
        qpat_x_assum `!i. _ ==> !lbl. _ ==> _`
          (qspec_then `1` mp_tac) >> simp[]) >>
      `EL 2 new_ops = Label l2` by (
        qpat_x_assum `!i. _ ==> !lbl. _ ==> _`
          (qspec_then `2` mp_tac) >> simp[]) >>
      `eval_operand (HD new_ops) st = eval_operand c st` by (
        qpat_x_assum `!i. _ ==> eval_operand _ _ = _`
          (qspec_then `0` mp_tac) >> simp[]) >>
      gvs[LENGTH_EQ_NUM_compute] >>
      simp[Once step_inst_base_def, SimpLHS] >>
      simp[Once step_inst_base_def, SimpRHS])
  >> ( (* DJMP: sel :: label_ops, need t = label_ops *)
      Cases_on `new_ops` >> gvs[] >>
      `t = label_ops` by (
        irule LIST_EQ >> simp[] >> rpt strip_tac >>
        rename1 `x < LENGTH label_ops` >>
        `(\op. IS_SOME (get_label op)) (EL x label_ops)` by
          (irule (iffLR EVERY_EL) >> simp[]) >> fs[] >>
        Cases_on `EL x label_ops` >> gvs[get_label_def] >>
        qpat_x_assum `!i. i < _ ==> !lbl. _ = Label lbl ==> _`
          (qspec_then `SUC x` mp_tac) >> simp[]) >>
      `eval_operand h st = eval_operand sel st` by (
        qpat_x_assum `!i. _ ==> eval_operand _ _ = _`
          (qspec_then `0` mp_tac) >> simp[]) >>
      gvs[] >>
      simp[Once step_inst_base_def, SimpLHS] >>
      simp[Once step_inst_base_def, SimpRHS])
QED
