(*
 * Checked frame-memory-pointer lowering.
 *)

Theory fmpLowerDefs
Ancestors
  dretDesugarDefs fmpReclaimDefs irSupply

(* A checked decomposition of the physical entry prefix before FMP lowering.
   User PARAM instructions are retained in source order; an existing hidden FMP
   parameter is rejected, and the optional RETPC parameter is separated from
   the ordinary body. *)
Datatype:
  fmp_entry_layout =
    FmpEntryLayout (instruction list) (instruction option) (instruction list)
End

Definition split_fmp_entry_from_def:
  split_fmp_entry_from k users [] =
    SOME (FmpEntryLayout (REVERSE users) NONE []) /\
  split_fmp_entry_from k users (inst::insts) =
    if inst.inst_opcode = PARAM then
      if param_inst_at k inst then
        split_fmp_entry_from (SUC k) (inst::users) insts
      else NONE
    else if inst.inst_opcode = FMP_PARAM then NONE
    else if inst.inst_opcode = RETPC_PARAM then
      if param_inst_at k inst /\ no_param_insts insts then
        SOME (FmpEntryLayout (REVERSE users) (SOME inst) insts)
      else NONE
    else if no_param_insts (inst::insts) then
      SOME (FmpEntryLayout (REVERSE users) NONE (inst::insts))
    else NONE
End

Definition split_fmp_entry_def:
  split_fmp_entry fn =
    case fn.fn_blocks of
      [] => NONE
    | entry::_ => split_fmp_entry_from 0 [] entry.bb_instructions
End

Definition set_param_index_def:
  set_param_index k inst = inst with inst_operands := [Lit (n2w k)]
End

(* Resolve a raw INVOKE against both the current context and the freshly
   computed information map.  Raw operands and outputs contain only the user
   layout: this boundary checks those exact arities before lowering appends a
   hidden runner input or publishing output.  The returned argument list
   excludes the leading label. *)
Definition fmp_resolve_invoke_def:
  fmp_resolve_invoke infos ctx inst =
    if inst.inst_opcode <> INVOKE then NONE
    else
      case inst.inst_operands of
        Label name::args =>
          (case lookup_function name ctx.ctx_functions of
             NONE => NONE
           | SOME callee =>
               case (FLOOKUP infos name,callee.fn_fmp_signature) of
                 (SOME info,SOME sig) =>
                   if info <> fmp_info_of_signature sig \/
                      ~fmp_seal_layout_matches_fn callee sig \/
                      LENGTH args <> LENGTH (fn_user_param_insts callee)
                   then NONE
                   else
                     (case fmp_expected_user_return_arity sig callee of
                        NONE => NONE
                      | SOME n =>
                          if LENGTH inst.inst_outputs = n
                          then SOME (callee,info,args)
                          else NONE)
               | _ => NONE)
      | _ => NONE
End

(* Exact envelopes consumed by the lowering engine.  In particular DRET and
   malformed raw operations cannot fall through as ordinary instructions. *)
Definition fmp_lower_inst_shape_def:
  fmp_lower_inst_shape infos ctx inst <=>
    if inst.inst_opcode = DALLOCA then
      LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1
    else if inst.inst_opcode = DRET then F
    else if inst.inst_opcode = GETFMP then
      inst.inst_operands = [] /\ LENGTH inst.inst_outputs = 1
    else if inst.inst_opcode = SETFMP then
      LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = []
    else if inst.inst_opcode = RETFMP then
      inst.inst_operands <> [] /\ inst.inst_outputs = []
    else if inst.inst_opcode = INVOKE then
      IS_SOME (fmp_resolve_invoke infos ctx inst)
    else ~is_raw_fmp_opcode inst.inst_opcode
End

Definition fmp_lower_insts_shape_def:
  fmp_lower_insts_shape infos ctx insts <=>
    EVERY (fmp_lower_inst_shape infos ctx) insts
End

Definition fmp_lower_blocks_shape_def:
  fmp_lower_blocks_shape infos ctx bbs <=>
    EVERY (\bb. fmp_lower_insts_shape infos ctx bb.bb_instructions) bbs
End

(* The internal lowering boundary is independently checked: the function must
   be the current context member, unsealed, covered by current information,
   canonically parameterized without an existing FMP parameter, and every
   instruction must have a supported exact envelope. *)
Definition fmp_lower_input_def:
  fmp_lower_input infos ctx fn <=>
    lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
    fn.fn_fmp_signature = NONE /\
    FLOOKUP infos fn.fn_name <> NONE /\
    canonical_param_prefix fn /\
    fn_hidden_fmp_param fn = NONE /\
    IS_SOME (split_fmp_entry fn) /\
    fmp_lower_blocks_shape infos ctx fn.fn_blocks
End

(* Select restores at one exact endpoint while preserving plan order.  The
   second component is threaded through all blocks and must be empty at the
   outer boundary, so an unlocated analysis result cannot be ignored. *)
Definition fmp_select_point_restores_def:
  fmp_select_point_restores p [] = ([],[]) /\
  fmp_select_point_restores p ((q,base)::rest) =
    let (here,later) = fmp_select_point_restores p rest in
      if q = p then (base::here,later)
      else (here,(q,base)::later)
End

Definition fmp_reclaim_input_def:
  fmp_reclaim_input fn (plan:fmp_reclaim_plan) <=>
    !p base. FLOOKUP plan p = SOME base ==>
      fmp_point_well_located fn p
End

Theorem fmp_reclaim_input_compute[compute]:
  fmp_reclaim_input fn plan <=>
    FEVERY (λ(p,base). fmp_point_well_located fn p) plan
Proof
  simp[fmp_reclaim_input_def, finite_mapTheory.FEVERY_DEF,
       finite_mapTheory.FLOOKUP_DEF] >>
  metis_tac[]
QED

(* Lower one checked instruction.  Single-instruction rewrites retain the
   source ID; a DALLOCA expansion obtains every temporary and instruction ID
   from the unit supply. *)
Definition fmp_lower_inst_def:
  fmp_lower_inst infos ctx runner s inst =
    if ~fmp_lower_inst_shape infos ctx inst then NONE
    else if inst.inst_opcode = DALLOCA then
      (case inst.inst_operands of
         [size_op] =>
           (case inst.inst_outputs of
              [old] =>
                (case fresh_ir_var s of (plus31,s1) =>
                 case fresh_ir_var s1 of (aligned,s2) =>
                 case fresh_inst_id s2 of (add_id,s3) =>
                 case fresh_inst_id s3 of (and_id,s4) =>
                 case fresh_inst_id s4 of (bump_id,s5) =>
                   SOME
                     ([mk_inst add_id ADD [size_op; Lit 31w] [plus31];
                       mk_inst and_id AND
                         [Var plus31;
                          Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
                         [aligned];
                       mk_inst bump_id BUMP
                         [Var runner; Var aligned] [old;runner]],
                      s5))
            | _ => NONE)
       | _ => NONE)
    else if inst.inst_opcode = DRET then NONE
    else if inst.inst_opcode = GETFMP then
      (case inst.inst_outputs of
         [out] => SOME ([inst with <| inst_opcode := ASSIGN;
                                    inst_operands := [Var runner] |>],s)
       | _ => NONE)
    else if inst.inst_opcode = SETFMP then
      (case inst.inst_operands of
         [value] => SOME ([inst with <| inst_opcode := ASSIGN;
                                      inst_outputs := [runner] |>],s)
       | _ => NONE)
    else if inst.inst_opcode = RETFMP then
      if NULL inst.inst_operands then NONE
      else SOME
        ([inst with <| inst_opcode := RET;
                     inst_operands :=
                       FRONT inst.inst_operands ++
                       [Var runner; LAST inst.inst_operands] |>],s)
    else if inst.inst_opcode = INVOKE then
      (case fmp_resolve_invoke infos ctx inst of
         NONE => NONE
       | SOME (callee,info,args) =>
           SOME
             ([inst with <|
                 inst_operands :=
                   Label callee.fn_name ::
                   (args ++ if info.fi_needs_fmp then [Var runner] else []);
                 inst_outputs :=
                   inst.inst_outputs ++
                   if info.fi_publishes_fmp then [runner] else [] |>],s))
    else if is_raw_fmp_opcode inst.inst_opcode then NONE
    else SOME ([inst],s)
End

Definition fmp_lower_insts_def:
  fmp_lower_insts infos ctx runner s [] = SOME ([],s) /\
  fmp_lower_insts infos ctx runner s (inst::insts) =
    case fmp_lower_inst infos ctx runner s inst of
      NONE => NONE
    | SOME (head,s1) =>
        case fmp_lower_insts infos ctx runner s1 insts of
          NONE => NONE
        | SOME (tail,s2) => SOME (head ++ tail,s2)
End

Definition fmp_emit_restores_def:
  fmp_emit_restores runner s [] = ([],s) /\
  fmp_emit_restores runner s (base::bases) =
    case fresh_inst_id s of (id,s1) =>
    case fmp_emit_restores runner s1 bases of (tail,s2) =>
      (mk_inst id ASSIGN [Var base] [runner]::tail,s2)
End

Datatype:
  fmp_blocks_result =
    FmpBlocksResult (basic_block list) ((fmp_point # string) list) ir_supply
End

(* Reclaim points refer to original instruction indices.  Each block selects
   its exact original endpoint before rewriting; leftovers are returned for the
   outer checked boundary to reject. *)
Definition fmp_lower_blocks_def:
  fmp_lower_blocks infos ctx runner s restores [] =
    SOME (FmpBlocksResult [] restores s) /\
  fmp_lower_blocks infos ctx runner s restores (bb::bbs) =
    case fmp_lower_insts infos ctx runner s bb.bb_instructions of
      NONE => NONE
    | SOME (insts,s1) =>
        let p = (bb.bb_label,LENGTH bb.bb_instructions) in
        let (bases,later) = fmp_select_point_restores p restores in
        case fmp_emit_restores runner s1 bases of (restore_insts,s2) =>
        case fmp_lower_blocks infos ctx runner s2 later bbs of
          NONE => NONE
        | SOME (FmpBlocksResult tail leftover s3) =>
            SOME (FmpBlocksResult
              ((bb with bb_instructions := insts ++ restore_insts)::tail)
              leftover s3)
End

Datatype:
  fmp_root_layout =
    FmpRootLayout num (instruction option) (instruction option) ir_supply
End

(* Allocate the optional incoming root before lowering the body, so generated
   instruction IDs follow physical output order. *)
Definition fmp_make_root_layout_def:
  fmp_make_root_layout ctx fn info runner s =
    case split_fmp_entry fn of
      NONE => NONE
    | SOME (FmpEntryLayout users retpc entry_body) =>
        if ~info.fi_needs_fmp then
          SOME (FmpRootLayout (LENGTH users) NONE retpc s)
        else if fn_is_context_entry ctx fn then
          (case fresh_inst_id s of (id,s1) =>
             SOME (FmpRootLayout (LENGTH users)
               (SOME (mk_inst id INITIAL_FMP [] [runner])) retpc s1))
        else
          case retpc of
            NONE => NONE
          | SOME retpc_inst =>
              (case fresh_inst_id s of (id,s1) =>
                 SOME (FmpRootLayout (LENGTH users)
                   (SOME (mk_inst id FMP_PARAM
                     [Lit (n2w (LENGTH users))] [runner]))
                   (SOME (set_param_index (SUC (LENGTH users)) retpc_inst)) s1))
End

(* Install the allocated root into the already-lowered entry block.  Lowering
   leaves the original physical parameter prefix one-for-one, so its user and
   RETPC lengths remain a stable split point even when the body expands. *)
Definition fmp_install_root_def:
  fmp_install_root ctx fn (FmpRootLayout n root retpc s) blocks =
    case blocks of
      [] => NONE
    | entry::rest =>
        let old_prefix = n + (if retpc = NONE then 0 else 1) in
        let users = TAKE n entry.bb_instructions in
        let body = DROP old_prefix entry.bb_instructions in
        let hidden = OPTION_TO_LIST root in
        let retpcs = OPTION_TO_LIST retpc in
        let insts =
          if fn_is_context_entry ctx fn then
            users ++ retpcs ++ hidden ++ body
          else users ++ hidden ++ retpcs ++ body
        in SOME ((entry with bb_instructions := insts)::rest,s)
End

Definition fmp_seal_def:
  fmp_seal ctx fn info blocks =
    fn with <|
      fn_blocks := blocks;
      fn_fmp_signature := SOME (<|
        fms_has_fmp_param := (info.fi_needs_fmp /\
                              ~fn_is_context_entry ctx fn);
        fms_publishes := info.fi_publishes_fmp
      |>)
    |>
End

(* Writing seal bits is not itself evidence that the constructed physical
   layout is valid.  Check the candidate against the current context before it
   can cross the lowering boundary. *)
Definition fmp_checked_seal_def:
  fmp_checked_seal ctx fn info blocks =
    let sealed = fmp_seal ctx fn info blocks in
      case sealed.fn_fmp_signature of
        NONE => NONE
      | SOME sig =>
          if fmp_signature_syntax_wf sig sealed then SOME sealed else NONE
End

Definition fmp_lower_function_with_info_def:
  fmp_lower_function_with_info infos ctx s fn =
    case fn.fn_fmp_signature of
      SOME sig =>
        if fmp_info_valid ctx infos /\
           lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
           fmp_signature_matches_fn ctx fn /\ no_raw_fmp_ops fn
        then SOME (fn,s) else NONE
    | NONE =>
        if ~(fmp_info_valid ctx infos /\ fmp_lower_input infos ctx fn) then NONE
        else
          case FLOOKUP infos fn.fn_name of
            NONE => NONE
          | SOME info =>
              case analyze_fmp_reclaims infos ctx fn of
                NONE => NONE
              | SOME plan =>
                  if ~fmp_reclaim_input fn plan then NONE
                  else if ~(info.fi_needs_fmp \/ info.fi_publishes_fmp) then
                    if plan = FEMPTY then
                      (case fmp_checked_seal ctx fn info fn.fn_blocks of
                         NONE => NONE
                       | SOME sealed => SOME (sealed,s))
                    else NONE
                  else
                    (case fresh_ir_var s of (runner,s1) =>
                     case fmp_make_root_layout ctx fn info runner s1 of
                       NONE => NONE
                     | SOME root_layout =>
                         case fmp_lower_blocks infos ctx runner
                           (case root_layout of FmpRootLayout n r pc s2 => s2)
                           (fmap_to_alist plan) fn.fn_blocks of
                           NONE => NONE
                         | SOME (FmpBlocksResult blocks leftover s3) =>
                             if leftover <> [] then NONE
                             else
                               case fmp_install_root ctx fn
                                      (case root_layout of
                                         FmpRootLayout n r pc s2 =>
                                           FmpRootLayout n r pc s3)
                                      blocks of
                                 NONE => NONE
                               | SOME (blocks',s4) =>
                                   (case fmp_checked_seal ctx fn info blocks' of
                                      NONE => NONE
                                    | SOME sealed => SOME (sealed,s4)))
End

Definition fmp_lower_function_def:
  fmp_lower_function ctx s fn =
    case analyze_fmp_context ctx of
      NONE => NONE
    | SOME infos => fmp_lower_function_with_info infos ctx s fn
End

Theorem fmp_lower_inst_shape_ordinary:
  inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> DRET /\
  inst.inst_opcode <> GETFMP /\
  inst.inst_opcode <> SETFMP /\
  inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> INVOKE ==>
  (fmp_lower_inst_shape infos ctx inst <=>
   ~is_raw_fmp_opcode inst.inst_opcode)
Proof
  simp[fmp_lower_inst_shape_def]
QED

Theorem fmp_lower_inst_ordinary:
  inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> DRET /\
  inst.inst_opcode <> GETFMP /\
  inst.inst_opcode <> SETFMP /\
  inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> INVOKE ==>
  fmp_lower_inst infos ctx runner s inst =
    if is_raw_fmp_opcode inst.inst_opcode then NONE
    else SOME ([inst],s)
Proof
  simp[fmp_lower_inst_def, fmp_lower_inst_shape_ordinary]
QED

Definition fmp_inst_invokes_def:
  fmp_inst_invokes target inst <=>
    ?tail. inst.inst_opcode = INVOKE /\
           inst.inst_operands = Label target :: tail
End


Theorem lookup_function_result_name[local]:
  !name fns fn.
    lookup_function name fns = SOME fn ==>
    fn.fn_name = name
Proof
  Induct_on `fns` >> simp[venomInstTheory.lookup_function_def, listTheory.FIND_thm]
  >> rw[] >> gvs[venomInstTheory.lookup_function_def]
QED
Theorem fmp_lower_inst_invokes:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') /\
  MEM out_inst out /\
  fmp_inst_invokes target out_inst ==>
  fmp_inst_invokes target inst
Proof
  rpt strip_tac
  >> Cases_on `inst.inst_opcode = DALLOCA`
  >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def,
         fmp_inst_invokes_def, fmp_resolve_invoke_def,
         lookup_function_result_name, venomInstTheory.mk_inst_def,
         AllCaseEqs()]
  >> Cases_on `inst.inst_opcode = DRET`
  >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def,
         fmp_inst_invokes_def, fmp_resolve_invoke_def,
         lookup_function_result_name, venomInstTheory.mk_inst_def,
         AllCaseEqs()]
  >> Cases_on `inst.inst_opcode = GETFMP`
  >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def,
         fmp_inst_invokes_def, fmp_resolve_invoke_def,
         lookup_function_result_name, venomInstTheory.mk_inst_def,
         AllCaseEqs()]
  >> Cases_on `inst.inst_opcode = SETFMP`
  >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def,
         fmp_inst_invokes_def, fmp_resolve_invoke_def,
         lookup_function_result_name, venomInstTheory.mk_inst_def,
         AllCaseEqs()]
  >> Cases_on `inst.inst_opcode = RETFMP`
  >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def,
         fmp_inst_invokes_def, fmp_resolve_invoke_def,
         lookup_function_result_name, venomInstTheory.mk_inst_def,
         AllCaseEqs()]
  >> Cases_on `inst.inst_opcode = INVOKE`
  >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def,
         fmp_inst_invokes_def, fmp_resolve_invoke_def,
         lookup_function_result_name, venomInstTheory.mk_inst_def,
         AllCaseEqs()]
  >> metis_tac[lookup_function_result_name]
QED

Theorem fmp_resolve_invoke_some:
  fmp_resolve_invoke infos ctx inst = SOME (callee,info,args) ==>
  ?name sig n.
    inst.inst_operands = Label name::args /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME sig /\
    FLOOKUP infos name = SOME info /\
    info = fmp_info_of_signature sig /\
    fmp_seal_layout_matches_fn callee sig /\
    LENGTH args = LENGTH (fn_user_param_insts callee) /\
    fmp_expected_user_return_arity sig callee = SOME n /\
    LENGTH inst.inst_outputs = n
Proof
  simp[fmp_resolve_invoke_def]
  >> Cases_on `inst.inst_opcode = INVOKE` >> simp[]
  >> Cases_on `inst.inst_operands` >> simp[]
  >> Cases_on `h` >> simp[]
  >> Cases_on `lookup_function s ctx.ctx_functions` >> simp[]
  >> Cases_on `FLOOKUP infos s` >> simp[]
  >> Cases_on `x.fn_fmp_signature` >> simp[]
  >> Cases_on `fmp_expected_user_return_arity x'' x` >> simp[]
  >> metis_tac[]
QED

Theorem fmp_checked_seal_some:
  fmp_checked_seal ctx fn info blocks = SOME sealed ==>
  sealed = fmp_seal ctx fn info blocks /\
  ?sig. sealed.fn_fmp_signature = SOME sig /\
        fmp_signature_syntax_wf sig sealed
Proof
  simp[fmp_checked_seal_def]
  >> Cases_on `(fmp_seal ctx fn info blocks).fn_fmp_signature` >> simp[]
  >> metis_tac[]
QED

val _ = export_theory();
