(*
 * Fresh current-context frame-memory-pointer needs analysis.
 *
 * Sealed functions are authoritative only after their current syntax/layout
 * validates.  Unsealed functions are seeded from raw syntax and closed over
 * current INVOKE edges by a bounded synchronous iteration.
 *)

Theory fmpAnalysisDefs
Ancestors
  fmpWfDefs
  venomWf
  finite_map
  arithmetic

Datatype:
  fmp_info = <|
    fi_needs_fmp : bool;
    fi_publishes_fmp : bool
  |>
End

Type fmp_info_map = ``:(string,fmp_info) fmap``

Definition fmp_info_bottom_def:
  fmp_info_bottom = <| fi_needs_fmp := F; fi_publishes_fmp := F |>
End

Definition fmp_info_join_def:
  fmp_info_join x y = <|
    fi_needs_fmp := (x.fi_needs_fmp \/ y.fi_needs_fmp);
    fi_publishes_fmp := (x.fi_publishes_fmp \/ y.fi_publishes_fmp)
  |>
End

Definition fmp_info_of_signature_def:
  fmp_info_of_signature sig = <|
    fi_needs_fmp := sig.fms_has_fmp_param;
    fi_publishes_fmp := sig.fms_publishes
  |>
End

(* Raw operations which consume the incoming/current FMP.  SETFMP adopts a
 * supplied value, so it can publish without requiring an incoming value. *)
Definition fmp_opcode_needs_fmp_def:
  fmp_opcode_needs_fmp op <=>
    op = DALLOCA \/ op = DRET \/ op = GETFMP \/ op = RETFMP
End

(* Operations which can advance, adopt, or explicitly return the current FMP. *)
Definition fmp_opcode_publishes_fmp_def:
  fmp_opcode_publishes_fmp op <=>
    op = DALLOCA \/ op = DRET \/ op = SETFMP \/ op = RETFMP
End

Definition fmp_scan_insts_def:
  fmp_scan_insts [] = fmp_info_bottom /\
  fmp_scan_insts (inst::rest) =
    fmp_info_join
      <| fi_needs_fmp := fmp_opcode_needs_fmp inst.inst_opcode;
         fi_publishes_fmp := fmp_opcode_publishes_fmp inst.inst_opcode |>
      (fmp_scan_insts rest)
End

Definition fmp_direct_info_def:
  fmp_direct_info fn = fmp_scan_insts (fn_insts fn)
End

(* Unlike the older call-graph scanner, malformed INVOKEs are rejected. *)
Definition fmp_invoke_target_def:
  fmp_invoke_target inst =
    if inst.inst_opcode = INVOKE then
      case inst.inst_operands of
        Label name::_ => SOME (SOME name)
      | _ => NONE
    else SOME NONE
End

Definition fmp_collect_invokes_def:
  fmp_collect_invokes [] = SOME [] /\
  fmp_collect_invokes (inst::rest) =
    case fmp_invoke_target inst of
      NONE => NONE
    | SOME target =>
        case fmp_collect_invokes rest of
          NONE => NONE
        | SOME targets =>
            SOME (case target of NONE => targets | SOME name => name::targets)
End

Definition fmp_resolve_targets_def:
  fmp_resolve_targets ctx [] = T /\
  fmp_resolve_targets ctx (name::rest) =
    if IS_SOME (lookup_function name ctx.ctx_functions) then
      fmp_resolve_targets ctx rest
    else F
End

Definition fmp_function_targets_def:
  fmp_function_targets ctx fn =
    case fmp_collect_invokes (fn_insts fn) of
      NONE => NONE
    | SOME targets =>
        if fmp_resolve_targets ctx targets then SOME targets else NONE
End

(* Seed one function.  The old map is used only to reject duplicate names. *)
Definition fmp_seed_function_def:
  fmp_seed_function ctx fn infos =
    if FLOOKUP infos fn.fn_name <> NONE then NONE
    else
      case fmp_function_targets ctx fn of
        NONE => NONE
      | SOME targets =>
          case fn.fn_fmp_signature of
            SOME sig =>
              if fmp_signature_matches_fn ctx fn then
                SOME (infos |+ (fn.fn_name, fmp_info_of_signature sig))
              else NONE
          | NONE =>
              SOME (infos |+ (fn.fn_name, fmp_direct_info fn))
End

Definition fmp_seed_functions_def:
  fmp_seed_functions ctx [] infos = SOME infos /\
  fmp_seed_functions ctx (fn::rest) infos =
    case fmp_seed_function ctx fn infos of
      NONE => NONE
    | SOME infos' => fmp_seed_functions ctx rest infos'
End

Definition seed_fmp_context_def:
  seed_fmp_context ctx = fmp_seed_functions ctx ctx.ctx_functions FEMPTY
End

Definition fmp_join_target_info_def:
  fmp_join_target_info infos [] acc = SOME acc /\
  fmp_join_target_info infos (name::rest) acc =
    case FLOOKUP infos name of
      NONE => NONE
    | SOME info =>
        fmp_join_target_info infos rest (fmp_info_join acc info)
End

(* Compute a function's next entry entirely from the old map. *)
Definition fmp_step_function_def:
  fmp_step_function ctx old fn =
    case FLOOKUP old fn.fn_name of
      NONE => NONE
    | SOME old_info =>
        case fn.fn_fmp_signature of
          SOME sig => SOME old_info
        | NONE =>
            case fmp_function_targets ctx fn of
              NONE => NONE
            | SOME targets =>
                fmp_join_target_info old targets
                  (fmp_info_join old_info (fmp_direct_info fn))
End

Definition fmp_step_functions_def:
  fmp_step_functions ctx old [] fresh = SOME fresh /\
  fmp_step_functions ctx old (fn::rest) fresh =
    case fmp_step_function ctx old fn of
      NONE => NONE
    | SOME info =>
        fmp_step_functions ctx old rest (fresh |+ (fn.fn_name,info))
End

Definition fmp_context_step_def:
  fmp_context_step ctx old =
    fmp_step_functions ctx old ctx.ctx_functions FEMPTY
End

(* Option-valued FUNPOW makes any unexpected malformed intermediate state
 * sticky while preserving the exact synchronous-round interface. *)
Definition fmp_option_step_def:
  fmp_option_step ctx state =
    case state of NONE => NONE | SOME infos => fmp_context_step ctx infos
End

Definition analyze_fmp_context_def:
  analyze_fmp_context (ctx:venom_context) : fmp_info_map option =
    FUNPOW (fmp_option_step ctx) (LENGTH ctx.ctx_functions)
      (seed_fmp_context ctx)
End

(* Stable consumer contract.  Coverage and exact sealed entries are stated
 * directly; every unsealed entry is the direct seed joined with all current
 * resolved callees, and malformed/dangling invokes are impossible. *)
Definition fmp_info_valid_def:
  fmp_info_valid (ctx:venom_context) (infos:fmp_info_map) <=>
    ctx_distinct_fn_names ctx /\
    (!fn. MEM fn ctx.ctx_functions ==> ?info. FLOOKUP infos fn.fn_name = SOME info) /\
    (!fn sig.
       MEM fn ctx.ctx_functions /\ fn.fn_fmp_signature = SOME sig ==>
       fmp_signature_matches_fn ctx fn /\
       FLOOKUP infos fn.fn_name = SOME (fmp_info_of_signature sig)) /\
    (!fn.
       MEM fn ctx.ctx_functions /\ fn.fn_fmp_signature = NONE ==>
       ?targets info.
         fmp_function_targets ctx fn = SOME targets /\
         FLOOKUP infos fn.fn_name = SOME info /\
         fmp_join_target_info infos targets (fmp_direct_info fn) = SOME info)
End

(* Executable view of the finite context-wide validity contract. *)
Theorem fmp_info_valid_compute[compute]:
  fmp_info_valid ctx infos <=>
    ctx_distinct_fn_names ctx /\
    EVERY (λfn. IS_SOME (FLOOKUP infos fn.fn_name)) ctx.ctx_functions /\
    EVERY
      (λfn.
        case fn.fn_fmp_signature of
          NONE => T
        | SOME sig =>
            fmp_signature_matches_fn ctx fn /\
            FLOOKUP infos fn.fn_name =
              SOME (fmp_info_of_signature sig))
      ctx.ctx_functions /\
    EVERY
      (λfn.
        case fn.fn_fmp_signature of
          SOME sig => T
        | NONE =>
            case fmp_function_targets ctx fn of
              NONE => F
            | SOME targets =>
                case FLOOKUP infos fn.fn_name of
                  NONE => F
                | SOME info =>
                    fmp_join_target_info infos targets
                      (fmp_direct_info fn) = SOME info)
      ctx.ctx_functions
Proof
  simp[fmp_info_valid_def, listTheory.EVERY_MEM] >>
  eq_tac >> rpt strip_tac >> gvs[] >>
  Cases_on `fn.fn_fmp_signature` >> gvs[] >>
  TRY (Cases_on `fmp_function_targets ctx fn` >> gvs[]) >>
  TRY (Cases_on `FLOOKUP infos fn.fn_name` >> gvs[]) >>
  rpt (qpat_x_assum `!f. MEM f ctx.ctx_functions ==> _`
         (qspec_then `fn` mp_tac)) >>
  simp[] >> res_tac >> gvs[]
QED

val _ = export_theory();
