(*
 * Checked, chain-compressing compilation-unit label maps.
 *)

Theory unitLabelMap
Ancestors
  venomCompilerWf
  cfgTransform

Definition resolve_label_fuel_def:
  resolve_label_fuel label_map visited 0 label =
    (case ALOOKUP label_map label of
       NONE => SOME label
     | SOME next => NONE) /\
  resolve_label_fuel label_map visited (SUC fuel) label =
    if MEM label visited then NONE
    else
      case ALOOKUP label_map label of
        NONE => SOME label
      | SOME next =>
          resolve_label_fuel label_map (label::visited) fuel next
End

Definition resolve_label_entries_def:
  resolve_label_entries label_map fuel [] = SOME [] /\
  resolve_label_entries label_map fuel ((source,target)::rest) =
    case resolve_label_fuel label_map [] fuel source of
      NONE => NONE
    | SOME terminal =>
        case resolve_label_entries label_map fuel rest of
          NONE => NONE
        | SOME resolved => SOME ((source,terminal)::resolved)
End

Definition resolve_label_map_def:
  resolve_label_map label_map =
    if ALL_DISTINCT (MAP FST label_map) then
      resolve_label_entries label_map (SUC (LENGTH label_map)) label_map
    else NONE
End

Theorem resolve_label_map_singleton:
  a <> b ==> resolve_label_map [(a,b)] = SOME [(a,b)]
Proof
  strip_tac >>
  EVAL_TAC >> gvs[]
QED

Theorem resolve_label_map_two_link:
  ALL_DISTINCT [a;b;c] ==>
  resolve_label_map [(a,b);(b,c)] = SOME [(a,c);(b,c)]
Proof
  strip_tac >> EVAL_TAC >> gvs[listTheory.ALL_DISTINCT]
QED

Theorem resolve_label_map_self_cycle[simp]:
  resolve_label_map [(a,a)] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_direct_eval:
  resolve_label_map [("a","b")] = SOME [("a","b")]
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_chain_eval:
  resolve_label_map [("a","b");("b","c")] =
    SOME [("a","c");("b","c")]
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_non_topological_chain_eval:
  resolve_label_map [("b","c");("a","b")] =
    SOME [("b","c");("a","c")]
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_two_cycle_eval:
  resolve_label_map [("a","b");("b","a")] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_three_cycle_eval:
  resolve_label_map [("a","b");("b","c");("c","a")] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_duplicate_domain_eval:
  resolve_label_map [("a","b");("a","c")] = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
