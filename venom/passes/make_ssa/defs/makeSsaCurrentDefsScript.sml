(*
 * Current-analysis, supply-safe MakeSSA adapter — definitions.
 *
 * This theory starts with the canonical analysis bridge.  The configured
 * MakeSSA implementation is kept separate from the legacy semantic model in
 * makeSsaDefs.
 *)

Theory makeSsaCurrentDefs
Ancestors
  makeSsaDefs cfgDefs dominatorDefs livenessDefs
  list alist

(* A finite association-list view of a query function, in function-label
   order.  This is the only conversion used by the current-analysis bridge. *)
Definition current_query_map_def:
  current_query_map labels query = MAP (\l. (l, query l)) labels
End

Definition current_pred_map_def:
  current_pred_map fn =
    current_query_map (fn_labels fn) (cfg_preds_of (cfg_analyze fn))
End

Definition current_succ_map_def:
  current_succ_map fn =
    current_query_map (fn_labels fn) (cfg_succs_of (cfg_analyze fn))
End

Definition current_frontier_map_def:
  current_frontier_map fn =
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
      current_query_map (fn_labels fn) (frontier_of dom)
End

Definition current_live_in_def:
  current_live_in fn =
    let live = liveness_analyze fn in
      current_query_map (fn_labels fn) (\l. live_vars_at live l 0)
End

(* Build the dominator tree from the canonical dominated-children query.
   Fuel makes this executable independently of analysis correctness. *)
Definition current_dom_tree_aux_def:
  (current_dom_tree_aux dom 0 lbl = DNode lbl []) /\
  (current_dom_tree_aux dom (SUC fuel) lbl =
     DNode lbl
       (MAP (current_dom_tree_aux dom fuel) (dominated_of dom lbl)))
End

Definition current_dom_tree_def:
  current_dom_tree fn =
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
      case fn_entry_label fn of
        NONE => DNode "" []
      | SOME entry => current_dom_tree_aux dom (LENGTH (fn_labels fn)) entry
End

(* Structural postorder of the dominator tree (children left-to-right, then
   the node), rather than the CFG DFS postorder. *)
Definition dom_tree_postorder_def:
  dom_tree_postorder (DNode lbl children) =
    FLAT (MAP dom_tree_postorder children) ++ [lbl]
End

Definition current_dom_postorder_def:
  current_dom_postorder fn = dom_tree_postorder (current_dom_tree fn)
End

Theorem ALOOKUP_current_query_map:
  !labels query l.
    MEM l labels ==>
    ALOOKUP (current_query_map labels query) l = SOME (query l)
Proof
  Induct >> gvs[current_query_map_def] >> metis_tac[]
QED

Theorem ALOOKUP_current_pred_map:
  MEM l (fn_labels fn) ==>
  ALOOKUP (current_pred_map fn) l =
    SOME (cfg_preds_of (cfg_analyze fn) l)
Proof
  simp[current_pred_map_def, ALOOKUP_current_query_map]
QED

Theorem ALOOKUP_current_succ_map:
  MEM l (fn_labels fn) ==>
  ALOOKUP (current_succ_map fn) l =
    SOME (cfg_succs_of (cfg_analyze fn) l)
Proof
  simp[current_succ_map_def, ALOOKUP_current_query_map]
QED

Theorem ALOOKUP_current_frontier_map:
  MEM l (fn_labels fn) ==>
  ALOOKUP (current_frontier_map fn) l =
    SOME (frontier_of (dom_analyze (cfg_analyze fn) fn) l)
Proof
  simp[current_frontier_map_def, ALOOKUP_current_query_map]
QED

Theorem ALOOKUP_current_live_in:
  MEM l (fn_labels fn) ==>
  ALOOKUP (current_live_in fn) l =
    SOME (live_vars_at (liveness_analyze fn) l 0)
Proof
  simp[current_live_in_def, ALOOKUP_current_query_map]
QED

Theorem current_dom_tree_eq:
  current_dom_tree fn =
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
      case fn_entry_label fn of
        NONE => DNode "" []
      | SOME entry => current_dom_tree_aux dom (LENGTH (fn_labels fn)) entry
Proof
  simp[current_dom_tree_def]
QED

Theorem current_dom_postorder_eq:
  current_dom_postorder fn = dom_tree_postorder (current_dom_tree fn)
Proof
  simp[current_dom_postorder_def]
QED

val _ = export_theory();
