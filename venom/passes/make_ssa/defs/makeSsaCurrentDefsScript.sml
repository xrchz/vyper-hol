(*
 * Current-analysis, supply-safe MakeSSA adapter — definitions.
 *
 * This theory starts with the canonical analysis bridge.  The configured
 * MakeSSA implementation is kept separate from the legacy semantic model in
 * makeSsaDefs.
 *)

Theory makeSsaCurrentDefs
Ancestors
  makeSsaDefs cfgDefs dominatorDefs livenessDefs irSupply
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

(* ===== Supply-aware PHI insertion ===== *)

(* The ID is supplied explicitly by fresh_inst_id at the unique insertion
   point; this constructor contains no placeholder or arithmetic ID. *)
Definition build_phi_inst_supply_def:
  build_phi_inst_supply id var pred_labels =
    <| inst_id := id;
       inst_opcode := PHI;
       inst_operands := FLAT (MAP (\l. [Label l; Var var]) pred_labels);
       inst_outputs := [var] |>
End

Definition process_frontiers_supply_def:
  process_frontiers_supply s var pred_map live_in bbs rest has_phi [] =
    (bbs, rest, has_phi, s) /\
  process_frontiers_supply s var pred_map live_in bbs rest has_phi (f::fs) =
    if MEM f has_phi then
      process_frontiers_supply s var pred_map live_in bbs rest has_phi fs
    else
      let is_live = case ALOOKUP live_in f of
                      SOME vars => MEM var vars
                    | NONE => F in
      if ~is_live then
        process_frontiers_supply s var pred_map live_in bbs rest
                                 (f::has_phi) fs
      else
        let preds = case ALOOKUP pred_map f of SOME ps => ps | NONE => [] in
        let (id,s') = fresh_inst_id s in
        let phi = build_phi_inst_supply id var preds in
        let bbs' = MAP (\bb.
          if bb.bb_label = f then insert_phi_at_block phi bb else bb) bbs in
          process_frontiers_supply s' var pred_map live_in bbs'
                                   (f::rest) (f::has_phi) fs
End

Theorem process_frontiers_supply_labels:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  asm "ih" drule >>
  rw[MAP_MAP_o, insert_phi_at_block_def] >>
  irule MAP_CONG >> rw[]
QED

Triviality filter_add_mem_decrease_supply:
  !U (h:'a) hp.
    MEM h U /\ ~MEM h hp /\ ALL_DISTINCT U ==>
    LENGTH (FILTER (\x. ~MEM x (h::hp)) U) + 1 <=
    LENGTH (FILTER (\x. ~MEM x hp) U)
Proof
  Induct >> simp[ALL_DISTINCT] >> rpt strip_tac >> gvs[]
  >- (
    `LENGTH (FILTER (\x. x <> h /\ ~MEM x hp) U) <=
     LENGTH (FILTER (\x. ~MEM x hp) U)` suffices_by DECIDE_TAC >>
    irule LENGTH_FILTER_LEQ_MONO >> simp[])
  >- (
    Cases_on `MEM h hp`
    >- (`~(h <> h' /\ ~MEM h hp)` by simp[] >>
        `~(~MEM h hp)` by simp[] >>
        simp[] >> first_x_assum drule_all >> simp[])
    >- (`h <> h'` by metis_tac[MEM] >>
        simp[LENGTH] >> first_x_assum drule_all >> DECIDE_TAC))
QED

Triviality filter_weaken_exclusion_supply:
  !(U:'a list) hp1 hp2.
    (!x. MEM x hp1 ==> MEM x hp2) ==>
    LENGTH (FILTER (\x. ~MEM x hp2) U) <=
    LENGTH (FILTER (\x. ~MEM x hp1) U)
Proof
  Induct >> rw[FILTER] >> gvs[] >> res_tac >> DECIDE_TAC
QED

Triviality process_frontiers_supply_measure:
  !fs s var pm li bbs rest hp bbs' rest' hp' s' U.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    (!f. MEM f fs ==> MEM f U) ==>
    ALL_DISTINCT U ==>
    LENGTH (FILTER (\x. ~MEM x hp') U) + LENGTH rest' <=
    LENGTH (FILTER (\x. ~MEM x hp) U) + LENGTH rest
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (
    rpt strip_tac >>
    `!f. MEM f fs ==> MEM f U` by metis_tac[] >>
    asm "ih" (drule_then (qspec_then `U` mp_tac)) >>
    simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (
    rpt strip_tac >>
    `!f. MEM f fs ==> MEM f U` by metis_tac[] >>
    asm "ih" (drule_then (qspec_then `U` mp_tac)) >>
    (impl_tac >- simp[]) >> strip_tac >>
    `LENGTH (FILTER (\x. ~MEM x (h::hp)) U) <=
     LENGTH (FILTER (\x. ~MEM x hp) U)` by
      (irule filter_weaken_exclusion_supply >> simp[]) >>
    DECIDE_TAC)
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  `!f. MEM f fs ==> MEM f U` by metis_tac[] >>
  asm "ih" (drule_then (qspec_then `U` mp_tac)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `MEM h U` by metis_tac[] >>
  `LENGTH (FILTER (\x. ~MEM x (h::hp)) U) + 1 <=
   LENGTH (FILTER (\x. ~MEM x hp) U)` by
    (irule filter_add_mem_decrease_supply >> simp[]) >>
  gvs[LENGTH] >> DECIDE_TAC
QED


Definition insert_phis_for_var_supply_def:
  insert_phis_for_var_supply s var dom_frontiers pred_map live_in bbs [] has_phi =
    (bbs,s) /\
  insert_phis_for_var_supply s var dom_frontiers pred_map live_in bbs
                             (d::rest) has_phi =
    let frontiers = case ALOOKUP dom_frontiers d of
                      SOME fs => fs | NONE => [] in
    let (bbs',rest',has_phi',s') =
      process_frontiers_supply s var pred_map live_in bbs rest has_phi
                               frontiers in
      insert_phis_for_var_supply s' var dom_frontiers pred_map live_in
                                 bbs' rest' has_phi'
Termination
  WF_REL_TAC `measure (\(s,var,df,pm,li,bbs,wl,hp).
    LENGTH (FILTER (\x. ~MEM x hp)
      (nub (MAP (\bb. bb.bb_label) bbs ++ FLAT (MAP SND df)))) +
    LENGTH wl)` >>
  rpt strip_tac >>
  qabbrev_tac `fs = case ALOOKUP dom_frontiers d of
                      NONE => [] | SOME x => x` >>
  qabbrev_tac `U = nub (MAP (\bb. bb.bb_label) bbs ++
                         FLAT (MAP SND dom_frontiers))` >>
  qabbrev_tac `result = process_frontiers_supply s var pred_map live_in
                          bbs rest has_phi fs` >>
  `result = (bbs',rest',has_phi',s')` by
    simp[Abbr `result`, Abbr `fs`] >>
  pop_assum SUBST_ALL_TAC >> simp[] >>
  `process_frontiers_supply s var pred_map live_in bbs rest has_phi fs =
   (bbs',rest',has_phi',s')` by gvs[markerTheory.Abbrev_def] >>
  `MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs` by
    (irule process_frontiers_supply_labels >> metis_tac[]) >>
  `nub (MAP (\bb. bb.bb_label) bbs' ++ FLAT (MAP SND dom_frontiers)) = U` by
    simp[Abbr `U`] >>
  gvs[] >>
  `!f. MEM f fs ==> MEM f U` by (
    unabbrev_all_tac >> rpt strip_tac >>
    Cases_on `ALOOKUP dom_frontiers d` >> gvs[] >>
    simp[MEM_nub, MEM_APPEND, MEM_FLAT, MEM_MAP] >>
    disj2_tac >> qexists_tac `x` >> simp[] >>
    qexists_tac `(d,x)` >> simp[] >> metis_tac[ALOOKUP_MEM]) >>
  `ALL_DISTINCT U` by simp[Abbr `U`, all_distinct_nub] >>
  `LENGTH (FILTER (\x. ~MEM x has_phi') U) + LENGTH rest' <=
   LENGTH (FILTER (\x. ~MEM x has_phi) U) + LENGTH rest` by
    metis_tac[process_frontiers_supply_measure] >>
  DECIDE_TAC
End

Definition add_phi_nodes_supply_def:
  (add_phi_nodes_supply s dom_frontiers pred_map live_in bbs [] = (bbs,s)) /\
  (add_phi_nodes_supply s dom_frontiers pred_map live_in bbs
                        ((var,def_blocks)::defs) =
    let (bbs',s') = insert_phis_for_var_supply s var dom_frontiers pred_map
                                                live_in bbs def_blocks [] in
      add_phi_nodes_supply s' dom_frontiers pred_map live_in bbs' defs)
End

(* ===== Supply-aware concrete-name renaming ===== *)

Definition init_current_rename_state_def:
  init_current_rename_state defs =
    let vars = MAP FST defs in
      (MAP (\v. (v,0n)) vars, MAP (\v. (v,[v])) vars)
End

Definition latest_current_name_def:
  latest_current_name
    (counters : (string # num) list, stacks : (string # string list) list) var =
    case ALOOKUP stacks var of SOME (name::_) => name | _ => var
End

(* Counter zero is the original spelling and consumes no supply.  Every later
   definition gets its concrete spelling directly from fresh_ir_var. *)
Definition push_current_name_def:
  push_current_name s
    (counters : (string # num) list, stacks : (string # string list) list) var =
    let n = case ALOOKUP counters var of SOME k => k | NONE => 0n in
    let counters' = (var,n+1)::FILTER (\(v,_). v <> var) counters in
    if n = 0 then
      let stacks' = (var,var::case ALOOKUP stacks var of
                                SOME ns => ns | NONE => []) ::
                    FILTER (\(v,_). v <> var) stacks in
        ((counters',stacks'),s,var)
    else
      let (name,s') = fresh_ir_var s in
      let stacks' = (var,name::case ALOOKUP stacks var of
                                  SOME ns => ns | NONE => []) ::
                    FILTER (\(v,_). v <> var) stacks in
        ((counters',stacks'),s',name)
End

Definition rename_current_operands_def:
  (rename_current_operands rs [] = []) /\
  (rename_current_operands rs (Var v::ops) =
    Var (latest_current_name rs v)::rename_current_operands rs ops) /\
  (rename_current_operands rs (op::ops) =
    op::rename_current_operands rs ops)
End

Definition rename_current_outputs_def:
  (rename_current_outputs s rs [] = (rs,s,[]:string list)) /\
  (rename_current_outputs s rs (v::vs) =
    let (rs',s',name) = push_current_name s rs v in
    let (rs'',s'',rest) = rename_current_outputs s' rs' vs in
      (rs'',s'',name::rest))
End

Definition rename_current_inst_def:
  rename_current_inst s rs inst =
    if inst.inst_opcode = PHI then
      let (rs',s',outs') = rename_current_outputs s rs inst.inst_outputs in
        (rs',s',inst with inst_outputs := outs')
    else
      let ops' = rename_current_operands rs inst.inst_operands in
      let (rs',s',outs') = rename_current_outputs s rs inst.inst_outputs in
        (rs',s',inst with <| inst_operands := ops'; inst_outputs := outs' |>)
End

Definition rename_current_block_insts_def:
  (rename_current_block_insts s rs [] = (rs,s,[])) /\
  (rename_current_block_insts s rs (inst::rest) =
    let (rs',s',inst') = rename_current_inst s rs inst in
    let (rs'',s'',rest') = rename_current_block_insts s' rs' rest in
      (rs'',s'',inst'::rest'))
End

Definition update_current_phi_for_pred_def:
  (update_current_phi_for_pred rs current_label [] = []) /\
  (update_current_phi_for_pred rs current_label [x] = [x]) /\
  (update_current_phi_for_pred rs current_label (Label l::Var v::rest) =
    (if l = current_label
     then Label l::Var (latest_current_name rs v)::
          update_current_phi_for_pred rs current_label rest
     else Label l::Var v::update_current_phi_for_pred rs current_label rest)) /\
  (update_current_phi_for_pred rs current_label (x::y::rest) =
    x::y::update_current_phi_for_pred rs current_label rest)
End

Definition update_current_succ_phis_def:
  update_current_succ_phis rs current_label bbs succs =
    FOLDL (\bs lbl.
      case lookup_block lbl bs of
        NONE => bs
      | SOME bb =>
          let bb' = bb with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else inst with inst_operands :=
                          update_current_phi_for_pred rs current_label
                                                      inst.inst_operands)
                bb.bb_instructions in
            replace_block lbl bb' bs) bbs succs
End

Definition rename_current_blocks_def:
  (rename_current_blocks s rs bbs succ_map (DNode lbl children) =
    case lookup_block lbl bbs of
      NONE => (FST rs,s,bbs)
    | SOME bb =>
        let (rs1,s1,insts') =
          rename_current_block_insts s rs bb.bb_instructions in
        let bb' = bb with bb_instructions := insts' in
        let bbs1 = replace_block lbl bb' bbs in
        let succs = case ALOOKUP succ_map lbl of SOME ss => ss | NONE => [] in
        let bbs2 = update_current_succ_phis rs1 lbl bbs1 succs in
          rename_current_children s1 (FST rs1) (SND rs1) bbs2 succ_map
                                  children) /\
  (rename_current_children s ctrs stacks bbs succ_map [] = (ctrs,s,bbs)) /\
  (rename_current_children s ctrs stacks bbs succ_map (child::rest) =
    let (ctrs',s',bbs') =
      rename_current_blocks s (ctrs,stacks) bbs succ_map child in
      rename_current_children s' ctrs' stacks bbs' succ_map rest)
End

(* This boundary intentionally binds every analysis from this very fn. *)
Definition make_ssa_current_fn_def:
  make_ssa_current_fn s fn =
    case fn_entry_label fn of
      NONE => (fn,s)
    | SOME entry =>
        let cfg = cfg_analyze fn in
        let dom = dom_analyze cfg fn in
        let live = liveness_analyze fn in
        let pred_map = current_query_map (fn_labels fn) (cfg_preds_of cfg) in
        let succ_map = current_query_map (fn_labels fn) (cfg_succs_of cfg) in
        let frontiers = current_query_map (fn_labels fn) (frontier_of dom) in
        let live_in = current_query_map (fn_labels fn)
                                        (\l. live_vars_at live l 0) in
        let dtree = current_dom_tree_aux dom (LENGTH (fn_labels fn)) entry in
        let postorder = dom_tree_postorder dtree in
        let ordered_bbs = MAP THE (FILTER IS_SOME
          (MAP (\lbl. lookup_block lbl fn.fn_blocks) postorder)) in
        let defs = compute_defs ordered_bbs in
        let (bbs1,s1) = add_phi_nodes_supply s frontiers pred_map live_in
                                             fn.fn_blocks defs in
        let rs0 = init_current_rename_state defs in
        let (_,s2,bbs2) = rename_current_blocks s1 rs0 bbs1 succ_map dtree in
          (fn with fn_blocks := bbs2,s2)
End

Definition make_ssa_functions_supply_def:
  (make_ssa_functions_supply s [] = ([],s)) /\
  (make_ssa_functions_supply s (fn::fns) =
    let (fn',s') = make_ssa_current_fn s fn in
    let (fns',s'') = make_ssa_functions_supply s' fns in
      (fn'::fns',s''))
End

Definition make_ssa_ctx_supply_def:
  make_ssa_ctx_supply s ctx =
    let (fns,s') = make_ssa_functions_supply s ctx.ctx_functions in
      (ctx with ctx_functions := fns,s')
End

Definition make_ssa_unit_supply_def:
  make_ssa_unit_supply s unit =
    let (ctx,s') = make_ssa_ctx_supply s unit.cu_context in
      (unit with cu_context := ctx,s')
End

Definition make_ssa_configured_with_supply_def:
  make_ssa_configured_with_supply unit =
    make_ssa_unit_supply (init_ir_supply unit) unit
End

Definition make_ssa_configured_def:
  make_ssa_configured unit = FST (make_ssa_configured_with_supply unit)
End

Theorem make_ssa_configured_with_supply_eq:
  make_ssa_configured_with_supply unit =
    make_ssa_unit_supply (init_ir_supply unit) unit
Proof
  simp[make_ssa_configured_with_supply_def]
QED

Theorem make_ssa_configured_eq:
  make_ssa_configured unit = FST (make_ssa_configured_with_supply unit)
Proof
  simp[make_ssa_configured_def]
QED

Theorem make_ssa_current_fn_current_analysis_eq:
  make_ssa_current_fn s fn =
    case fn_entry_label fn of
      NONE => (fn,s)
    | SOME entry =>
        let cfg = cfg_analyze fn in
        let dom = dom_analyze cfg fn in
        let live = liveness_analyze fn in
        let pred_map = current_query_map (fn_labels fn) (cfg_preds_of cfg) in
        let succ_map = current_query_map (fn_labels fn) (cfg_succs_of cfg) in
        let frontiers = current_query_map (fn_labels fn) (frontier_of dom) in
        let live_in = current_query_map (fn_labels fn)
                                        (\l. live_vars_at live l 0) in
        let dtree = current_dom_tree_aux dom (LENGTH (fn_labels fn)) entry in
        let postorder = dom_tree_postorder dtree in
        let ordered_bbs = MAP THE (FILTER IS_SOME
          (MAP (\lbl. lookup_block lbl fn.fn_blocks) postorder)) in
        let defs = compute_defs ordered_bbs in
        let (bbs1,s1) = add_phi_nodes_supply s frontiers pred_map live_in
                                             fn.fn_blocks defs in
        let rs0 = init_current_rename_state defs in
        let (_,s2,bbs2) = rename_current_blocks s1 rs0 bbs1 succ_map dtree in
          (fn with fn_blocks := bbs2,s2)
Proof
  simp[make_ssa_current_fn_def]
QED

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
