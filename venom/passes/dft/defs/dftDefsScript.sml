(*
 * DFT (Depth-First Traversal) Pass — Definitions
 *
 * Reorders instructions within each basic block according to a depth-first
 * traversal of data and effect dependencies. Produces an instruction order
 * suitable for stack-based code generation.
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * TOP-LEVEL:
 *   producing_inst         — find instruction producing a variable
 *   inst_data_deps         — data dependencies for one instruction
 *   build_eda              — effect dependency analysis (incremental, with clearing)
 *   build_full_eda         — combined EDA with barrier/abort/alloca chains
 *   inst_all_deps          — combined DDA + EDA dependencies
 *   entry_instructions     — dependency DAG roots
 *   schedule_from_entries  — DFS schedule of a block's non-phi instructions
 *   dft_block              — transform a single block
 *   dft_fn                 — transform all blocks in a function
 *   dft_ctx                — transform all functions in a context
 *)

Theory dftDefs
Ancestors
  venomEffects venomWf stackOrderDefs livenessDefs passSharedDefs

(* ===== Effect Enumeration (deterministic) ===== *)

(* Python iterates Flag enum members in definition order.
   SET_TO_LIST has no specified order. This canonical enumeration
   matches Python's Flag member order for faithfulness. *)
Definition effects_to_list_def:
  effects_to_list effs =
    FILTER (\e. e IN effs)
      [Eff_STORAGE; Eff_TRANSIENT; Eff_MEMORY; Eff_FMP;
       Eff_IMMUTABLES; Eff_RETURNDATA; Eff_LOG; Eff_BALANCE; Eff_EXTCODE]
End

(* ===== Producing Instruction Lookup ===== *)

Definition producing_inst_def:
  producing_inst [] var = NONE ∧
  producing_inst (inst::rest) var =
    if MEM var inst.inst_outputs then SOME inst
    else producing_inst rest var
End

(* ===== Data Dependency Analysis (DDA) ===== *)

(* Data dependencies: inst depends on instructions that produce its operands.
   For terminators, also depends on stack-order vars.
   Returns a finite map: inst_id → list of dependency inst_ids *)
Definition operand_producer_def:
  operand_producer block_insts (Var v) = producing_inst block_insts v ∧
  operand_producer block_insts (Lit _) = NONE ∧
  operand_producer block_insts (Label _) = NONE
End

Definition inst_data_deps_def:
  inst_data_deps block_insts order inst =
    let var_deps = MAP THE (FILTER IS_SOME
      (MAP (operand_producer block_insts) inst.inst_operands)) in
    let order_deps =
      if is_terminator inst.inst_opcode
      then FILTER (\d. d.inst_id <> inst.inst_id)
             (MAP THE (FILTER IS_SOME (MAP (producing_inst block_insts) order)))
      else [] in
    nub (var_deps ++ order_deps)
End

(* ===== Effect Dependency Analysis (EDA) ===== *)

(* Python tracks last_write_effects and all_read_effects incrementally,
   clearing reads after a write. This matters: if A reads X, B writes X,
   then C writes X — only C depends on B (not A, which was cleared). *)

(* Effect tracking state *)
Datatype:
  effect_track = <|
    et_last_write : (effect, instruction) fmap;
    et_all_reads : (effect, instruction list) fmap
  |>
End

Definition empty_effect_track_def:
  empty_effect_track =
    <| et_last_write := FEMPTY; et_all_reads := FEMPTY |>
End

(* Get reads for an effect *)
Definition et_get_reads_def:
  et_get_reads et eff =
    case FLOOKUP et.et_all_reads eff of NONE => [] | SOME rs => rs
End

(* Compute effect deps for one instruction + update tracking state.
   Python: _calculate_dependency_graphs body *)
Definition compute_effect_deps_def:
  compute_effect_deps et inst =
    let w_effs = effects_to_list (write_effects inst.inst_opcode) in
    let r_effs = effects_to_list (read_effects inst.inst_opcode) in
    (* Python interleaves WAR + WAW per write effect (not all WAR then all WAW).
       This affects dep ordering in nub → EDA list → children → tiebreaker. *)
    let write_deps = FLAT (MAP (\weff.
      let war = et_get_reads et weff in
      let waw = case FLOOKUP et.et_last_write weff of
                      SOME w => [w] | NONE => [] in
      war ++ waw) w_effs) in
    (* RAW from reads *)
    let raw_deps = MAP THE (FILTER IS_SOME (MAP (\reff.
      case FLOOKUP et.et_last_write reff of
        SOME writer => if writer.inst_id <> inst.inst_id
                       then SOME writer else NONE
      | NONE => NONE) r_effs)) in
    let deps = nub (write_deps ++ raw_deps) in
    (* Update tracking state *)
    let et' = FOLDL (\acc weff.
      acc with <|
        et_last_write := acc.et_last_write |+ (weff, inst);
        (* Clear reads after write *)
        et_all_reads := acc.et_all_reads |+ (weff, [])
      |>) et w_effs in
    let et'' = FOLDL (\acc reff.
      acc with et_all_reads :=
        acc.et_all_reads |+ (reff, et_get_reads acc reff ++ [inst]))
      et' r_effs in
    (deps, et'')
End

(* Build EDA for a block: fold over non-phi instructions *)
Definition build_eda_def:
  build_eda block_insts =
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) block_insts in
    FST (FOLDL (\(acc_map, et) inst.
      let (deps, et') = compute_effect_deps et inst in
      (acc_map |+ (inst.inst_id, deps), et'))
    (FEMPTY, empty_effect_track) non_phis)
End

(* Generic: chain all instructions matching predicate P in original block
   order. Each matching instruction gets an EDA edge to the previous matching
   instruction, ensuring they are never reordered by DFT. *)
Definition add_chain_deps_def:
  add_chain_deps P block_insts eda =
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) block_insts in
    let matching = FILTER P non_phis in
    FST (FOLDL (\(acc, prev) inst.
      let old_deps = case FLOOKUP acc inst.inst_id of
                       NONE => [] | SOME ds => ds in
      let new_deps = case prev of
                       NONE => old_deps
                     | SOME p => if MEM p old_deps then old_deps
                                 else p :: old_deps in
      (acc |+ (inst.inst_id, new_deps), SOME inst))
    (eda, NONE) matching)
End

(* Instruction whose execution can fail (abort). *)
Definition is_fallible_def:
  is_fallible inst <=> opcode_fail_class inst.inst_opcode <> NoFail
End

(* Chain all fallible instructions so abort-incompatible pairs can never
   be reordered. Ensures abort_compatible for every reorderable pair.
   (Diverges from Python DFT which lacks this — upstream bug.) *)
Definition add_abort_deps_def:
  add_abort_deps block_insts eda =
    add_chain_deps is_fallible block_insts eda
End

(* Instruction whose opcode is ALLOCA. *)
Definition is_alloca_inst_def:
  is_alloca_inst inst <=> is_alloca_op inst.inst_opcode
End

(* Chain all ALLOCA instructions. exec_alloca uses vs_alloca_next as a
   bump-pointer allocator, making results order-dependent. The effects
   system does not model this implicit state dependency. *)
Definition add_alloca_deps_def:
  add_alloca_deps block_insts eda =
    add_chain_deps is_alloca_inst block_insts eda
End

(* Barrier predicate: instructions that bi_independent cannot handle.
   Volatile ops (INVOKE, ext_call, MSTORE, ...), alloca ops, and raw FMP ops
   have implicit state dependencies that must be ordered conservatively. *)
Definition is_barrier_def:
  is_barrier inst <=>
    is_volatile inst.inst_opcode \/
    is_alloca_op inst.inst_opcode \/
    is_raw_fmp_opcode inst.inst_opcode
End

(* Pass 1: each non-phi after a barrier gets that barrier as a dep.
   Tracks only last_barrier — simple 2-component FOLDL. *)
Definition add_deps_on_barrier_def:
  add_deps_on_barrier block_insts eda =
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) block_insts in
    FST (FOLDL (\(acc, last_bar) inst.
      let old_deps = case FLOOKUP acc inst.inst_id of
                       NONE => [] | SOME ds => ds in
      if is_barrier inst then
        (acc, SOME inst)
      else
        let new_deps = case last_bar of
                         NONE => old_deps
                       | SOME b => if MEM b old_deps then old_deps
                                   else b :: old_deps in
        (acc |+ (inst.inst_id, new_deps), last_bar))
    (eda, NONE) non_phis)
End

(* Pass 2: each barrier depends on ALL preceding non-phis.
   Uses add_chain_deps pattern but adds ALL prev non-phis, not just matching.
   Tracks only prev_insts — simple 2-component FOLDL. *)
Definition add_deps_from_barrier_def:
  add_deps_from_barrier block_insts eda =
    let non_phis = FILTER (\i. ~is_pseudo i.inst_opcode) block_insts in
    FST (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        let old_deps = case FLOOKUP acc inst.inst_id of
                         NONE => [] | SOME ds => ds in
        let new_deps = FOLDL (\ds p.
              if MEM p ds then ds else p :: ds) old_deps prev_insts in
        (acc |+ (inst.inst_id, new_deps), prev_insts ++ [inst])
      else
        (acc, prev_insts ++ [inst]))
    (eda, []) non_phis)
End

(* Combined barrier deps: both passes *)
Definition add_barrier_deps_def:
  add_barrier_deps block_insts eda =
    add_deps_from_barrier block_insts
      (add_deps_on_barrier block_insts eda)
End

Definition build_full_eda_def:
  build_full_eda block_insts =
    add_alloca_deps block_insts
      (add_barrier_deps block_insts
        (add_abort_deps block_insts (build_eda block_insts)))
End


(* ===== Combined Dependencies ===== *)

Definition inst_all_deps_def:
  inst_all_deps block_insts order eda inst =
    let dda = inst_data_deps block_insts order inst in
    let eda_deps = case FLOOKUP eda inst.inst_id of
                     NONE => [] | SOME ds => ds in
    nub (dda ++ eda_deps)
End

(* ===== Data Offspring (transitive closure of DDA) ===== *)

(* Python: _calculate_data_offspring — transitive closure of data deps.
   Used in cost function to distinguish effect-only deps with/without
   data children.
   Structural termination: DDA deps are always earlier instructions in
   the block (producers before uses under SSA). Processing instructions
   front-to-back guarantees all deps are already in the offspring map. *)
Definition build_offspring_map_def:
  build_offspring_map block_insts order =
    FOLDL (λacc inst.
      if is_pseudo inst.inst_opcode then acc
      else
        let direct = inst_data_deps block_insts order inst in
        let transitive = FLAT (MAP (λd.
          case FLOOKUP acc d.inst_id of
            SOME offs => offs
          | NONE => []) direct) in
        acc |+ (inst.inst_id, nub (direct ++ transitive)))
    FEMPTY block_insts
End

(* ===== Entry Instructions ===== *)

Definition entry_instructions_def:
  entry_instructions block_insts order eda =
    let non_phis = FILTER (λi. ¬is_pseudo i.inst_opcode) block_insts in
    let all_dep_ids = nub (FLAT
      (MAP (λi. MAP (λd. d.inst_id)
                     (inst_all_deps block_insts order eda i))
           non_phis)) in
    FILTER (λi. ¬MEM i.inst_id all_dep_ids) non_phis
End

(* ===== Operand Flipping ===== *)

(* Python: inst.flippable = is_commutative or is_comparator.
   is_commutative is inherited from venomEffectsTheory.
   is_comparator is inherited from passSharedDefsTheory. *)

Definition is_flippable_def:
  is_flippable op <=> is_commutative op \/ is_comparator op
End

(* flip_comparison_opcode is inherited from passSharedDefsTheory *)

Definition flip_operands_def:
  flip_operands inst =
    case inst.inst_operands of
      [a; b] =>
        let swapped = inst with inst_operands := [b; a] in
        if is_comparator inst.inst_opcode
        then swapped with inst_opcode := flip_comparison_opcode inst.inst_opcode
        else swapped
    | _ => inst
End

(* ===== Cost Function for Child Ordering ===== *)

(* Python: cost() in _process_instruction_r.
   Determines child traversal order in DFS.
   Python costs (can be negative):
     effect-only with data offspring: -1
     effect-only without data offspring: 0
     order position match: position (0..len(order)-1)
     direct operand match: operand_idx + len(order)
     fallback: len(order)
   We shift all costs by +1 for num (natural numbers):
     -1→0, 0→1, position→position+1, idx+len→idx+len+1, len→len+1 *)
Definition dft_cost_def:
  dft_cost block_insts order eda offspring_map parent child =
    let dda = inst_data_deps block_insts order parent in
    let is_effect_only = ~MEM child dda in
    (* Python: if is_effect_only or inst.flippable — for flippable
       instructions, ALL children get the simple offspring-based cost,
       not just effect-only deps. *)
    if is_effect_only \/ is_flippable parent.inst_opcode then
      let has_offspring =
        case FLOOKUP offspring_map child.inst_id of
          SOME offs => offs <> []
        | NONE => F in
      if has_offspring then 0:num  (* maps to -1 in Python, but we use num *)
      else 1
    else
      (* Data dep: find operand index *)
      (* REVERSE: HOL4 stores operands in EVM semantic order but Python
         iterates in stack-push order (reversed). REVERSE aligns indices
         so index 0 = deepest on stack = lowest cost. *)
      let op_idxs = MAP THE (FILTER IS_SOME
        (MAPi (\i op.
          case operand_producer block_insts op of
            SOME prod => if prod.inst_id = child.inst_id then SOME i
                         else NONE
          | NONE => NONE) (REVERSE parent.inst_operands))) in
      (* Python cost = idx + len(order); shifted +1 for num: idx + len(order) + 1 *)
      case op_idxs of
        idx :: _ => idx + LENGTH order + 1
      | [] =>
        (* Fallback: check if child's outputs appear directly in parent's
           operands. Python path 2: x.get_outputs() in inst.operands.
           Equivalent to path 1 under SSA, but kept for faithfulness. *)
        let output_idxs = MAP THE (FILTER IS_SOME
          (MAPi (\i op.
            case op of
              Var v => if MEM v child.inst_outputs then SOME i else NONE
            | Lit _ => NONE
            | Label _ => NONE) (REVERSE parent.inst_operands))) in
        case output_idxs of
          idx :: _ => idx + LENGTH order + 1
        | [] =>
        (* Python cost = order_position; shifted +1: position + 1 *)
        let order_idxs = MAP THE (FILTER IS_SOME
          (MAPi (\i v.
            if MEM v child.inst_outputs then SOME i else NONE)
            order)) in
        case order_idxs of
          idx :: _ => idx + 1
        | [] => LENGTH order + 1
End

(* Sort children by cost. Lower cost = processed first in DFS
   (will appear earlier in output = deeper in stack).
   Python uses stable sort; we emulate stability via decorate-sort-undecorate:
   pair each child with its original index, sort by (cost, index), strip. *)
Definition sort_children_def:
  sort_children block_insts order eda offspring_map parent children =
    let indexed = MAPi (\i c. (i, c)) children in
    let sorted = QSORT (\(i1,c1) (i2,c2).
      let cost1 = dft_cost block_insts order eda offspring_map parent c1 in
      let cost2 = dft_cost block_insts order eda offspring_map parent c2 in
      cost1 < cost2 \/ (cost1 = cost2 /\ i1 <= i2)) indexed in
    MAP SND sorted
End

(* ===== DFS Scheduling ===== *)

(* Iterative DFS using an explicit work-item stack.
   DfsProcess: visit an instruction (may push children + DfsEmit).
   DfsEmit: append instruction to output.
   Structural termination via FUNPOW over a bounded step count. *)
Datatype:
  dfs_work_item = DfsProcess instruction | DfsEmit instruction
End

Datatype:
  dfs_state = <|
    ds_stack : dfs_work_item list;
    ds_output : instruction list;
    ds_visited : num list
  |>
End

Definition dfs_step_def:
  dfs_step block_insts order eda offspring_map do_flip state =
    case state.ds_stack of
      [] => state
    | DfsEmit inst :: rest =>
        state with <| ds_stack := rest;
                      ds_output := state.ds_output ++ [inst] |>
    | DfsProcess inst :: rest =>
        if MEM inst.inst_id state.ds_visited then
          state with ds_stack := rest
        else if is_pseudo inst.inst_opcode then
          state with <| ds_stack := rest;
                        ds_visited := inst.inst_id :: state.ds_visited |>
        else
          let visited' = inst.inst_id :: state.ds_visited in
          let children = inst_all_deps block_insts order eda inst in
          let sorted = sort_children block_insts order eda offspring_map
                                     inst children in
          let inst' = if do_flip ∧ is_flippable inst.inst_opcode ∧
                         sorted ≠ children
                      then flip_operands inst else inst in
          let child_work = MAP DfsProcess sorted in
          state with <| ds_stack := child_work ++ [DfsEmit inst'] ++ rest;
                        ds_visited := visited' |>
End

(* Bound: N process steps + N emit steps + ≤ N² skip steps + ≤ N initial
   entries = N² + 2N total steps. Use (N+1)² for clean expression. *)
Definition schedule_from_entries_def:
  schedule_from_entries block_insts order eda offspring_map entries =
    let n = LENGTH block_insts in
    let init = <| ds_stack := MAP DfsProcess entries;
                  ds_output := [];
                  ds_visited := [] |> in
    let final = FUNPOW (dfs_step block_insts order eda offspring_map T)
                       ((n + 1) * (n + 1)) init in
    final.ds_output
End

(* ===== Block-Level Transform ===== *)

Definition dft_block_def:
  dft_block order bb =
    let phis = FILTER (λi. is_pseudo i.inst_opcode) bb.bb_instructions in
    let eda = build_full_eda bb.bb_instructions in
    let offspring_map = build_offspring_map bb.bb_instructions order in
    let entries = entry_instructions bb.bb_instructions order eda in
    let scheduled = schedule_from_entries bb.bb_instructions order
                      eda offspring_map entries in
    bb with bb_instructions := phis ++ scheduled
End


(* ===== Function-Level Transform with StackOrder Convergence ===== *)

(* Python: run_pass convergence loop state *)
Datatype:
  dft_loop_state = <|
    dls_blocks : basic_block list;  (* current function blocks *)
    dls_from_to : (string # string, string list) fmap;  (* stack order from_to *)
    dls_last_order : (string, string list) fmap  (* last order per block *)
  |>
End

(* Process one block in the worklist: analyze, check convergence, schedule.
   Returns (updated_state, converged, preds_to_add).
   Python: body of while loop in run_pass *)
Definition dft_process_one_def:
  dft_process_one cfg lr fn st lbl =
    (* Use current (possibly scheduled) blocks, not original fn.fn_blocks.
       Python modifies bb.instructions in-place during the loop. *)
    let cur_fn = fn with fn_blocks := st.dls_blocks in
    (* Python: self.stack_order.analyze_bb(bb)
       This records from_to for (pred, bb) edges *)
    case lookup_block lbl st.dls_blocks of
      NONE => (st, T, [])  (* block not found: treat as converged *)
    | SOME bb =>
        let (needed, _) =
          so_analyze_block cfg lr st.dls_from_to lbl bb.bb_instructions in
        let from_to' =
          so_record_from_to cfg st.dls_from_to lbl needed in
        (* Python: order = self.stack_order.get_stack(bb)
           Uses cur_fn so successors are looked up from current blocks *)
        let (order, from_to'') =
          so_get_stack cfg lr cur_fn from_to' lbl in
        (* Python: if bb in last_order and last_order[bb] == order: break *)
        let converged =
          case FLOOKUP st.dls_last_order lbl of
            SOME prev => prev = order
          | NONE => F in
        if converged then
          (st with dls_from_to := from_to'', T, [])
        else
          (* Python: self.order = list(reversed(order)) *)
          let rev_order = REVERSE order in
          (* Python: self._process_basic_block(bb) — schedule with this order *)
          let bb' = dft_block rev_order bb in
          let blocks' = MAP (λb. if b.bb_label = lbl then bb' else b)
                            st.dls_blocks in
          let st' = st with <|
            dls_blocks := blocks';
            dls_from_to := from_to'';
            dls_last_order := st.dls_last_order |+ (lbl, order)
          |> in
          (* Python: for pred in self.cfg.cfg_in(bb): worklist.append(pred) *)
          (st', F, cfg_preds_of cfg lbl)
End

(* Worklist loop step function.
   Python: body of while loop in run_pass *)
Definition dft_loop_step_def:
  dft_loop_step cfg lr fn (st, worklist, done) =
    if done then (st, worklist, T)
    else case worklist of
      [] => (st, [], T)
    | lbl :: rest =>
        let (st', converged, preds) =
          dft_process_one cfg lr fn st lbl in
        if converged then (st', [], T)  (* Python: break *)
        else (st', rest ++ preds, F)
End

(* Full function transform: build CFG, compute liveness, run convergence loop.
   Python: run_pass.
   Structural termination: FUNPOW applies a fixed number of steps
   computed from block count. In practice the loop converges in ≤ N
   iterations; N² gives margin for re-processing via predecessors. *)
Definition dft_fn_def:
  dft_fn fn =
    let cfg = cfg_analyze fn in
    let lr = liveness_analyze fn in
    let worklist = cfg.cfg_dfs_post in
    let init_st = <|
      dls_blocks := fn.fn_blocks;
      dls_from_to := FEMPTY;
      dls_last_order := FEMPTY
    |> in
    let n = LENGTH fn.fn_blocks in
    let (final_st, _, _) =
      FUNPOW (dft_loop_step cfg lr fn) (n * n) (init_st, worklist, F) in
    fn with fn_blocks := final_st.dls_blocks
End

Definition dft_ctx_def:
  dft_ctx ctx =
    ctx with ctx_functions := MAP dft_fn ctx.ctx_functions
End
