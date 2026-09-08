(*
 * Concretize Memory Locations — Definitions
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 *
 * Replaces abstract memory allocation instructions (alloca)
 * with concrete ASSIGN of computed memory offsets.
 *
 * TOP-LEVEL:
 *   mem_liveness_analyze  — MemLiveness analysis (liveat ∩ used)
 *   compute_alloc_map     — first-fit allocator with liveness-aware reservation
 *   concretize_inst       — per-instruction transform
 *   concretize_function   — function-level transform (allocate + rewrite)
 *   concretize_context_eval — evaluator-friendly sequential allocation
 *)

Theory concretizeMemLocDefs
Ancestors
  staticLayoutDefs passSimulationDefs passSharedDefs basePtrDefs cfgDefs enumeral toto

(* ===== Allocation map ===== *)

(* Maps alloca output variable names to their concrete memory offsets *)
Type alloc_map = ``:(string, 256 word) fmap``

(* ===== Sorted list comparators for allocation and inst_addr ===== *)

Definition alloc_cmp_def:
  alloc_cmp (Allocation m) (Allocation n) = apto numto m n
End

Definition alloc_to_def:
  alloc_to = TO alloc_cmp
End

Definition inst_addr_to_def:
  inst_addr_to = stringto lextoto numto
End

(* =========================================================================
   Helpers: memory read/write queries for MemLiveness
   ========================================================================= *)

(* Find base allocations referenced by an operand, using bp_result.
   Matches Python MemLiveness._find_base_ptrs. *)
Definition find_base_allocas_def:
  find_base_allocas (bpr : bp_result) op =
    case op of
      Var v => incr_ssort alloc_to
                 (MAP (\p. case p of Ptr alloc _ => alloc)
                      (bp_get_ptrs bpr v))
    | _ => []
End

Definition find_base_allocas_opt_def:
  find_base_allocas_opt bpr NONE = [] /\
  find_base_allocas_opt bpr (SOME op) = find_base_allocas bpr op
End

(* Get write operand (offset) of an instruction *)
Definition inst_write_op_def:
  inst_write_op inst =
    case mem_write_ops inst of
      NONE => NONE
    | SOME ops => SOME ops.iao_ofst
End

(* Get read operand (offset) of an instruction *)
Definition inst_read_op_def:
  inst_read_op inst =
    case mem_read_ops inst of
      NONE => NONE
    | SOME ops => SOME ops.iao_ofst
End

(* Get write size as a number, if literal *)
Definition inst_write_size_def:
  inst_write_size inst =
    case mem_write_ops inst of
      NONE => NONE
    | SOME ops =>
        case ops.iao_size of
          SOME (Lit n) => SOME (w2n n)
        | _ => NONE
End

(* Get alloca size from first operand *)
Definition inst_alloca_size_def:
  inst_alloca_size inst =
    case inst.inst_operands of
      Lit sz :: _ => SOME (w2n sz)
    | _ => NONE
End

(* =========================================================================
   MemLiveness Analysis
   Ports Python MemLiveness class.

   Two simultaneous dataflow analyses:
   1. liveat (backward): which allocations could still be needed
   2. used (forward): which allocations have been referenced

   An allocation is live at an instruction iff in both liveat and used.

   State indexed by (block_label, instruction_index).
   ========================================================================= *)

Type inst_addr = ``:string # num``
Type ml_state[pp] = ``:(inst_addr, allocation list) fmap``

Definition ml_lookup_def:
  ml_lookup (st : ml_state) (addr : inst_addr) =
    case FLOOKUP st addr of SOME s => s | NONE => []
End

(* ===== liveat helpers ===== *)

(* Kill an alloca from live set if write completely covers it and
   the instruction doesn't also read it. Re-add if it also reads. *)
Definition ml_kill_write_def:
  ml_kill_write alloca_sizes read_allocas wsz live alloc =
    case alloca_sizes alloc of
      NONE => live
    | SOME asz =>
        if MEM alloc live /\ wsz = asz /\ ~MEM alloc read_allocas
        then sdiff alloc_to live [alloc]
        else if MEM alloc read_allocas then smerge alloc_to [alloc] live
        else live
End

(* Process one instruction for liveat (called in reverse order).
   Returns (new_live_set, updated_liveat_state). *)
Definition ml_liveat_inst_def:
  ml_liveat_inst bpr mems_used alloca_sizes bb_label
                 idx inst live (la : ml_state) =
    let write_allocas = find_base_allocas_opt bpr (inst_write_op inst) in
    let read_allocas = find_base_allocas_opt bpr (inst_read_op inst) in
    let live1 = smerge alloc_to live read_allocas in
    (* INVOKE: add callee mems_used + all operand base ptrs *)
    let live2 =
      if inst.inst_opcode = INVOKE then
        (case inst.inst_operands of
           Label callee_lbl :: _ =>
             smerge alloc_to live1
               (smerge alloc_to (mems_used callee_lbl)
                 (FOLDL (smerge alloc_to) []
                   (MAP (find_base_allocas bpr) inst.inst_operands)))
         | _ => live1)
      else live1 in
    let la' = la |+ ((bb_label, idx), live2) in
    (* Complete-overwrite kill *)
    let live3 = case inst_write_size inst of
      NONE => live2
    | SOME wsz =>
        FOLDL (ml_kill_write alloca_sizes read_allocas wsz)
              live2 write_allocas in
    (live3, la')
End

(* Process a block's instructions in reverse for liveat *)
Definition ml_liveat_insts_rev_def:
  ml_liveat_insts_rev bpr mems_used alloca_sizes bb_label
                      live la [] = (live, la) /\
  ml_liveat_insts_rev bpr mems_used alloca_sizes bb_label
                      live la ((idx, inst) :: rest) =
    (* Process rest first (they come later in the block) *)
    let (live', la') = ml_liveat_insts_rev bpr mems_used
                         alloca_sizes bb_label live la rest in
    ml_liveat_inst bpr mems_used alloca_sizes bb_label
                   idx inst live' la'
End

(* Process one block for liveat. Returns (changed, new_liveat). *)
Definition ml_liveat_block_def:
  ml_liveat_block bpr mems_used alloca_sizes cfg
                  (liveat : ml_state) bb =
    let succs = cfg_succs_of cfg bb.bb_label in
    let live_init = FOLDL (smerge alloc_to) []
      (MAP (\lbl. ml_lookup liveat (lbl, 0)) succs) in
    let before = ml_lookup liveat (bb.bb_label, 0) in
    let indexed = MAPi (\i inst. (i, inst)) bb.bb_instructions in
    let (_, liveat') = ml_liveat_insts_rev bpr mems_used
                         alloca_sizes bb.bb_label live_init liveat
                         indexed in
    (ml_lookup liveat' (bb.bb_label, 0) <> before, liveat')
End

(* ===== used helpers ===== *)

(* Process one instruction for used (forward order). *)
Definition ml_used_inst_def:
  ml_used_inst bpr mems_used bb_label
               idx inst cur_used (us : ml_state) =
    let new_used = smerge alloc_to cur_used
      (FOLDL (smerge alloc_to) []
        (MAP (find_base_allocas bpr) inst.inst_operands)) in
    let new_used2 =
      if inst.inst_opcode = INVOKE then
        (case inst.inst_operands of
           Label callee_lbl :: _ => smerge alloc_to new_used (mems_used callee_lbl)
         | _ => new_used)
      else new_used in
    (new_used2, us |+ ((bb_label, idx), new_used2))
End

(* Process a block's instructions forward for used *)
Definition ml_used_insts_def:
  ml_used_insts bpr mems_used bb_label
                cur_used us [] = (cur_used, us) /\
  ml_used_insts bpr mems_used bb_label
                cur_used us ((idx, inst) :: rest) =
    let (cur', us') = ml_used_inst bpr mems_used bb_label
                        idx inst cur_used us in
    ml_used_insts bpr mems_used bb_label cur' us' rest
End

(* Process one block for used. Returns (changed, new_used). *)
Definition ml_used_block_def:
  ml_used_block bpr mems_used live_pallocas cfg
                (used : ml_state) bb fn_blocks =
    let preds = cfg_preds_of cfg bb.bb_label in
    let used_init = smerge alloc_to live_pallocas
      (FOLDL (smerge alloc_to) [] (MAP (\lbl.
        case FIND (\b. b.bb_label = lbl) fn_blocks of
          NONE => ml_lookup used (lbl, 0)
        | SOME pred_bb =>
            ml_lookup used (pred_bb.bb_label,
                            PRE (LENGTH pred_bb.bb_instructions)))
        preds)) in
    let n = LENGTH bb.bb_instructions in
    let before = ml_lookup used (bb.bb_label, PRE n) in
    let indexed = MAPi (\i inst. (i, inst)) bb.bb_instructions in
    let (_, used') = ml_used_insts bpr mems_used bb.bb_label
                       used_init used indexed in
    (ml_lookup used' (bb.bb_label, PRE n) <> before, used')
End

(* ===== Fixpoint iteration ===== *)

(* One pass: liveat over post-order, used over pre-order *)
Definition ml_one_pass_liveat_def:
  ml_one_pass_liveat bpr mems_used alloca_sizes cfg blocks
                     [] la = (F, la) /\
  ml_one_pass_liveat bpr mems_used alloca_sizes cfg blocks
                     (lbl :: lbls) la =
    case FIND (\bb. bb.bb_label = lbl) blocks of
      NONE => ml_one_pass_liveat bpr mems_used alloca_sizes
                cfg blocks lbls la
    | SOME bb =>
        let (c1, la') = ml_liveat_block bpr mems_used
                          alloca_sizes cfg la bb in
        let (c2, la'') = ml_one_pass_liveat bpr mems_used
                           alloca_sizes cfg blocks lbls la' in
        (c1 \/ c2, la'')
End

Definition ml_one_pass_used_def:
  ml_one_pass_used bpr mems_used live_pallocas cfg blocks
                   [] us = (F, us) /\
  ml_one_pass_used bpr mems_used live_pallocas cfg blocks
                   (lbl :: lbls) us =
    case FIND (\bb. bb.bb_label = lbl) blocks of
      NONE => ml_one_pass_used bpr mems_used live_pallocas
                cfg blocks lbls us
    | SOME bb =>
        let (c1, us') = ml_used_block bpr mems_used
                          live_pallocas cfg us bb blocks in
        let (c2, us'') = ml_one_pass_used bpr mems_used
                           live_pallocas cfg blocks lbls us' in
        (c1 \/ c2, us'')
End

Definition ml_one_pass_def:
  ml_one_pass bpr mems_used alloca_sizes live_pallocas cfg fn
              la us =
    let (c1, la') = ml_one_pass_liveat bpr mems_used alloca_sizes
                      cfg fn.fn_blocks cfg.cfg_dfs_post la in
    let (c2, us') = ml_one_pass_used bpr mems_used live_pallocas
                      cfg fn.fn_blocks cfg.cfg_dfs_pre us in
    (c1 \/ c2, la', us')
End

(* Iterate until fixpoint via OWHILE *)
Definition ml_iterate_def:
  ml_iterate bpr mems_used alloca_sizes live_pallocas cfg fn =
    OWHILE
      (\(changed, la, us). changed)
      (\(_, la, us).
        ml_one_pass bpr mems_used alloca_sizes live_pallocas
                    cfg fn la us)
      (T, FEMPTY, FEMPTY)
End

(* ===== Compute livesets from liveat ∩ used ===== *)

Definition ml_livesets_insts_def:
  ml_livesets_insts bb_label liveat used ls [] = ls /\
  ml_livesets_insts bb_label liveat used ls ((idx, inst) :: rest) =
    let addr = (bb_label, idx) in
    let both = sinter alloc_to (ml_lookup liveat addr) (ml_lookup used addr) in
    let ls' = FOLDL (\m alloc.
      let cur = case FLOOKUP m alloc of SOME s => s | NONE => [] in
      m |+ (alloc, smerge inst_addr_to [addr] cur))
      ls both in
    ml_livesets_insts bb_label liveat used ls' rest
End

Definition ml_compute_livesets_def:
  ml_compute_livesets liveat used fn =
    FOLDL (\ls bb.
      ml_livesets_insts bb.bb_label liveat used ls
        (MAPi (\i inst. (i, inst)) bb.bb_instructions))
      (FEMPTY : (allocation, inst_addr list) fmap)
      fn.fn_blocks
End

(* Mark store locations live *)
Definition ml_mark_stores_insts_def:
  ml_mark_stores_insts bpr bb_label ls [] = ls /\
  ml_mark_stores_insts bpr bb_label ls ((idx, inst) :: rest) =
    let write_allocas = find_base_allocas_opt bpr (inst_write_op inst) in
    let addr = (bb_label, idx) in
    let ls' = FOLDL (\m alloc.
      let cur = case FLOOKUP m alloc of SOME s => s | NONE => [] in
      m |+ (alloc, smerge inst_addr_to [addr] cur))
      ls write_allocas in
    ml_mark_stores_insts bpr bb_label ls' rest
End

Definition ml_mark_stores_live_def:
  ml_mark_stores_live bpr fn ls =
    FOLDL (\ls' bb.
      ml_mark_stores_insts bpr bb.bb_label ls'
        (MAPi (\i inst. (i, inst)) bb.bb_instructions))
      ls fn.fn_blocks
End

(* Top-level MemLiveness *)
Definition mem_liveness_analyze_def:
  mem_liveness_analyze bpr mems_used alloca_sizes
                       live_pallocas cfg fn =
    case ml_iterate bpr mems_used alloca_sizes
           live_pallocas cfg fn of
      SOME (_, liveat, used) =>
        ml_mark_stores_live bpr fn
          (ml_compute_livesets liveat used fn)
    | NONE => FEMPTY
End

(* =========================================================================
   Fuel-Bounded Evaluation Helpers
   ========================================================================= *)

Definition bp_iterate_fuel_def:
  bp_iterate_fuel 0 fn order result = result ∧
  bp_iterate_fuel (SUC fuel) fn order result =
    let (changed, result') = bp_one_pass fn order result in
    if changed then bp_iterate_fuel fuel fn order result'
    else result'
End

Definition bp_analyze_fuel_def:
  bp_analyze_fuel fuel cfg fn =
    bp_iterate_fuel fuel fn cfg.cfg_dfs_pre FEMPTY
End

Definition ml_iterate_fuel_def:
  ml_iterate_fuel 0 bpr mems_used alloca_sizes live_pallocas cfg fn
                  liveat used = (liveat, used) ∧
  ml_iterate_fuel (SUC fuel) bpr mems_used alloca_sizes live_pallocas cfg fn
                  liveat used =
    let (changed, liveat', used') =
      ml_one_pass bpr mems_used alloca_sizes live_pallocas cfg fn
        liveat used in
    if changed then
      ml_iterate_fuel fuel bpr mems_used alloca_sizes live_pallocas
        cfg fn liveat' used'
    else (liveat', used')
End

Definition mem_liveness_analyze_fuel_def:
  mem_liveness_analyze_fuel fuel bpr mems_used alloca_sizes
                            live_pallocas cfg fn =
    let (liveat, used) =
      ml_iterate_fuel fuel bpr mems_used alloca_sizes
        live_pallocas cfg fn FEMPTY FEMPTY in
    ml_mark_stores_live bpr fn
      (ml_compute_livesets liveat used fn)
End

(* =========================================================================
   First-Fit Allocator
   Ports Python MemoryAllocator.allocate + run_pass allocation loop.
   ========================================================================= *)

(* Find first position >= start fitting in gap between reserved regions.
   Reserved must be sorted by position ascending. *)
Definition first_fit_pos_def:
  first_fit_pos (reserved : (num # num) list) (size : num) (start : num) =
    case reserved of
      [] => start
    | (rpos, rsz) :: rest =>
        if rpos + rsz <= start then first_fit_pos rest size start
        else if start + size <= rpos then start
        else first_fit_pos rest size (rpos + rsz)
End

(* Get alloca size from function's instructions *)
Definition get_alloca_size_def:
  get_alloca_size fn (Allocation aid) =
    case FIND (\inst. is_alloca_op inst.inst_opcode /\ inst.inst_id = aid)
              (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)) of
      SOME inst => (case inst.inst_operands of
                      Lit sz :: _ => w2n sz
                    | _ => 0)
    | NONE => 0
End

(* Allocate one: first-fit among sorted reserved regions *)
Definition allocate_one_def:
  allocate_one (reserved : (num # num) list) (size : num) =
    let sorted = QSORT (\(p1:num,_) (p2,_). p1 <= p2) reserved in
    let pos = first_fit_pos sorted size 0 in
    (pos, (pos, size) :: reserved)
End


(* =========================================================================
   Checked static-ALLOCA completion helpers
   ========================================================================= *)

(* Unlike inst_alloca_size/get_alloca_size, this accepts only the exact source
   shape consumed by checked concretization. *)
Definition exact_static_alloca_size_def:
  exact_static_alloca_size inst =
    if inst.inst_opcode = ALLOCA then
      case (inst.inst_operands, inst.inst_outputs) of
        ([Lit sz], [_]) => SOME (w2n sz)
      | _ => NONE
    else NONE
End

(* Collect source allocation identities and sizes in instruction order, while
   rejecting both malformed ALLOCAs and duplicate instruction identities. *)
Definition exact_static_alloca_def:
  exact_static_alloca inst =
    case exact_static_alloca_size inst of
      NONE => NONE
    | SOME sz => SOME ((Allocation inst.inst_id), sz)
End

Definition collect_static_allocas_def:
  collect_static_allocas ([] : instruction list) =
    SOME ([] : (allocation # num) list) /\
  collect_static_allocas (inst::insts) =
    case collect_static_allocas insts of
      NONE => NONE
    | SOME items =>
        if inst.inst_opcode = ALLOCA then
          case exact_static_alloca inst of
            NONE => NONE
          | SOME item =>
              if MEM (FST item) (MAP FST items) then NONE
              else SOME (item::items)
        else SOME items
End

Definition static_alloca_items_def:
  static_alloca_items fn = collect_static_allocas (fn_insts fn)
End

Definition allocation_id_def:
  allocation_id (Allocation aid) = aid
End

Definition forced_alloc_keys_valid_def:
  forced_alloc_keys_valid allocs (forced : (num,num) fmap) <=>
    FDOM forced SUBSET LIST_TO_SET (MAP allocation_id allocs)
End

Definition candidate_alloc_keys_valid_def:
  candidate_alloc_keys_valid allocs
      (positions : (allocation,num) fmap) <=>
    FDOM positions SUBSET LIST_TO_SET allocs
End

(* Forced positions augment a candidate map, but never silently override it.
   Iterate over authoritative source items, avoiding finite-map enumeration. *)
Definition merge_forced_positions_def:
  merge_forced_positions [] forced positions = SOME positions /\
  merge_forced_positions ((alloc,sz)::rest) forced positions =
    case FLOOKUP forced (allocation_id alloc) of
      NONE => merge_forced_positions rest forced positions
    | SOME pos =>
        case FLOOKUP positions alloc of
          SOME old =>
            if old = pos then
              merge_forced_positions rest forced positions
            else NONE
        | NONE =>
            merge_forced_positions rest forced (positions |+ (alloc,pos))
End

(* Validate all preserved intervals before any hole is filled.  Empty ALLOCAs
   are admissible and occupy no interval, but their address must be in range.
   Source-item recursion also avoids evaluator-hostile fmap_to_alist. *)
Definition checked_preserved_intervals_aux_def:
  checked_preserved_intervals_aux [] positions reserved occupied =
    SOME occupied /\
  checked_preserved_intervals_aux ((alloc,sz)::rest) positions
      reserved occupied =
    case FLOOKUP positions alloc of
      NONE =>
        checked_preserved_intervals_aux rest positions reserved occupied
    | SOME pos =>
        if pos + sz < dimword (:256) then
          if sz = 0 then
            checked_preserved_intervals_aux rest positions reserved occupied
          else if EVERY (reserved_intervals_disjoint (pos,sz))
                        (reserved ++ occupied) then
            checked_preserved_intervals_aux rest positions reserved
              ((pos,sz)::occupied)
          else NONE
        else NONE
End

Definition checked_preserved_intervals_def:
  checked_preserved_intervals items
      (positions : (allocation,num) fmap) reserved =
    if reserved_intervals_wf reserved then
      checked_preserved_intervals_aux items positions reserved []
    else NONE
End

(* The scan is over position-sorted, already validated nonempty intervals.
   Every candidate exclusive endpoint is checked before it is returned. *)
Definition checked_first_fit_scan_def:
  checked_first_fit_scan [] sz start =
    (if start + sz < dimword (:256) then SOME start else NONE) /\
  checked_first_fit_scan ((rpos,rsz)::rest) sz start =
    if start + sz >= dimword (:256) then NONE
    else if rpos + rsz <= start then
      checked_first_fit_scan rest sz start
    else if start + sz <= rpos then SOME start
    else checked_first_fit_scan rest sz (rpos + rsz)
End

Definition insert_reserved_by_pos_def:
  insert_reserved_by_pos (r : num # num) [] = [r] /\
  insert_reserved_by_pos (pos,sz) ((pos',sz')::rs) =
    if pos <= pos' then (pos,sz)::(pos',sz')::rs
    else (pos',sz')::insert_reserved_by_pos (pos,sz) rs
End

Definition sort_reserved_by_pos_def:
  sort_reserved_by_pos [] = [] /\
  sort_reserved_by_pos (r::rs) =
    insert_reserved_by_pos r (sort_reserved_by_pos rs)
End

Definition checked_first_fit_def:
  checked_first_fit occupied sz =
    if reserved_intervals_wf occupied then
      checked_first_fit_scan (sort_reserved_by_pos occupied) sz 0
    else NONE
End

(* Fill source ALLOCAs in instruction order after all preserved positions have
   already been validated and reserved. *)
Definition complete_alloc_positions_aux_def:
  complete_alloc_positions_aux [] positions occupied = SOME positions /\
  complete_alloc_positions_aux (inst::insts) positions occupied =
    if inst.inst_opcode = ALLOCA then
      case exact_static_alloca_size inst of
        NONE => NONE
      | SOME sz =>
          let alloc = Allocation inst.inst_id in
            case FLOOKUP positions alloc of
              SOME pos =>
                complete_alloc_positions_aux insts positions occupied
            | NONE =>
                case checked_first_fit occupied sz of
                  NONE => NONE
                | SOME pos =>
                    let occupied' =
                      if sz = 0 then occupied else (pos,sz)::occupied in
                      complete_alloc_positions_aux insts
                        (positions |+ (alloc,pos)) occupied'
    else complete_alloc_positions_aux insts positions occupied
End

Definition complete_alloc_positions_def:
  complete_alloc_positions (forced : (num,num) fmap) reserved fn
      (positions : (allocation,num) fmap) =
    case static_alloca_items fn of
      NONE => NONE
    | SOME items =>
        let allocs = MAP FST items in
          if ~forced_alloc_keys_valid allocs forced \/
             ~candidate_alloc_keys_valid allocs positions then NONE
          else
            case merge_forced_positions items forced positions of
              NONE => NONE
            | SOME merged =>
                case checked_preserved_intervals items merged reserved of
                  NONE => NONE
                | SOME occupied =>
                    complete_alloc_positions_aux (fn_insts fn) merged
                      (reserved ++ occupied)
End

(* Liveness-aware allocation loop.
   already: (alloc, liveset, position, size) — pre-allocated
   to_alloc: (alloc, liveset, size) — sorted by |liveset| ascending
   For each: reserve only intersecting, then first-fit. *)
Definition allocate_with_livesets_def:
  allocate_with_livesets global_reserved already [] result = result /\
  allocate_with_livesets global_reserved already
    ((alloc, live_insts, sz) :: rest) result =
    let reserved = global_reserved ++
      MAP (\(_, _, pos, asz). (pos, asz))
        (FILTER (\(_, other_live, _, _).
           sinter inst_addr_to other_live live_insts <> []) already) in
    let (pos, _) = allocate_one reserved sz in
    allocate_with_livesets global_reserved
      (already ++ [(alloc, live_insts, pos, sz)])
      rest (result |+ (alloc, pos))
End

(* Full allocation pipeline *)
Definition compute_alloc_map_def:
  compute_alloc_map fn bpr mems_used live_pallocas cfg
                    (pre_allocated : (allocation, num) fmap)
                    (global_reserved : (num # num) list) =
    let alloca_sz = get_alloca_size fn in
    let alloca_sz_opt = \a. let sz = alloca_sz a in
                            if sz = 0 then NONE else SOME sz in
    let ls = mem_liveness_analyze bpr mems_used alloca_sz_opt
               live_pallocas cfg fn in
    let items = fmap_to_alist ls in
    let pre_allocated_dom = FDOM pre_allocated in
    let (already, to_alloc) = PARTITION (\(alloc, _). alloc IN pre_allocated_dom) items in
    let sorted = QSORT (\(_, s1) (_, s2). LENGTH s1 <= LENGTH s2)
                   to_alloc in
    let already_info = MAP (\(alloc, live).
      let pos = case FLOOKUP pre_allocated alloc of
                  SOME p => p | NONE => 0 in
      (alloc, live, pos, alloca_sz alloc)) already in
    let sorted_info = MAP (\(alloc, live).
      (alloc, live, alloca_sz alloc)) sorted in
    allocate_with_livesets global_reserved already_info
      sorted_info pre_allocated
End

Definition alloc_liveset_items_def:
  alloc_liveset_items fn ls =
    MAP
      (\inst.
         let alloc = Allocation inst.inst_id in
         let live = case FLOOKUP ls alloc of SOME s => s | NONE => [] in
         (alloc, live))
      (FILTER (\inst. is_alloca_op inst.inst_opcode) (fn_insts fn))
End

Definition compute_alloc_map_fuel_def:
  compute_alloc_map_fuel fuel fn bpr mems_used live_pallocas cfg
                         (pre_allocated : (allocation, num) fmap)
                         (global_reserved : (num # num) list) =
    let alloca_sz = get_alloca_size fn in
    let alloca_sz_opt = \a. let sz = alloca_sz a in
                            if sz = 0 then NONE else SOME sz in
    let ls = mem_liveness_analyze_fuel fuel bpr mems_used alloca_sz_opt
               live_pallocas cfg fn in
    let items = alloc_liveset_items fn ls in
    let pre_allocated_dom = FDOM pre_allocated in
    let (already, to_alloc) =
      PARTITION (\(alloc, _). alloc IN pre_allocated_dom) items in
    let sorted = QSORT (\(_, s1) (_, s2). LENGTH s1 <= LENGTH s2)
                   to_alloc in
    let already_info = MAP (\(alloc, live).
      let pos = case FLOOKUP pre_allocated alloc of
                  SOME p => p | NONE => 0 in
      (alloc, live, pos, alloca_sz alloc)) already in
    let sorted_info = MAP (\(alloc, live).
      (alloc, live, alloca_sz alloc)) sorted in
    allocate_with_livesets global_reserved already_info
      sorted_info pre_allocated
End

(* Convert allocation-keyed result to variable-keyed alloc_map *)
Definition alloc_result_to_map_def:
  alloc_result_to_map fn (result : (allocation, num) fmap) : alloc_map =
    FOLDL (\amap bb.
      FOLDL (\amap' inst.
        if is_alloca_op inst.inst_opcode then
          case inst.inst_outputs of
            [out] =>
              (case FLOOKUP result (Allocation inst.inst_id) of
                 SOME pos => amap' |+ (out, n2w pos)
               | NONE => amap')
          | _ => amap'
        else amap')
        amap bb.bb_instructions)
      FEMPTY fn.fn_blocks
End

(* =========================================================================
   Per-Instruction Transform
   ========================================================================= *)

Definition concretize_inst_def:
  concretize_inst (amap : alloc_map) inst =
    if is_alloca_op inst.inst_opcode then
      (case inst.inst_outputs of
         [out] =>
           (case FLOOKUP amap out of
              SOME addr => mk_assign_inst inst (Lit addr)
            | NONE => mk_nop_inst inst)
       | _ => inst)
    else inst
End

(* Canonical static-layout rewrite: consume allocation identities directly.
   In particular, equal output strings cannot collapse distinct ALLOCAs. *)
Definition concretize_inst_with_positions_def:
  concretize_inst_with_positions
      (positions : (allocation, num) fmap) inst =
    if inst.inst_opcode = ALLOCA then
      (case inst.inst_outputs of
         [out] =>
           (case FLOOKUP positions (Allocation inst.inst_id) of
              SOME pos => mk_assign_inst inst (Lit (n2w pos))
            | NONE => mk_nop_inst inst)
       | _ => inst)
    else inst
End

(* =========================================================================
   Function-Level Transform
   ========================================================================= *)

(* Function-level: concretize all instructions + clear NOPs.
   Post-sunset: no calloca orphan handling needed. *)
Definition concretize_function_def:
  concretize_function amap fn =
    clear_nops_function
      (function_map_transform
        (block_map_transform (concretize_inst amap))
        fn)
End

Definition concretize_function_with_positions_def:
  concretize_function_with_positions positions fn =
    clear_nops_function
      (function_map_transform
        (block_map_transform (concretize_inst_with_positions positions))
        fn)
End

Definition compute_function_alloc_map_fuel_def:
  compute_function_alloc_map_fuel fuel fn =
    let cfg = cfg_analyze fn in
    let bpr = bp_analyze_fuel fuel cfg fn in
    let result =
      compute_alloc_map_fuel fuel fn bpr (K ([] : allocation list))
        ([] : allocation list) cfg FEMPTY ([] : (num # num) list) in
    alloc_result_to_map fn result
End


(* Convert only source-known forced IDs to the allocation-keyed seed required
   by the liveness allocator.  complete_alloc_positions still validates the
   raw forced domain and all resulting placements. *)
Definition forced_candidate_positions_def:
  forced_candidate_positions [] forced result = result /\
  forced_candidate_positions ((alloc,sz)::items) forced result =
    case FLOOKUP forced (allocation_id alloc) of
      NONE => forced_candidate_positions items forced result
    | SOME pos =>
        forced_candidate_positions items forced (result |+ (alloc,pos))
End

Definition compute_function_layout_fuel_def:
  compute_function_layout_fuel fuel reserved fn =
    case static_alloca_items fn of
      NONE => NONE
    | SOME items =>
        let seed = forced_candidate_positions items
          fn.fn_forced_alloc_positions FEMPTY in
        let cfg = cfg_analyze fn in
        let bpr = bp_analyze_fuel fuel cfg fn in
        let candidate =
          compute_alloc_map_fuel fuel fn bpr (K ([] : allocation list))
            ([] : allocation list) cfg seed reserved in
          case complete_alloc_positions fn.fn_forced_alloc_positions
                 reserved fn candidate of
            NONE => NONE
          | SOME completed => mk_concretize_layout reserved completed fn
End

Definition compute_function_layout_eval_def:
  compute_function_layout_eval reserved fn =
    case complete_alloc_positions fn.fn_forced_alloc_positions
           reserved fn FEMPTY of
      NONE => NONE
    | SOME completed => mk_concretize_layout reserved completed fn
End

Definition fn_has_alloca_def:
  fn_has_alloca fn =
    EXISTS (\inst. is_alloca_op inst.inst_opcode) (fn_insts fn)
End

(* Evaluator path: concrete non-overlapping offsets without MemLiveness. *)
Definition compute_alloc_map_linear_def:
  compute_alloc_map_linear ([] : instruction list) pos = FEMPTY ∧
  compute_alloc_map_linear (inst :: rest) pos =
    if is_alloca_op inst.inst_opcode then
      let sz = case inst_alloca_size inst of SOME n => n | NONE => 0 in
      let amap = compute_alloc_map_linear rest (pos + sz) in
      case inst.inst_outputs of
        [out] => amap |+ (out, n2w pos)
      | _ => amap
    else
      compute_alloc_map_linear rest pos
End

Definition compute_function_alloc_map_eval_def:
  compute_function_alloc_map_eval fn =
    compute_alloc_map_linear (fn_insts fn) 0
End

Definition fn_has_static_layout_def:
  fn_has_static_layout fn = IS_SOME fn.fn_eom
End

Definition apply_concretize_layout_def:
  apply_concretize_layout layout fn =
    (concretize_function_with_positions layout.cl_positions fn) with
      <| fn_forced_alloc_positions := FEMPTY;
         fn_eom := SOME layout.cl_eom |>
End

Definition concretize_function_fuel_def:
  concretize_function_fuel fuel reserved fn =
    if fn_has_static_layout fn then
      if ~fn_has_alloca fn /\ fn.fn_forced_alloc_positions = FEMPTY
      then SOME fn else NONE
    else
      case compute_function_layout_fuel fuel reserved fn of
        NONE => NONE
      | SOME layout => SOME (apply_concretize_layout layout fn)
End

Definition concretize_function_eval_def:
  concretize_function_eval reserved fn =
    if fn_has_static_layout fn then
      if ~fn_has_alloca fn /\ fn.fn_forced_alloc_positions = FEMPTY
      then SOME fn else NONE
    else
      case compute_function_layout_eval reserved fn of
        NONE => NONE
      | SOME layout => SOME (apply_concretize_layout layout fn)
End

Definition concretize_context_fuel_def:
  concretize_context_fuel fuel ctx =
    case OPT_MMAP
      (concretize_function_fuel fuel ctx.ctx_global_reserved)
      ctx.ctx_functions of
      NONE => NONE
    | SOME fns => SOME (ctx with ctx_functions := fns)
End

Definition concretize_context_eval_def:
  concretize_context_eval ctx =
    case OPT_MMAP
      (concretize_function_eval ctx.ctx_global_reserved)
      ctx.ctx_functions of
      NONE => NONE
    | SOME fns => SOME (ctx with ctx_functions := fns)
End
