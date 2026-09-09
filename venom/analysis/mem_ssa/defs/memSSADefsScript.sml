(*
 * Memory SSA Analysis — Definitions
 *
 * Ported from vyper/venom/analysis/mem_ssa.py.
 * LLVM-style Memory SSA: tracks memory state versions, not partitioned
 * ranges.  Each store creates a new version (MemDef), each load reads
 * a version (MemUse), join points get MemPhi nodes.
 *
 * TOP-LEVEL:
 *   mem_ssa_node, mem_ssa_state    — types
 *   mem_ssa_build               — construct memory SSA for a function
 *   mem_ssa_get_memory_def      — instruction → def access id
 *   mem_ssa_get_memory_use      — instruction → use access id
 *   mem_ssa_get_exit_def        — block → last reaching definition
 *   mem_ssa_get_clobbered       — walk for clobbering definition
 *   mem_ssa_get_aliased         — walk for aliased accesses
 *   mem_ssa_mark_volatile       — mark a location volatile
 *   memory_ssa_analyze, storage_ssa_analyze, transient_ssa_analyze
 *
 * Helper (internal):
 *   mn_inst_id, mn_block, mn_loc — node projections
 *   mem_ssa_process_inst, mem_ssa_process_block, mem_ssa_process_blocks — Phase 1
 *   mem_ssa_insert_phis — Phase 2
 *   mem_ssa_connect_all — Phase 3
 *   mem_ssa_remove_redundant_phis — Phase 4
 *   find_prev_def — backward scan within block
 *
 * Divergences from Python:
 *   - Flat map representation: nodes stored in (num, mem_ssa_node) fmap
 *   - LiveOnEntry is access_id 0 (sentinel, not stored in ms_nodes)
 *   - reaching_def stored in separate ms_reaching map (not embedded in node)
 *   - Uses fuel for recursive functions (get_exit_def, clobber walk)
 *)

Theory memSSADefs
Ancestors
  memAliasDefs dominatorDefs
Libs
  listTheory finite_mapTheory pairTheory

(* ==========================================================================
   Types
   ========================================================================== *)

(* A memory SSA node.  Each node carries the originating instruction's id,
   the block it belongs to, and the memory location accessed.
   MnPhi carries only the block label (no instruction). *)
Datatype:
  mem_ssa_node =
    MnDef num string mem_loc     (* inst_id, block_label, location *)
  | MnUse num string mem_loc     (* inst_id, block_label, location *)
  | MnPhi string                 (* block_label *)
End

(* Memory SSA analysis result.
 * access_id = 0 is the implicit LiveOnEntry sentinel. *)
Datatype:
  mem_ssa_state = <|
    ms_nodes      : (num, mem_ssa_node) fmap;          (* access_id → node *)
    ms_reaching   : (num, num) fmap;                 (* access_id → reaching_def id *)
    ms_phi_ops    : (num, (num # string) list) fmap; (* phi_id → [(rd_id, pred_block)] *)
    ms_block_defs : (string, num list) fmap;         (* block → ordered def ids *)
    ms_block_uses : (string, num list) fmap;         (* block → ordered use ids *)
    ms_block_phis : (string, num) fmap;              (* block → phi id (at most one) *)
    ms_inst_def   : (num, num) fmap;                 (* inst_id → def access_id *)
    ms_inst_use   : (num, num) fmap;                 (* inst_id → use access_id *)
    ms_next_id    : num                              (* next fresh id *)
  |>
End

(* ==========================================================================
   Node projections
   ========================================================================== *)

Definition mn_inst_id_def:
  mn_inst_id (MnDef iid _ _) = iid ∧
  mn_inst_id (MnUse iid _ _) = iid ∧
  mn_inst_id (MnPhi _) = 0
End

Definition mn_block_def:
  mn_block (MnDef _ blk _) = blk ∧
  mn_block (MnUse _ blk _) = blk ∧
  mn_block (MnPhi blk) = blk
End

Definition mn_loc_def:
  mn_loc (MnDef _ _ loc) = loc ∧
  mn_loc (MnUse _ _ loc) = loc ∧
  mn_loc (MnPhi _) = ml_empty
End

(* ==========================================================================
   Initial state
   ========================================================================== *)

Definition mem_ssa_init_def:
  mem_ssa_init =
    <| ms_nodes      := FEMPTY;
       ms_reaching   := FEMPTY;
       ms_phi_ops    := FEMPTY;
       ms_block_defs := FEMPTY;
       ms_block_uses := FEMPTY;
       ms_block_phis := FEMPTY;
       ms_inst_def   := FEMPTY;
       ms_inst_use   := FEMPTY;
       ms_next_id    := 1  (* 0 reserved for LiveOnEntry *)
    |>
End

(* ==========================================================================
   Phase 1: Collect definitions and uses
   ========================================================================== *)

(* Process one instruction: create MnUse and/or MnDef if it accesses memory. *)
Definition mem_ssa_process_inst_def:
  mem_ssa_process_inst bp addr_sp blk_lbl ms inst =
    let rloc = bp_get_read_location bp inst addr_sp in
    let wloc = bp_get_write_location bp inst addr_sp in
    (* Create use if instruction reads memory *)
    let ms1 =
      if rloc = ml_empty then ms
      else
        let uid = ms.ms_next_id in
        let old = fmap_lookup_list ms.ms_block_uses blk_lbl in
        ms with <|
          ms_nodes      := ms.ms_nodes |+ (uid, MnUse inst.inst_id blk_lbl rloc);
          ms_block_uses := ms.ms_block_uses |+ (blk_lbl, SNOC uid old);
          ms_inst_use   := ms.ms_inst_use |+ (inst.inst_id, uid);
          ms_next_id    := uid + 1
        |>
    in
    (* Create def if instruction writes memory *)
    if wloc = ml_empty then ms1
    else
      let did = ms1.ms_next_id in
      let old = fmap_lookup_list ms1.ms_block_defs blk_lbl in
      ms1 with <|
        ms_nodes      := ms1.ms_nodes |+ (did, MnDef inst.inst_id blk_lbl wloc);
        ms_block_defs := ms1.ms_block_defs |+ (blk_lbl, SNOC did old);
        ms_inst_def   := ms1.ms_inst_def |+ (inst.inst_id, did);
        ms_next_id    := did + 1
      |>
End

(* Process all instructions in a basic block. *)
Definition mem_ssa_process_block_def:
  mem_ssa_process_block bp addr_sp blk_lbl ms [] = ms ∧
  mem_ssa_process_block bp addr_sp blk_lbl ms (inst::insts) =
    mem_ssa_process_block bp addr_sp blk_lbl
      (mem_ssa_process_inst bp addr_sp blk_lbl ms inst) insts
End

(* Process blocks in DFS pre-order. *)
Definition mem_ssa_process_blocks_def:
  mem_ssa_process_blocks bp addr_sp fn ms [] = ms ∧
  mem_ssa_process_blocks bp addr_sp fn ms (lbl::lbls) =
    case lookup_block lbl fn.fn_blocks of
      NONE => mem_ssa_process_blocks bp addr_sp fn ms lbls
    | SOME bb =>
        mem_ssa_process_blocks bp addr_sp fn
          (mem_ssa_process_block bp addr_sp lbl ms bb.bb_instructions) lbls
End

(* ==========================================================================
   get_exit_def — last reaching definition at block exit (fuel-based)

   1. Last MemDef in block (if any)
   2. Block's MemPhi (if any)
   3. Recurse to idom
   4. LiveOnEntry (id 0)
   ========================================================================== *)

Definition mem_ssa_get_exit_def_def:
  mem_ssa_get_exit_def ms dom 0 lbl = 0 ∧
  mem_ssa_get_exit_def ms dom (SUC fuel) lbl =
    let defs = fmap_lookup_list ms.ms_block_defs lbl in
    if defs ≠ [] then LAST defs
    else
      case FLOOKUP ms.ms_block_phis lbl of
        SOME phi_id => phi_id
      | NONE =>
          (case idom_of dom lbl of
             SOME idom_lbl => mem_ssa_get_exit_def ms dom fuel idom_lbl
           | NONE => 0)
End

(* ==========================================================================
   Phase 2: Insert MemPhi nodes at dominance frontiers
   ========================================================================== *)

(* Insert a phi at a single frontier block (if not already present).
 * Returns (ms', T) if a new phi was inserted, (ms, F) otherwise. *)
Definition mem_ssa_insert_phi_at_def:
  mem_ssa_insert_phi_at ms cfg dom fuel blk_lbl =
    case FLOOKUP ms.ms_block_phis blk_lbl of
      SOME _ => (ms, F)
    | NONE =>
        let phi_id = ms.ms_next_id in
        let preds = cfg_preds_of cfg blk_lbl in
        let ops = MAP (λp. (mem_ssa_get_exit_def ms dom fuel p, p)) preds in
        let ms' = ms with <|
          ms_nodes      := ms.ms_nodes |+ (phi_id, MnPhi blk_lbl);
          ms_block_phis := ms.ms_block_phis |+ (blk_lbl, phi_id);
          ms_phi_ops    := ms.ms_phi_ops |+ (phi_id, ops);
          ms_next_id    := phi_id + 1
        |> in
        (ms', T)
End

(* Process the dominance frontiers of one block.
 * Returns (ms', new_worklist_additions). *)
Definition mem_ssa_process_frontiers_def:
  mem_ssa_process_frontiers ms cfg dom fuel [] = (ms, []) ∧
  mem_ssa_process_frontiers ms cfg dom fuel (f::fs) =
    let (ms1, inserted) = mem_ssa_insert_phi_at ms cfg dom fuel f in
    let (ms2, rest) = mem_ssa_process_frontiers ms1 cfg dom fuel fs in
    (ms2, if inserted then f :: rest else rest)
End

(* Worklist iteration for phi placement.
 * LIFO order: Python uses worklist.pop() + append() (stack).
 * fuel bounds total iterations (at most |blocks| phis can be inserted). *)
Definition mem_ssa_insert_phis_def:
  mem_ssa_insert_phis ms cfg dom ef 0 wl = ms ∧
  mem_ssa_insert_phis ms cfg dom ef (SUC fuel) [] = ms ∧
  mem_ssa_insert_phis ms cfg dom ef (SUC fuel) (b::wl) =
    let frontiers = frontier_of dom b in
    let (ms', new_wl) = mem_ssa_process_frontiers ms cfg dom ef frontiers in
    mem_ssa_insert_phis ms' cfg dom ef fuel (new_wl ++ wl)
End

(* ==========================================================================
   Phase 3: Connect reaching definitions
   ========================================================================== *)

(* Find the last MemDef in a block's instruction list before a target inst.
 * Scans forward; returns the def closest to (but before) target_id. *)
Definition mem_ssa_find_prev_def_def:
  mem_ssa_find_prev_def ms [] target_id = NONE ∧
  mem_ssa_find_prev_def ms (inst::insts) target_id =
    if inst.inst_id = target_id then NONE
    else
      case mem_ssa_find_prev_def ms insts target_id of
        SOME d => SOME d
      | NONE => FLOOKUP ms.ms_inst_def inst.inst_id
End

(* Get the reaching definition for a def/use at a given position in a block.
 * 1. Scan backward in same block for preceding MemDef
 * 2. Check block's MemPhi
 * 3. Get exit_def from immediate dominator
 * 4. LiveOnEntry *)
Definition mem_ssa_reaching_in_block_def:
  mem_ssa_reaching_in_block ms dom fn fuel inst_id blk_lbl =
    case lookup_block blk_lbl fn.fn_blocks of
      NONE => 0
    | SOME bb =>
        case mem_ssa_find_prev_def ms bb.bb_instructions inst_id of
          SOME def_id => def_id
        | NONE =>
            (case FLOOKUP ms.ms_block_phis blk_lbl of
               SOME phi_id => phi_id
             | NONE =>
                 (case idom_of dom blk_lbl of
                    SOME idom_lbl => mem_ssa_get_exit_def ms dom fuel idom_lbl
                  | NONE => 0))
End

(* Connect a list of access ids to their reaching definitions. *)
Definition mem_ssa_connect_list_def:
  mem_ssa_connect_list ms dom fn fuel [] = ms ∧
  mem_ssa_connect_list ms dom fn fuel (aid::aids) =
    case FLOOKUP ms.ms_nodes aid of
      NONE => mem_ssa_connect_list ms dom fn fuel aids
    | SOME (MnPhi _) => mem_ssa_connect_list ms dom fn fuel aids
    | SOME node =>
        let rd = mem_ssa_reaching_in_block ms dom fn fuel
                   (mn_inst_id node) (mn_block node) in
        let ms' = ms with ms_reaching := ms.ms_reaching |+ (aid, rd) in
        mem_ssa_connect_list ms' dom fn fuel aids
End

(* Connect all uses and defs across all blocks (in DFS pre-order). *)
Definition mem_ssa_connect_all_def:
  mem_ssa_connect_all ms dom fn fuel [] = ms ∧
  mem_ssa_connect_all ms dom fn fuel (lbl::lbls) =
    let uses = fmap_lookup_list ms.ms_block_uses lbl in
    let defs = fmap_lookup_list ms.ms_block_defs lbl in
    let ms1 = mem_ssa_connect_list ms dom fn fuel uses in
    let ms2 = mem_ssa_connect_list ms1 dom fn fuel defs in
    mem_ssa_connect_all ms2 dom fn fuel lbls
End

(* ==========================================================================
   Phase 4: Remove redundant phi nodes
   ========================================================================== *)

(* A phi is redundant if all operands have the same reaching-def id. *)
Definition mem_ssa_phi_redundant_def:
  mem_ssa_phi_redundant [] = T ∧
  mem_ssa_phi_redundant ((first_rd, _) :: rest) =
    EVERY (λ(rd, _). rd = first_rd) rest
End

(* Remove all redundant phis.  Input: list of (block_label, phi_id) pairs. *)
Definition mem_ssa_remove_redundant_phis_def:
  mem_ssa_remove_redundant_phis ms [] = ms ∧
  mem_ssa_remove_redundant_phis ms ((lbl, phi_id)::rest) =
    case FLOOKUP ms.ms_phi_ops phi_id of
      NONE => mem_ssa_remove_redundant_phis ms rest
    | SOME ops =>
        if mem_ssa_phi_redundant ops then
          mem_ssa_remove_redundant_phis
            (ms with ms_block_phis := ms.ms_block_phis \\ lbl) rest
        else
          mem_ssa_remove_redundant_phis ms rest
End

(* ==========================================================================
   Top-level construction
   ========================================================================== *)

Definition mem_ssa_build_def:
  mem_ssa_build cfg dom bp fn addr_sp =
    let order = cfg.cfg_dfs_pre in
    let fuel = LENGTH (fn_labels fn) in
    (* Phase 1: collect defs and uses *)
    let ms = mem_ssa_process_blocks bp addr_sp fn mem_ssa_init order in
    (* Phase 2: insert phi nodes *)
    let def_blocks = MAP FST (fmap_to_alist ms.ms_block_defs) in
    let ms = mem_ssa_insert_phis ms cfg dom fuel (fuel * fuel) def_blocks in
    (* Phase 3: connect reaching definitions *)
    let ms = mem_ssa_connect_all ms dom fn fuel order in
    (* Phase 4: remove redundant phis *)
    let phi_pairs = fmap_to_alist ms.ms_block_phis in
    mem_ssa_remove_redundant_phis ms phi_pairs
End

(* ==========================================================================
   Query: get_memory_def / get_memory_use
   ========================================================================== *)

Definition mem_ssa_get_memory_def_def:
  mem_ssa_get_memory_def ms inst_id = FLOOKUP ms.ms_inst_def inst_id
End

Definition mem_ssa_get_memory_use_def:
  mem_ssa_get_memory_use ms inst_id = FLOOKUP ms.ms_inst_use inst_id
End

(* ==========================================================================
   Query: Clobber walk

   Walks up the reaching-def chain from an access to find the most
   recent definition that completely_contains the query location.
   For MemPhi: recurse into each operand.
     - 0 clobbering operands → NONE (no clobber on any path)
     - 1 clobbering operand  → SOME that operand
     - ≥2 clobbering operands → SOME the phi itself (conservative)
   ========================================================================== *)

(* Collect clobbers from phi operands, threading visited set.
 * walker : num list → num → num option × num list
 * Returns (clobbers, updated_visited). *)
Definition mem_ssa_collect_phi_clobbers_def:
  mem_ssa_collect_phi_clobbers walker visited [] = ([], visited) ∧
  mem_ssa_collect_phi_clobbers walker visited ((rd, _)::ops) =
    let (result, visited1) = walker visited rd in
    let (rest, visited2) =
      mem_ssa_collect_phi_clobbers walker visited1 ops in
    case result of
      NONE => (rest, visited2)
    | SOME c => (c :: rest, visited2)
End

(* Returns (result, updated_visited) to share visited across phi branches. *)
Definition mem_ssa_walk_clobber_def:
  mem_ssa_walk_clobber ms 0 visited current qloc = (NONE, visited) ∧
  mem_ssa_walk_clobber ms (SUC fuel) visited current qloc =
    if current = 0 then (NONE, visited)
    else if MEM current visited then (NONE, visited)
    else
      let visited' = current :: visited in
      case FLOOKUP ms.ms_nodes current of
        NONE => (NONE, visited')
      | SOME (MnDef _ _ def_loc) =>
          if completely_contains def_loc qloc then (SOME current, visited')
          else
            (case FLOOKUP ms.ms_reaching current of
               NONE => (NONE, visited')
             | SOME rd => mem_ssa_walk_clobber ms fuel visited' rd qloc)
      | SOME (MnUse _ _ _) =>
          (case FLOOKUP ms.ms_reaching current of
             NONE => (NONE, visited')
           | SOME rd => mem_ssa_walk_clobber ms fuel visited' rd qloc)
      | SOME (MnPhi _) =>
          (case FLOOKUP ms.ms_phi_ops current of
             NONE => (NONE, visited')
           | SOME ops =>
               let (clobbers, visited'') = mem_ssa_collect_phi_clobbers
                 (λv rd. mem_ssa_walk_clobber ms fuel v rd qloc)
                 visited' ops in
               case clobbers of
                 [] => (NONE, visited'')
               | [c] => (SOME c, visited'')
               | _ => (SOME current, visited''))
End

(* Top-level clobber query.
 * Returns NONE if given LiveOnEntry (id 0).
 * Returns SOME 0 (LiveOnEntry) if no store clobbers the location.
 * Returns SOME access_id of the clobbering definition otherwise. *)
Definition mem_ssa_get_clobbered_def:
  mem_ssa_get_clobbered ms fuel access_id =
    if access_id = 0 then NONE
    else
      case FLOOKUP ms.ms_nodes access_id of
        NONE => NONE
      | SOME node =>
          let qloc = mn_loc node in
          case FLOOKUP ms.ms_reaching access_id of
            NONE => SOME 0
          | SOME rd =>
              let (result, _) = mem_ssa_walk_clobber ms fuel [] rd qloc in
              case result of
                NONE => SOME 0
              | SOME c => SOME c
End

(* ==========================================================================
   Query: Aliased accesses walk

   Walk up the reaching-def chain and collect all MemDef nodes whose
   locations may_alias with the query location.
   ========================================================================== *)

(* Collect aliased accesses from phi operands, threading visited set.
 * Returns (accesses, updated_visited). *)
Definition mem_ssa_collect_phi_aliased_def:
  mem_ssa_collect_phi_aliased walker visited [] = ([], visited) ∧
  mem_ssa_collect_phi_aliased walker visited ((rd, _)::ops) =
    let (results, visited1) = walker visited rd in
    let (rest, visited2) =
      mem_ssa_collect_phi_aliased walker visited1 ops in
    (results ++ rest, visited2)
End

(* Returns (aliased_accesses, updated_visited). *)
Definition mem_ssa_walk_aliased_def:
  mem_ssa_walk_aliased ms alias 0 visited current qloc = ([], visited) ∧
  mem_ssa_walk_aliased ms alias (SUC fuel) visited current qloc =
    if current = 0 then ([], visited)
    else if MEM current visited then ([], visited)
    else
      let visited' = current :: visited in
      let (from_here, visited2) =
        case FLOOKUP ms.ms_nodes current of
          NONE => ([], visited')
        | SOME (MnDef _ _ def_loc) =>
            if ma_may_alias alias qloc def_loc then ([current], visited')
            else ([], visited')
        | SOME (MnUse _ _ _) => ([], visited')
        | SOME (MnPhi _) =>
            (case FLOOKUP ms.ms_phi_ops current of
               NONE => ([], visited')
             | SOME ops =>
                 mem_ssa_collect_phi_aliased
                   (λv rd. mem_ssa_walk_aliased ms alias fuel v rd qloc)
                   visited' ops)
      in
      let (from_chain, visited3) =
        case FLOOKUP ms.ms_reaching current of
          NONE => ([], visited2)
        | SOME rd => mem_ssa_walk_aliased ms alias fuel visited2 rd qloc
      in
      (from_here ++ from_chain, visited3)
End

Definition mem_ssa_get_aliased_def:
  mem_ssa_get_aliased ms alias fuel access_id =
    if access_id = 0 then []
    else
      let qloc = case FLOOKUP ms.ms_nodes access_id of
                   SOME node => mn_loc node
                 | NONE => ml_empty in
      FST (mem_ssa_walk_aliased ms alias fuel [] access_id qloc)
End

(* ==========================================================================
   Mark location volatile
   ========================================================================== *)

Definition mem_ssa_mark_volatile_def:
  mem_ssa_mark_volatile ms alias loc =
    let (vloc, alias') = ma_mark_volatile alias loc in
    (* Update any def whose location aliases with loc to be volatile *)
    let ms' = ms with
      ms_nodes :=
        FOLDL (λnodes (aid, node).
          case node of
            MnDef iid blk dloc =>
              if ma_may_alias alias dloc loc
              then nodes |+ (aid, MnDef iid blk (mk_volatile dloc))
              else nodes
          | _ => nodes)
        ms.ms_nodes (fmap_to_alist ms.ms_nodes)
    in
    (vloc, ms', alias')
End

(* ==========================================================================
   Three address-space instantiations
   ========================================================================== *)

Definition memory_ssa_analyze_def:
  memory_ssa_analyze cfg dom bp fn =
    mem_ssa_build cfg dom bp fn AddrSp_Memory
End

Definition storage_ssa_analyze_def:
  storage_ssa_analyze cfg dom bp fn =
    mem_ssa_build cfg dom bp fn AddrSp_Storage
End

Definition transient_ssa_analyze_def:
  transient_ssa_analyze cfg dom bp fn =
    mem_ssa_build cfg dom bp fn AddrSp_Transient
End
