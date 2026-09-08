(*
 * Dead Store Elimination — Definitions
 *
 * Ports vyper/venom/passes/dead_store_elimination.py to HOL4.
 *
 * Eliminates memory/storage/transient stores that are dead: no
 * subsequent read before the location is overwritten or the
 * function terminates.
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * Framework: analysis_inst_simulates + custom lifting.
 * Uses memory SSA analysis (memSSADefs) to identify dead stores.
 *
 * The Python checks:
 *   1. Location is not volatile
 *   2. Location is fixed (known offset and size)
 *   3. Instruction output is not used
 *   4. No non-related effects
 *   5. Memory def is not live (no read before clobber)
 *
 * We model this as: given a set of dead store instruction IDs
 * (computed by the analysis), NOP those instructions.
 *
 * TOP-LEVEL:
 *   is_dead_store         — predicate for dead store identification
 *   dse_inst              — per-instruction transform
 *   dse_function          — function-level transform
 *)

Theory deadStoreElimDefs
Ancestors
  analysisSimDefs passSharedDefs venomEffects memSSADefs
  memAliasDefs memLocDefs basePtrDefs cfgDefs While

(* is_store_opcode (in passSharedDefs) covers MSTORE/SSTORE/TSTORE.
   DSE operates on all non-terminating memory definitions identified by
   memSSA.  Terminators must be excluded because dse_inst replaces eligible
   instructions with NOP. *)
Definition is_memory_def_opcode_def:
  is_memory_def_opcode (space : addr_space) op <=>
    ~is_terminator op /\
    (case space of
       AddrSp_Memory => Eff_MEMORY IN write_effects op
     | AddrSp_Storage => Eff_STORAGE IN write_effects op
     | AddrSp_Transient => Eff_TRANSIENT IN write_effects op
     | _ => F)
End

(* ===== Memory store liveness ===== *)

(* Check if an instruction reads a location that may alias the query.
   Uses the base pointer analysis to compute read locations.
   No fixedness check on read_loc: unfixed locations conservatively
   may-alias everything, matching Python's may_overlap behavior
   for unknown offsets (e.g., INVOKE reads). *)
Definition dse_inst_reads_alias_def:
  dse_inst_reads_alias (aliases : alias_sets) (bp : bp_result)
                       (space : addr_space) store_loc inst =
    let read_loc = bp_get_read_location bp inst space in
    ma_may_alias aliases read_loc store_loc
End

(* Check if an instruction completely clobbers the query location.
   Python: write_loc.completely_contains(query_loc). *)
Definition dse_inst_clobbers_def:
  dse_inst_clobbers (bp : bp_result) (space : addr_space)
                    store_loc inst =
    let write_loc = bp_get_write_location bp inst space in
    ml_is_fixed write_loc /\ completely_contains write_loc store_loc
End

(* A store is "live" if some reachable read may alias its write location
   without an intervening complete clobber. This models Python's
   _is_memory_def_live: a CFG walk from the store checking for reads
   before clobbers.

   Semantic property (used as precondition, established by memSSA):
   - Starting from the instruction after the store in its block,
     and continuing through all reachable blocks via CFG successors,
   - If any instruction reads a location that may_alias the store's
     write location, the store is live.
   - If an instruction completely_contains-clobbers the store's location,
     that path is dead (no further search needed on that path).

   We state this as a negated existential for the precondition. *)
(* A block contains no complete clobber of store_loc *)
Definition block_no_full_clobber_def:
  block_no_full_clobber bp space store_loc fn lbl <=>
    !bb. MEM bb fn.fn_blocks /\ bb.bb_label = lbl ==>
         EVERY (\inst. ~dse_inst_clobbers bp space store_loc inst)
               bb.bb_instructions
End

(* A block has a read aliasing store_loc before any clobber *)
Definition block_has_unclobbered_read_def:
  block_has_unclobbered_read (aliases : alias_sets) bp space
                             store_loc fn lbl <=>
    ?bb j.
      MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\
      j < LENGTH bb.bb_instructions /\
      (* No clobber before position j *)
      (!k. k < j ==>
           ~dse_inst_clobbers bp space store_loc
             (EL k bb.bb_instructions)) /\
      dse_inst_reads_alias aliases bp space store_loc
        (EL j bb.bb_instructions)
End

(* A store is "live" if some reachable read may alias its write location
   without an intervening complete clobber. Models Python's
   _is_memory_def_live: walks CFG from the store, tracking whether the
   location has been completely clobbered.

   The path consists of:
   1. Remaining instructions in the store's block (after store)
   2. Any block reachable through clobber-free intermediate blocks

   Intermediate blocks: no complete clobber anywhere in the block.
   Final block: read before any clobber (partial block check). *)
Definition dse_mem_def_live_def:
  dse_mem_def_live (cfg : cfg_analysis) (aliases : alias_sets)
                   (bp : bp_result) store_loc (space : addr_space)
                   fn bb inst_idx <=>
    (* Case 1: read in same block after store, before any clobber *)
    (?j. j > inst_idx /\
         j < LENGTH bb.bb_instructions /\
         (!k. inst_idx < k /\ k < j ==>
              ~dse_inst_clobbers bp space store_loc
                (EL k bb.bb_instructions)) /\
         dse_inst_reads_alias aliases bp space store_loc
           (EL j bb.bb_instructions)) \/
    (* Case 2: read in a successor block reachable through
       clobber-free blocks *)
    (?succ_lbl target_lbl.
       (* No clobber in rest of this block *)
       (!k. inst_idx < k /\ k < LENGTH bb.bb_instructions ==>
            ~dse_inst_clobbers bp space store_loc
              (EL k bb.bb_instructions)) /\
       (* succ_lbl is a direct successor *)
       MEM succ_lbl (cfg_succs_of cfg bb.bb_label) /\
       (* target_lbl reachable from succ_lbl through clobber-free blocks *)
       RTC (\a b. MEM b (cfg_succs_of cfg a) /\
                  block_no_full_clobber bp space store_loc fn a)
         succ_lbl target_lbl /\
       (* target block has a read before any clobber *)
       block_has_unclobbered_read aliases bp space store_loc fn
         target_lbl)
End

(* ===== Dead store precondition ===== *)

(* Instruction outputs are unused: no other instruction references them *)
Definition outputs_unused_def:
  outputs_unused inst fn <=>
    EVERY (\out.
      !bb' i'. MEM bb' fn.fn_blocks /\
               MEM i' bb'.bb_instructions /\
               i'.inst_id <> inst.inst_id ==>
               ~MEM (Var out) i'.inst_operands)
    inst.inst_outputs
End

(* Instruction's effects are confined to the given address space.
   Storage/Transient only allow their space. *)
Definition effects_in_space_def:
  effects_in_space (space : addr_space) inst <=>
    let space_eff = case space of
                      AddrSp_Memory => Eff_MEMORY
                    | AddrSp_Storage => Eff_STORAGE
                    | AddrSp_Transient => Eff_TRANSIENT
                    | AddrSp_Calldata => Eff_MEMORY
                    | AddrSp_Code => Eff_MEMORY
                    | AddrSp_Returndata => Eff_MEMORY in
    (write_effects inst.inst_opcode UNION read_effects inst.inst_opcode)
      SUBSET {space_eff}
End

(* Precondition: dead_ids only contains IDs of store instructions in fn
   whose stored values are provably dead. Matches Python's _is_dead_store.

   The inst.inst_outputs = [] condition restricts dead stores to
   instructions that have no output variables (MSTORE, SSTORE, TSTORE).
   This is necessary because mk_nop_inst removes the instruction's
   outputs, and dse_equiv checks ALL variables including unused ones.
   If a dead store had non-empty outputs (e.g., DLOAD which writes
   to memory AND produces an output variable), NOP'ing it would
   change the output variable's value, violating dse_equiv.

   In the Python DSE, DLOAD with unused outputs CAN be eliminated
   (Python doesn't check variable mappings, only EVM-observable
   effects). But in HOL4, dse_equiv checks !v. lookup_var v s1 =
   lookup_var v s2, so we must require empty outputs.

   This is the tightest sufficient fix: it precisely matches the
   set of instructions DSE eliminates in practice (actual stores)
   while being formally correct for the dse_equiv relation. *)
Definition all_dead_stores_def:
  all_dead_stores dead_ids cfg aliases bp (space : addr_space) fn <=>
    !id. id IN dead_ids ==>
      ?bb inst inst_idx.
        MEM bb fn.fn_blocks /\
        inst_idx < LENGTH bb.bb_instructions /\
        EL inst_idx bb.bb_instructions = inst /\
        inst.inst_id = id /\
        is_memory_def_opcode space inst.inst_opcode /\
        inst.inst_outputs = [] /\
        ~(bp_get_write_location bp inst space).ml_volatile /\
        ml_is_fixed (bp_get_write_location bp inst space) /\
        outputs_unused inst fn /\
        effects_in_space space inst /\
        ~dse_mem_def_live cfg aliases bp
          (bp_get_write_location bp inst space)
          space fn bb inst_idx
End

(* ===== Per-instruction transform ===== *)

(* Transform given a set of instruction IDs identified as dead stores.
   If the instruction's ID is in the dead set, NOP it.
   The dead set is computed by memSSA analysis externally. *)
(* Python: run_pass takes addr_space. The pass runs once per space. *)
Definition dse_inst_def:
  dse_inst (dead_ids : num set) (space : addr_space) inst =
    if inst.inst_id IN dead_ids /\ is_memory_def_opcode space inst.inst_opcode
    then mk_nop_inst inst
    else inst
End

(* ===== Function-level transform ===== *)

(* Single-pass: apply dead store elimination for given dead_ids. *)
Definition dse_single_pass_def:
  dse_single_pass dead_ids space fn =
    function_map_transform
      (block_map_transform (dse_inst dead_ids space)) fn
End

(* Python runs DSE in a loop: analyze → remove → re-analyze → ...
   until no more dead stores are found.
   The analysis_fn parameter computes dead store IDs for a given function.
   OWHILE terminates because each iteration removes at least one dead
   store, strictly decreasing the count of memory-writing instructions. *)
Definition dse_iterate_def:
  dse_iterate analysis_fn space fn =
    OWHILE (\fn. analysis_fn fn <> {})
         (\fn. dse_single_pass (analysis_fn fn) space fn) fn
End

(* Run DSE for one address space. Python: run_pass(addr_space). *)
Definition dse_function_space_def:
  dse_function_space analysis_fn space fn =
    case dse_iterate (analysis_fn space) space fn of
      SOME fn' => clear_nops_function fn'
    | NONE => clear_nops_function fn
End

(* Run DSE for all three address spaces (Python pipeline calls
   run_pass for each space in sequence). *)
Definition dse_function_def:
  dse_function analysis_fn fn =
    let fn1 = dse_function_space analysis_fn AddrSp_Memory fn in
    let fn2 = dse_function_space analysis_fn AddrSp_Storage fn1 in
    dse_function_space analysis_fn AddrSp_Transient fn2
End

(* ===== Observable equivalence for DSE ===== *)

(* DSE removes dead stores — the written value is never read on any
   path within the function (memSSA treats RETURN/REVERT/LOG/SHA3
   as memory reads). The raw memory/storage/transient state at the
   eliminated location differs between original and transformed,
   but no instruction observes the difference.

   dse_equiv compares everything except the address space being
   optimized. After running DSE for all 3 spaces, the combined
   equivalence (dse_all_equiv) drops memory, transient, and
   storage (inside vs_accounts) comparison.

   This is correct because:
   - Variables are unchanged (DSE only NOPs stores with empty outputs)
   - Logs, return data, halt status, immutables etc. unchanged
   - RETURN/REVERT data is unaffected (memSSA marks those reads
     as live, preventing elimination of stores in the return range)
   - vs_inst_idx and vs_current_bb are excluded: clear_nops_function
     changes instruction count within blocks, so Halt/Abort states may
     carry different inst_idx. These are purely internal control-flow
     fields with no semantic meaning after function completion.
     (execution_equiv also excludes these, enabling the clear_nops bridge.) *)
Definition dse_equiv_def:
  dse_equiv (space : addr_space) s1 s2 <=>
    (!v. lookup_var v s1 = lookup_var v s2) /\
    (space <> AddrSp_Memory ==> s1.vs_memory = s2.vs_memory) /\
    (space <> AddrSp_Transient ==> s1.vs_transient = s2.vs_transient) /\
    (space <> AddrSp_Storage ==> s1.vs_accounts = s2.vs_accounts) /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas
End

(* After all 3 spaces: memory, transient, and accounts may differ *)
(* Note: vs_current_bb and vs_inst_idx are excluded — they are internal
   control-flow fields with no semantic meaning after function completion.
   vs_memory, vs_transient, vs_accounts are excluded because each space
   may differ at eliminated store locations. *)
Definition dse_all_equiv_def:
  dse_all_equiv s1 s2 <=>
    (!v. lookup_var v s1 = lookup_var v s2) /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas
End
