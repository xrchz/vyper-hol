(*
 * FCG Analysis Definitions
 *
 * Function Call Graph construction for Venom IR.
 * Computes which functions call which via INVOKE instructions,
 * starting from the entry function.
 *
 * TOP-LEVEL definitions:
 *   fcg_analysis           - result record type
 *   fcg_empty              - empty analysis result
 *   fcg_postorder          - total callee-first walk from an entry
 *   fcg_get_callees        - query: callees of a function
 *   fcg_get_call_sites     - query: INVOKE instructions targeting a function
 *   fcg_is_reachable       - query: is a function reachable from entry?
 *   fcg_get_unreachable    - query: unreachable functions in context
 *   get_invoke_targets     - extract (callee, instruction) pairs from INVOKE list
 *   fcg_scan_function      - scan a function's blocks for INVOKE targets
 *   fcg_record_edges       - record caller->callee edges into analysis
 *   fcg_visit              - process a single unvisited function
 *   fcg_dfs                - DFS worklist traversal (has termination proof)
 *   fcg_analyze            - top-level entry point
 *
 * Helper lemmas (termination):
 *   filter_length_mono     - stricter predicate => shorter FILTER
 *   filter_visited_mono    - adding to visited can only shrink FILTER
 *   filter_visited_shrink  - adding unvisited name strictly shrinks FILTER
 *   filter_neq_redundant   - name not in list => neq conjunct redundant
 *)

Theory fcgDefs
Ancestors
  venomInst relation cfgDefs

(* ==========================================================================
   Result type
   ========================================================================== *)

Datatype:
  fcg_analysis = <|
    fcg_callees : (string, string list) fmap;
    fcg_call_sites : (string, instruction list) fmap;
    fcg_reachable : string list
  |>
End

Definition fcg_empty_def:
  fcg_empty = <|
    fcg_callees := FEMPTY;
    fcg_call_sites := FEMPTY;
    fcg_reachable := []
  |>
End

Definition fcg_postorder_def:
  fcg_postorder fcg entry =
    SND (dfs_post_walk fcg.fcg_callees [] entry)
End

Definition list_index_def:
  list_index x xs = INDEX_OF x xs
End

Definition list_precedes_def:
  list_precedes x y xs =
    case (list_index x xs, list_index y xs) of
      (SOME i, SOME j) => i < j
    | _ => F
End

Theorem list_precedes_iff:
  list_precedes x y xs <=>
  ?i j. list_index x xs = SOME i /\
        list_index y xs = SOME j /\ i < j
Proof
  simp[list_precedes_def] >>
  Cases_on `list_index x xs` >>
  Cases_on `list_index y xs` >> simp[]
QED


(* ==========================================================================
   Query API

   Use these to inspect results; they return sensible defaults for absent
   keys.  Do not inspect fmap domains directly — maps are sparse (only
   populated for functions with at least one edge).
   ========================================================================== *)

Definition fcg_get_callees_def:
  fcg_get_callees fcg fn_name =
    case FLOOKUP fcg.fcg_callees fn_name of
      NONE => []
    | SOME callees => callees
End

Definition fcg_get_call_sites_def:
  fcg_get_call_sites fcg fn_name =
    case FLOOKUP fcg.fcg_call_sites fn_name of
      NONE => []
    | SOME sites => sites
End

Definition fcg_is_reachable_def:
  fcg_is_reachable fcg fn_name = MEM fn_name fcg.fcg_reachable
End

Definition fcg_get_unreachable_def:
  fcg_get_unreachable ctx fcg =
    FILTER (\f. ~MEM f.fn_name fcg.fcg_reachable) ctx.ctx_functions
End

Definition reachable_fcg_acyclic_def:
  reachable_fcg_acyclic ctx fcg =
    case ctx.ctx_entry of
      NONE => T
    | SOME entry =>
        let order = fcg_postorder fcg entry in
        EVERY (\caller.
          EVERY (\callee. list_precedes callee caller order)
                (fcg_get_callees fcg caller))
          fcg.fcg_reachable
End

(* ==========================================================================
   Instruction scanning
   ========================================================================== *)

(* Extract (callee_name, instruction) pairs from INVOKE instructions.
 * Silently skips malformed INVOKEs (first operand not a Label);
 * wf_invoke_targets should rule this out. *)
Definition get_invoke_targets_def:
  get_invoke_targets [] = [] /\
  get_invoke_targets (inst::rest) =
    if inst.inst_opcode = INVOKE then
      (case inst.inst_operands of
         (Label lbl)::_ => (lbl, inst) :: get_invoke_targets rest
       | _ => get_invoke_targets rest)
    else get_invoke_targets rest
End

(* All INVOKE targets across every block of a function. *)
Definition fcg_scan_function_def:
  fcg_scan_function func =
    get_invoke_targets (fn_insts func)
End

(* ==========================================================================
   Edge recording
   ========================================================================== *)

(* Record caller->callee edges from invoke targets into the analysis.
 * Uses SNOC for append-order (matching Python reference). *)
Definition fcg_record_edges_def:
  fcg_record_edges fn_name [] fcg = fcg /\
  fcg_record_edges fn_name ((callee, inst)::rest) fcg =
    let callees = fcg_get_callees fcg fn_name in
    let sites = fcg_get_call_sites fcg callee in
    let fcg' = fcg with <|
      fcg_callees := fcg.fcg_callees |+ (fn_name,
        if MEM callee callees then callees else SNOC callee callees);
      fcg_call_sites := fcg.fcg_call_sites |+ (callee,
        if MEM inst sites then sites else SNOC inst sites)
    |> in
    fcg_record_edges fn_name rest fcg'
End

(* Process a single unvisited function: scan for invokes, record edges,
 * mark as reachable, return new callees to explore. *)
Definition fcg_visit_def:
  fcg_visit ctx fn_name fcg =
    case lookup_function fn_name ctx.ctx_functions of
      NONE => ([], fcg)
    | SOME func =>
        let targets = fcg_scan_function func in
        let new_callees = REVERSE (MAP FST targets) in
        let fcg' = fcg_record_edges fn_name targets fcg in
        let fcg'' = fcg' with
          fcg_reachable := SNOC fn_name fcg'.fcg_reachable in
        (new_callees, fcg'')
End

(* ==========================================================================
   Termination helpers
   ========================================================================== *)

Theorem filter_length_mono:
  (!x. P x ==> Q x) ==>
  LENGTH (FILTER P ls) <= LENGTH (FILTER Q ls)
Proof
  strip_tac >> Induct_on `ls` >> simp[] >>
  rw[] >> simp[] >> res_tac >> simp[]
QED

Theorem filter_visited_mono:
  LENGTH (FILTER (\f. ~MEM f.fn_name (name :: visited)) fns) <=
  LENGTH (FILTER (\f. ~MEM f.fn_name visited) fns)
Proof
  irule filter_length_mono >> simp[]
QED

Theorem filter_visited_shrink:
  ~MEM name visited /\
  MEM name (MAP (\f. f.fn_name) fns) ==>
  LENGTH (FILTER (\f. ~MEM f.fn_name (name :: visited)) fns) <
  LENGTH (FILTER (\f. ~MEM f.fn_name visited) fns)
Proof
  Induct_on `fns` >> rw[] >> gvs[] >> simp[filter_visited_mono] >>
  Cases_on `MEM h.fn_name visited` >> gvs[] >> simp[] >>
  irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
  qexists_tac `LENGTH (FILTER (\f. ~MEM f.fn_name visited) fns)` >>
  simp[] >> irule filter_length_mono >> simp[]
QED

Theorem filter_neq_redundant:
  ~MEM name (MAP (\f. f.fn_name) fns) ==>
  FILTER (\f. f.fn_name <> name /\ P f) fns =
  FILTER P fns
Proof
  Induct_on `fns` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

(* ==========================================================================
   DFS worklist traversal

   Terminates because:
    - visited names are skipped (stack shrinks)
    - new names are added to visited (unvisited set shrinks)
    - measure: (|context functions not in visited|, |stack|) lexicographic
   ========================================================================== *)

Definition fcg_dfs_def:
  fcg_dfs ctx [] visited fcg = fcg /\
  fcg_dfs ctx (fn_name::stack) visited fcg =
    if MEM fn_name visited then
      fcg_dfs ctx stack visited fcg
    else
      let (new_callees, fcg') = fcg_visit ctx fn_name fcg in
      fcg_dfs ctx (new_callees ++ stack) (fn_name :: visited) fcg'
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\(ctx, stack, visited, fcg).
       (LENGTH (FILTER (\f. ~MEM f.fn_name visited) ctx.ctx_functions),
        LENGTH stack))` >>
  rpt strip_tac >- simp[] >>
  Cases_on `lookup_function fn_name ctx.ctx_functions` >-
  (disj2_tac >>
   fs[fcg_visit_def] >> gvs[] >>
   imp_res_tac lookup_function_not_mem >>
   simp[filter_neq_redundant]) >>
  (disj1_tac >>
   imp_res_tac lookup_function_mem >>
   irule filter_visited_shrink >> simp[])
End

(* ==========================================================================
   Top-level entry point
   ========================================================================== *)

(* Run the full FCG analysis: if the context has an entry function,
 * DFS from it to discover all reachable callees and call sites. *)
Definition fcg_analyze_def:
  fcg_analyze ctx =
    case ctx.ctx_entry of
      NONE => fcg_empty
    | SOME entry_name =>
        fcg_dfs ctx [entry_name] [] fcg_empty
End

(* ==========================================================================
   Semantic relations
   ========================================================================== *)

(* Direct call edge: fn_a has an INVOKE instruction targeting fn_b.
 * Defined purely from instruction structure — no analysis functions. *)
Definition fn_directly_calls_def:
  fn_directly_calls ctx fn_a fn_b <=>
    ?func inst rest.
      lookup_function fn_a ctx.ctx_functions = SOME func /\
      MEM inst (fn_insts func) /\
      inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label fn_b :: rest
End

(* Reachability = reflexive-transitive closure of direct calls. *)
Definition fcg_path_def:
  fcg_path ctx = RTC (fn_directly_calls ctx)
End
