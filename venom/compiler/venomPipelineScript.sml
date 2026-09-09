(*
 * Venom IR Optimization Pipeline Compatibility Rollup
 *
 * Upstream: vyperlang/vyper@a7f7bf133 (split algebraic/affine passes)
 *
 * Defines legacy/model pass sequences for O2, O3, and Os optimization levels,
 * matching Python's vyper/venom/optimization_levels/*.py.  Their
 * lower_dload_function occurrences are the arithmetic-ID semantic model, not a
 * configured executable entry point.  Future configured unit composition must
 * invoke lower_dload_configured once at the compilation-unit boundary instead.
 *
 * The pipeline has two phases:
 *   Phase 1 (global, pre-inlining):
 *     simplify_cfg, ircf, ricf, function_inliner
 *   Phase 2 (per-function, post-inlining):
 *     level-specific pass list
 *
 * Passes that need pre-computed analysis are curried with their
 * analysis function (e.g. dse_function analysis_fn, concretize_function
 * amap).
 *
 * sccp_function returns option (NONE on static assertion failure).
 * sccp_unwrap provides identity fallback.
 *
 * phi_elimination and rta both export "transform_function" --
 * qualified names (phiTransform$, rtaDefs$) disambiguate.
 *
 * mem_merge is not formalized (omitted from all levels).
 * fix_mem_locations is pending deletion upstream (omitted).
 *
 * TOP-LEVEL:
 *   o2_fn_passes           -- O2 per-function pass sequence
 *   o3_fn_passes           -- O3 per-function pass sequence
 *   os_fn_passes           -- Os per-function pass sequence
 *   venom_pipeline         -- full pipeline (parameterized by level)
 *   apply_ctx_fn_transform -- lift fn transform to context level
 *)

Theory venomPipeline
Ancestors
  (* configured checked driver/runner and their structural boundary properties *)
  venomPipelineDriverProps venomPipelineRunnerProps
  phiTransform
  assignElimDefs
  rtaDefs
  sccpDefs
  removeUnusedDefs
  mem2varDefs
  memoryCopyElisionDefs
  loadElimDefs
  concretizeMemLocDefs
  deadStoreElimDefs
  simplifyCfgDefs
  cfgNormDefs
  tailMergeDefs
  branchOptDefs
  lowerDloadDefs
  singleUseExpansionDefs
  literalsCodesizeDefs
  cseDefs
  algebraicOptDefs
  affineFoldingDefs
  assertElimDefs
  overflowElimDefs
  assertCombinerDefs
  internalReturnCopyFwdDefs
  readonlyInvokeCopyFwdDefs
  dftDefs
  functionInlinerDefs
  makeSsaDefs

(* ===== Infrastructure ===== *)

Definition apply_ctx_fn_transform_def:
  apply_ctx_fn_transform (f : ir_function -> ir_function)
                          (ctx : venom_context) : venom_context =
    ctx with ctx_functions := MAP f ctx.ctx_functions
End

Definition sccp_unwrap_def:
  sccp_unwrap fn = case sccp_function fn of SOME fn' => fn' | NONE => fn
End

(* ===== Per-Function Pass Sequences ===== *)

(* O2: standard optimizations.
   Curried parameters are analyses computed per-function:
     make_ssa     -- SSA construction (needs dom tree, liveness, etc.)
     ircf         -- internal return copy fwd (curried with fn_meta, rma)
     ricf         -- readonly invoke copy fwd (curried with fn_meta, rma)
     dse_analysis -- dead store analysis (addr_space -> fn -> dead ids)
     amap         -- allocation map for memory concretization
     live_at      -- liveness for branch optimization *)
Definition o2_fn_passes_def:
  o2_fn_passes make_ssa ircf ricf dse_analysis amap live_at fn =
    let fn = simplify_cfg_fn fn in
    let fn = make_ssa fn in
    let fn = phiTransform$transform_function fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    let fn = assign_elim_function fn in
    let fn = m2v_transform_function fn in
    let fn = make_ssa fn in
    let fn = phiTransform$transform_function fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    let fn = assign_elim_function fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = load_elim_function fn in
    let fn = phiTransform$transform_function fn in
    let fn = assign_elim_function fn in
    let fn = sccp_unwrap fn in
    let fn = assign_elim_function fn in
    let fn = rtaDefs$transform_function fn in
    let fn = simplify_cfg_fn fn in
    let fn = ircf fn in
    let fn = ricf fn in
    (* mem_merge omitted *)
    let fn = copy_elision_function fn in
    let fn = load_elim_function fn in
    let fn = lower_dload_function fn in
    let fn = remove_unused_function fn in
    let fn = dse_function dse_analysis fn in
    let fn = assign_elim_function fn in
    let fn = remove_unused_function fn in
    let fn = concretize_function amap fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    (* mem_merge omitted *)
    let fn = load_elim_function fn in
    let fn = remove_unused_function fn in
    let fn = branch_opt_function live_at fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = ac_transform_function fn in
    let fn = remove_unused_function fn in
    let fn = phiTransform$transform_function fn in
    let fn = assign_elim_function fn in
    let fn = cse_function fn in
    let fn = assign_elim_function fn in
    let fn = remove_unused_function fn in
    let fn = sue_expand_function fn in
    let fn = dft_fn fn in
    cfg_norm_fn fn
End

(* O3: aggressive optimizations.
   Adds assert_elim, overflow_elim, tail_merge,
   lit_codesize, second copy_elision run. *)
Definition o3_fn_passes_def:
  o3_fn_passes make_ssa ircf ricf dse_analysis amap live_at fn =
    let fn = simplify_cfg_fn fn in
    let fn = make_ssa fn in
    let fn = phiTransform$transform_function fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    let fn = assign_elim_function fn in
    let fn = m2v_transform_function fn in
    let fn = make_ssa fn in
    let fn = phiTransform$transform_function fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    let fn = assign_elim_function fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = assert_elim_function fn in        (* O3 only *)
    let fn = overflow_elim_function fn in      (* O3 only *)
    let fn = load_elim_function fn in
    let fn = phiTransform$transform_function fn in
    let fn = assign_elim_function fn in
    let fn = sccp_unwrap fn in
    let fn = assign_elim_function fn in
    let fn = rtaDefs$transform_function fn in
    let fn = simplify_cfg_fn fn in
    let fn = ircf fn in
    let fn = ricf fn in
    (* mem_merge omitted *)
    let fn = copy_elision_function fn in
    let fn = load_elim_function fn in
    let fn = lower_dload_function fn in
    let fn = remove_unused_function fn in
    let fn = dse_function dse_analysis fn in
    let fn = assign_elim_function fn in
    let fn = remove_unused_function fn in
    let fn = concretize_function amap fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    (* mem_merge omitted *)
    let fn = load_elim_function fn in
    let fn = copy_elision_function fn in   (* O3 only: second MCE *)
    let fn = remove_unused_function fn in
    let fn = branch_opt_function live_at fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = ac_transform_function fn in
    let fn = remove_unused_function fn in
    let fn = phiTransform$transform_function fn in
    let fn = assign_elim_function fn in
    let fn = cse_function fn in
    let fn = assign_elim_function fn in
    let fn = remove_unused_function fn in
    let fn = tail_merge_fn fn in               (* O3 only *)
    let fn = simplify_cfg_fn fn in             (* O3 only *)
    let fn = sue_expand_function fn in
    let fn = lit_codesize_function fn in       (* O3 only *)
    let fn = dft_fn fn in
    cfg_norm_fn fn
End

(* Os: optimize for size. O2 + ReduceLiteralsCodesize before DFT. *)
Definition os_fn_passes_def:
  os_fn_passes make_ssa ircf ricf dse_analysis amap live_at fn =
    let fn = simplify_cfg_fn fn in
    let fn = make_ssa fn in
    let fn = phiTransform$transform_function fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    let fn = assign_elim_function fn in
    let fn = m2v_transform_function fn in
    let fn = make_ssa fn in
    let fn = phiTransform$transform_function fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    let fn = assign_elim_function fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = load_elim_function fn in
    let fn = phiTransform$transform_function fn in
    let fn = assign_elim_function fn in
    let fn = sccp_unwrap fn in
    let fn = assign_elim_function fn in
    let fn = rtaDefs$transform_function fn in
    let fn = simplify_cfg_fn fn in
    let fn = ircf fn in
    let fn = ricf fn in
    (* mem_merge omitted *)
    let fn = copy_elision_function fn in
    let fn = load_elim_function fn in
    let fn = lower_dload_function fn in
    let fn = remove_unused_function fn in
    let fn = dse_function dse_analysis fn in
    let fn = assign_elim_function fn in
    let fn = remove_unused_function fn in
    let fn = concretize_function amap fn in
    let fn = sccp_unwrap fn in
    let fn = simplify_cfg_fn fn in
    (* mem_merge omitted *)
    let fn = load_elim_function fn in
    let fn = remove_unused_function fn in
    let fn = branch_opt_function live_at fn in
    let fn = af_transform_function fn in
    let fn = ao_transform_function fn in
    let fn = ac_transform_function fn in
    let fn = remove_unused_function fn in
    let fn = phiTransform$transform_function fn in
    let fn = assign_elim_function fn in
    let fn = cse_function fn in
    let fn = assign_elim_function fn in
    let fn = remove_unused_function fn in
    let fn = sue_expand_function fn in
    let fn = lit_codesize_function fn in       (* Os only vs O2 *)
    let fn = dft_fn fn in
    cfg_norm_fn fn
End

(* ===== Full Pipeline ===== *)

(* Phase 1: global passes (from _run_global_passes in __init__.py).
   Phase 2: per-function passes from the optimization level.
   fn_pipeline is one of o2/o3/os_fn_passes with analysis args curried. *)
Definition venom_pipeline_def:
  venom_pipeline ircf_global ricf_global threshold fn_pipeline
                  (ctx : venom_context) =
    let ctx = apply_ctx_fn_transform simplify_cfg_fn ctx in
    let ctx = apply_ctx_fn_transform ircf_global ctx in
    let ctx = apply_ctx_fn_transform ricf_global ctx in
    let ctx = function_inliner_ctx threshold ctx in
    apply_ctx_fn_transform fn_pipeline ctx
End
