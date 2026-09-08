structure vyperCheckContractLib :> vyperCheckContractLib = struct

open HolKernel boolLib bossLib
open vyperASTTheory vyperContextTheory vyperInterpreterTheory
open vyperTypeCallGraphTheory vyperTypeContractTheory vyperTypeSystemTheory

 type check_input =
  {in_deploy : bool,
   layouts : term,
   address : term,
   modules : term}

val checker_defs =
  [check_contract_def,
   check_module_def,
   check_toplevel_body_def,
   check_function_body_def,
   check_toplevel_decl_def,
   check_value_type_def,
   artifact_env_def,
   function_entry_env_def,
   params_ok_def,
   lookup_var_slot_in_layouts_def,
   build_contract_type_artifact_def,
   add_module_static_maps_def,
   add_toplevel_static_maps_def,
   empty_contract_type_artifact_def,
   contract_type_artifact_accessors,
   contract_type_artifact_fn_updates,
   contract_type_artifact_updates_eq_literal,
   typing_env_accessors,
   typing_env_fn_updates,
   typing_env_updates_eq_literal,
   fn_sig_accessors,
   fn_sig_fn_updates,
   include_fn_sig_def,
   fn_sig_of_def,
   contract_namespaces_ok_def,
   contract_keys_def,
   fn_sig_keys_toplevel_def,
   toplevel_vtype_keys_toplevel_def,
   flag_member_keys_toplevel_def,
   type_def_keys_toplevel_def,
   contract_call_graph_acyclic_def,
   call_graph_acyclic_def,
   contract_call_nodes_def,
   contract_call_edges_def,
   module_call_edges_def,
   toplevel_call_edges_def,
   function_int_calls_def,
   int_calls_expr_def,
   int_calls_atarget_def,
   int_calls_iterator_def,
   int_calls_assert_reason_def,
   int_calls_raise_reason_def,
   int_calls_stmt_def,
   direct_callees_def,
   reachable_nodes_def,
   type_env_all_modules_def,
   type_env_for_module_def,
   lookup_nonreentrant_slot_def,
   lookup_function_def,
   lookup_callable_function_def,
   well_formed_type_def,
   assignable_type_def,
   hashmap_key_type_def,
   defaults_env_def,
   extend_local_def,
   well_typed_expr_def,
   well_typed_target_def,
   well_typed_atarget_def,
   well_typed_iterator_def,
   type_stmt_def,
   well_typed_stmt_def,
   well_typed_stmts_def,
   stmt_no_fallthrough_def,
   stmt_no_control_escape_def,
   vyperMiscTheory.string_to_num_def,
   vyperValueTheory.evaluate_type_def,
   vyperValueTheory.type_slot_size_def,
   vyperValueTheory.compatible_bound_def,
   vyperValueTheory.within_int_bound_def,
   expr_type_def,
   well_typed_literal_def,
   well_typed_binop_def,
   well_typed_builtin_app_def,
   is_int_type_def,
   bound_at_most_def,
   vtype_annotation_ok_def,
   subscript_type_ok_def,
   subscript_vtype_def,
   attribute_type_def,
   attribute_type_ok_def,
   well_typed_type_builtin_args_def,
   type_builtin_result_ok_def,
   raw_call_return_type_def,
   create_arg_types_ok_def,
   optionTheory.option_case_lazily,
   optionTheory.IS_SOME_DEF,
   pairTheory.FST,
   pairTheory.SND,
   pred_setTheory.NOT_IN_EMPTY]

(* Work around HOL issue #2055. list_compset can route membership through
   LIST_TO_SET and leave closed ALL_DISTINCT terms unreduced. *)
fun list_mem_conv eval =
  REWR_CONV (CONJUNCT1 listTheory.MEM) ORELSEC
  (REWR_CONV (CONJUNCT2 listTheory.MEM) THENC eval)

fun add_all_distinct_workaround cs = let
  val cs = computeLib.scrub_const cs ``list$LIST_TO_SET``
  val cs = computeLib.scrub_const cs ``bool$IN``
  val eval = computeLib.CBV_CONV cs
  val cs = computeLib.add_conv (``bool$IN``, 2, list_mem_conv eval) cs
  val cs = computeLib.scrub_const cs ``list$ALL_DISTINCT``
  val cs = computeLib.scrub_const cs ``list$nub``
in
  computeLib.add_thms [listTheory.ALL_DISTINCT, listTheory.nub_def] cs
end

(* This is deliberately fixed rather than derived from the global TypeBase. *)
val checker_datatypes =
  [``:vyperAST$toplevel``, ``:vyperAST$expr``, ``:vyperAST$stmt``,
   ``:vyperAST$type``, ``:vyperAST$base_type``, ``:vyperAST$value_type``,
   ``:vyperTypeContract$contract_type_artifact``,
   ``:vyperTypeSystem$typing_env``, ``:vyperTypeSystem$fn_sig``,
   ``:vyperAST$variable_mutability``, ``:vyperValue$type_args``,
   ``:vyperAST$bound``, ``:vyperAST$raw_call_flags``, ``:string$char``,
   ``:'a list``, ``:'a option``, ``:'a # 'b``]

fun build_checker_base () =
  reduceLib.num_compset
  |> computeLib.copy
  |> intReduce.add_int_compset
  |> wordsLib.add_words_compset false
  |> finite_mapLib.add_finite_map_compset
  |> alistLib.add_alist_compset
  |> pred_setLib.add_pred_set_compset
  |> stringLib.add_string_compset
  |> computeLib.extend_compset [computeLib.Tys checker_datatypes]
  |> computeLib.add_thmset "compute"
  |> computeLib.add_thms checker_defs
  |> add_all_distinct_workaround

fun eta_expand_quantifier_predicate tm = let
  val (quantifier, predicate) = dest_comb tm
  val (domain_ty, _) = dom_rng (type_of predicate)
  val bound = genvar domain_ty
  val expanded = mk_abs (bound, mk_comb (predicate, bound))
in
  AP_TERM quantifier (SYM (ETA_CONV expanded))
end

(* ML libraries are loaded before a script establishes its current theory.
   Construct on first use so the registered "compute" theorem set is available,
   then retain the same sealed compset for every subsequent call. *)
val cached_check_contract_compset : computeLib.compset option ref = ref NONE

fun make_check_contract_compset () = let
  (* This inner compset has no quantifier hooks, avoiding recursive invocation
     of the outer hook while a closed predicate body is normalized. *)
  val quantifier_body_conv = computeLib.CBV_CONV (build_checker_base ())
  val normalize_quantifier_predicate =
    SIMP_CONV bool_ss [vyperASTTheory.type_distinct]
  fun determined_quantifier_conv tm =
    (normalize_quantifier_predicate THENC
     TRY_CONV quantHeuristicsLib.SIMPLE_QUANT_INSTANTIATE_CONV THENC
     quantifier_body_conv THENC
     TRY_CONV eta_expand_quantifier_predicate THENC
     TRY_CONV quantHeuristicsLib.SIMPLE_QUANT_INSTANTIATE_CONV THENC
     quantifier_body_conv) tm
  fun normalized_universal_conv tm =
    (RAND_CONV (ABS_CONV quantifier_body_conv) THENC
     SIMP_CONV bool_ss [vyperASTTheory.type_distinct]) tm
in
  build_checker_base ()
  |> computeLib.add_conv
       (boolSyntax.existential, 1, determined_quantifier_conv)
  |> computeLib.add_conv
       (boolSyntax.universal, 1, normalized_universal_conv)
  |> computeLib.seal
end

fun check_contract_compset () = case !cached_check_contract_compset of
    SOME cs => cs
  | NONE => let
      val cs = make_check_contract_compset ()
      val () = cached_check_contract_compset := SOME cs
    in cs end

fun check_contract_conv tm =
  computeLib.CBV_CONV (check_contract_compset ()) tm

fun inst_apply function argument = let
  val (domain_ty, _) = dom_rng (type_of function)
  val instantiated = Term.inst
    (Type.match_type domain_ty (type_of argument)) function
in
  mk_comb (instantiated, argument)
end

fun mk_check_contract {in_deploy, layouts, address, modules} =
  let
    val arguments = [boolSyntax.mk_bool in_deploy, layouts, address, modules]
    val () = if List.all (null o free_vars) arguments then ()
      else raise Fail "check_contract input is open"
    val checker = prim_mk_const
      {Thy = "vyperTypeContract", Name = "check_contract"}
  in
    foldl (fn (argument, applied) => inst_apply applied argument)
      checker arguments
  end

fun check_contract_with conversion input = let
  val application = mk_check_contract input
  val theorem = conversion application
  val () = if null (hyp theorem) then ()
    else raise Fail "check_contract theorem has assumptions"
  val (lhs, result) = dest_eq (concl theorem)
  val () = if aconv lhs application then ()
    else raise Fail "check_contract theorem has an unexpected left-hand side"
  val artifact = if optionSyntax.is_some result
    then optionSyntax.dest_some result
    else raise Fail ("check_contract returned " ^ term_to_string result)
  val () = if null (free_vars artifact) then ()
    else raise Fail "check_contract returned an open artifact"
in
  theorem
end

fun check_contract input = check_contract_with check_contract_conv input

end
