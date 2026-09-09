structure vyperCheckContractLib :> vyperCheckContractLib = struct

open HolKernel boolLib bossLib
open vyperASTTheory vyperContextTheory vyperInterpreterTheory
open vyperTypeCallGraphTheory vyperTypeContractTheory vyperTypeSystemTheory

 type check_input =
  {in_deploy : bool,
   layouts : term,
   address : term,
   modules : term}

val in_empty_eq =
  pred_setTheory.NOT_IN_EMPTY |> SPEC_ALL |> EQF_INTRO |> GEN_ALL

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
   fn_sig_component_equality,
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
   reachable_nodes_compute,
   type_env_all_modules_def,
   type_env_for_module_def,
   lookup_nonreentrant_slot_def,
   lookup_function_def,
   lookup_callable_function_def,
   well_formed_type_def,
   is_numeric_type_def,
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
   optionTheory.THE_DEF,
   pairTheory.FST,
   pairTheory.SND,
   pairTheory.UNCURRY_DEF,
   numposrepTheory.l2n_def]

(* Work around HOL issue #2055. Install empty-set membership before the list
   rules so ALL_DISTINCT does not retain the problematic prior IN treatment. *)
fun add_list_compset cs =
  cs
  |> pred_setLib.add_pred_set_compset
  |> (fn cs' => computeLib.scrub_const cs' ``bool$IN``)
  |> computeLib.add_thms [in_empty_eq]
  |> listSimps.list_rws
  |> pred_setLib.add_pred_set_compset

(* This is deliberately fixed rather than derived from the global TypeBase. *)
val checker_datatypes =
  [``:vyperAST$toplevel``, ``:vyperAST$expr``, ``:vyperAST$stmt``,
   ``:vyperAST$type``, ``:vyperAST$base_type``, ``:vyperAST$value_type``,
   ``:vyperAST$int_bound``, ``:vyperAST$literal``, ``:vyperAST$binop``,
   ``:vyperAST$env_item``, ``:vyperAST$account_item``,
   ``:vyperAST$denomination``, ``:vyperAST$builtin``,
   ``:vyperAST$create_kind``, ``:vyperAST$call_target``,
   ``:vyperAST$type_builtin``, ``:vyperAST$assignment_target``,
   ``:vyperAST$iterator``, ``:vyperAST$assert_reason``,
   ``:vyperAST$raise_reason``, ``:vyperAST$function_visibility``,
   ``:vyperAST$function_mutability``, ``:vyperAST$variable_visibility``,
   ``:vyperTypeContract$contract_type_artifact``,
   ``:vyperTypeSystem$typing_env``, ``:vyperTypeSystem$fn_sig``,
   ``:vyperAST$variable_mutability``, ``:vyperValue$type_args``,
   ``:vyperAST$bound``, ``:vyperAST$raw_call_flags``, ``:string$char``,
   ``:'a list``, ``:'a option``, ``:'a # 'b``]

fun build_checker_base () =
  reduceLib.num_compset
  |> computeLib.copy
  |> add_list_compset
  |> combinLib.add_combin_compset
  |> numposrepLib.add_numposrep_compset
  |> ASCIInumbersLib.add_ASCIInumbers_compset
  |> intReduce.add_int_compset
  |> wordsLib.add_words_compset false
  |> finite_mapLib.add_finite_map_compset
  |> alistLib.add_alist_compset
  |> stringLib.add_string_compset
  |> computeLib.extend_compset [computeLib.Tys checker_datatypes]
  |> computeLib.add_thms checker_defs

fun eta_expand_quantifier_predicate tm = let
  val (quantifier, predicate) = dest_comb tm
  val (domain_ty, _) = dom_rng (type_of predicate)
  val bound = genvar domain_ty
  val expanded = mk_abs (bound, mk_comb (predicate, bound))
in
  AP_TERM quantifier (SYM (ETA_CONV expanded))
end

val check_contract_compset = let
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

fun check_contract_conv tm =
  computeLib.CBV_CONV check_contract_compset tm

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
