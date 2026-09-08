structure vyperCheckContractFrontendLib :> vyperCheckContractFrontendLib = struct

open HolKernel boolLib
open jsonToVyperTheory

 type frontend_input =
  {in_deploy : bool,
   address : term,
   annotated_ast : term,
   storage_layout : term}

fun require_closed what tm =
  if null (free_vars tm) then ()
  else raise Fail ("vyperCheckContractFrontendLib: open " ^ what)

fun eval_closed what tm = let
  val () = require_closed what tm
  val thm = bossLib.EVAL tm
  val () = if null (hyp thm) then ()
    else raise Fail ("vyperCheckContractFrontendLib: assumptions evaluating " ^ what)
  val (lhs, result) = dest_eq (concl thm)
  val () = if aconv lhs tm then ()
    else raise Fail ("vyperCheckContractFrontendLib: unexpected theorem for " ^ what)
  val () = require_closed (what ^ " result") result
in result end

fun inst_apply function argument = let
  val (domain_ty, _) = dom_rng (type_of function)
  val instantiated = Term.inst
    (Type.match_type domain_ty (type_of argument)) function
in mk_comb (instantiated, argument) end

fun apply name arguments =
  foldl (fn (argument, function) => inst_apply function argument)
    (prim_mk_const {Thy = "jsonToVyper", Name = name}) arguments

fun prepare_check_input
    {in_deploy, address, annotated_ast, storage_layout} = let
  val () = app (fn (name, tm) => require_closed name tm)
    [("address", address), ("annotated AST", annotated_ast),
     ("storage layout", storage_layout)]
  val translation = eval_closed "annotated AST translation"
    (apply "translate_annotated_ast" [annotated_ast])
  val translated = optionSyntax.dest_some translation
    handle HOL_ERR _ => raise Fail
      "vyperCheckContractFrontendLib: annotated AST translation rejected"
  val (sources, rest) = pairSyntax.dest_pair translated
  val (_, import_map) = pairSyntax.dest_pair rest
  val modules = eval_closed "storage-slot annotation"
    (apply "annotate_sources_slots" [storage_layout, sources])
  val layout_pair = eval_closed "storage layout extraction"
    (apply "extract_storage_layout" [import_map, storage_layout])
  val layout_entry = pairSyntax.mk_pair (address, layout_pair)
  val layouts = listSyntax.mk_list ([layout_entry], type_of layout_entry)
in
  {in_deploy = in_deploy, layouts = layouts,
   address = address, modules = modules}
end

fun check_contract input =
  vyperCheckContractLib.check_contract (prepare_check_input input)

fun check_contract_file {in_deploy, address, path} =
  check_contract
    {in_deploy = in_deploy,
     address = address,
     annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path,
     storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout path}

end
