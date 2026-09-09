structure vyperCheckContractTraceLib :> vyperCheckContractTraceLib = struct

open HolKernel
open vyperTestRunnerTheory

fun record_field name fields =
  case List.find (fn (field_name, _) => field_name = name) fields of
    SOME (_, value) => value
  | NONE => raise Fail
      ("vyperCheckContractTraceLib: missing deployment field " ^ name)

fun prepare_deployment_trace deployment = let
  val () = if null (free_vars deployment) then ()
    else raise Fail "vyperCheckContractTraceLib: open deployment trace"
  val (_, fields) = TypeBase.dest_record deployment
    handle HOL_ERR _ => raise Fail
      "vyperCheckContractTraceLib: expected deployment_trace record"
in
  vyperCheckContractFrontendLib.prepare_translated_input
    {in_deploy = true,
     address = record_field "deployedAddress" fields,
     sources = record_field "sourceAst" fields,
     import_map = record_field "importMap" fields,
     storage_layout = record_field "storageLayout" fields}
end

fun check_deployment_trace deployment =
  vyperCheckContractLib.check_contract
    (prepare_deployment_trace deployment)

end
