Theory vyperCheckContractFrontendLibTest
Ancestors
  jsonToVyper vyperTypeContract
Libs
  vyperCheckContractFrontendLib

val address = ``0w : address``;
fun check_fixture path = let
  val checked = vyperCheckContractFrontendLib.check_contract_file
    {in_deploy = false, address = address,
     path = "../../../tests/fixtures/check_contract/" ^ path}
  val (_, result) = dest_eq (concl checked)
in
  if optionSyntax.is_some result then ()
  else raise Fail ("frontend contract checker rejected " ^ path)
end;

val _ = check_fixture "simple.json";
val _ = check_fixture "storage.json";
val _ = check_fixture "imported_struct/main.json";
val _ = check_fixture "imported_flag/main.json";
val _ = check_fixture "imported_interface/main.json";
val _ = check_fixture "multimodule_storage/main.json";

val multimodule_path =
  "../../../tests/fixtures/check_contract/multimodule_storage/main.json";
val multimodule_input = vyperCheckContractFrontendLib.prepare_check_input
  {in_deploy = false, address = address,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     multimodule_path,
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     multimodule_path};
val expected_multimodule_layout =
  ``[(0w : address,
      ([((SOME 3, "stored"), 0)] : storage_layout,
       [] : storage_layout))]``;
val _ = if aconv (#layouts multimodule_input) expected_multimodule_layout then ()
  else raise Fail "multi-module storage layout did not preserve source identity";

val _ = export_theory ();
