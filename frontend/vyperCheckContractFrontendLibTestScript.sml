Theory vyperCheckContractFrontendLibTest
Ancestors
  jsonToVyper vyperTypeContract
Libs
  vyperCheckContractFrontendLib

val address = ``0w : address``;
val fixture_dir = "../../../tests/fixtures/check_contract/";

fun check_fixture in_deploy path = let
  val checked = vyperCheckContractFrontendLib.check_contract_file
    {in_deploy = in_deploy, address = address,
     path = fixture_dir ^ path}
  val (_, result) = dest_eq (concl checked)
in
  if optionSyntax.is_some result then ()
  else raise Fail ("frontend contract checker rejected " ^ path)
end;

val _ = check_fixture false "simple.json";
val _ = check_fixture false "storage.json";
val _ = check_fixture false "imported_struct/main.json";
val _ = check_fixture false "imported_flag/main.json";
val _ = check_fixture false "imported_interface/main.json";
val _ = check_fixture false "multimodule_storage/main.json";
val _ = check_fixture false "defaults_control/main.json";
val _ = check_fixture false "transient_storage/main.json";
val _ = check_fixture false "nonreentrant/main.json";
val _ = check_fixture true "deployment/main.json";

val multimodule_path = fixture_dir ^ "multimodule_storage/main.json";
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

val structured = vyperCheckContractFrontendLib.check_contract_result
  {in_deploy = false, address = address,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     (fixture_dir ^ "simple.json"),
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     (fixture_dir ^ "simple.json")};
val _ = if aconv (#modules structured) (#modules (#input structured)) andalso
               aconv (#layouts structured) (#layouts (#input structured)) andalso
               null (free_vars (#artifact structured))
  then () else raise Fail "structured frontend result is inconsistent";

val missing_layout_input =
  {in_deploy = false, address = address, modules = #modules multimodule_input,
   layouts = ``([] : (address # (storage_layout # storage_layout)) list)``};
val _ =
  ((vyperCheckContractLib.check_contract missing_layout_input;
    raise Fail "checker accepted a contract with a missing imported layout")
   handle Fail message =>
     if String.isSubstring "check_contract returned NONE" message then ()
     else raise Fail message);

val _ = export_theory ();
