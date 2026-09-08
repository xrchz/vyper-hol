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

val _ = export_theory ();
