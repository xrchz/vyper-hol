signature vyperCheckContractFrontendLib = sig

  type frontend_input =
    {in_deploy : bool,
     address : Term.term,
     annotated_ast : Term.term,
     storage_layout : Term.term}

  type translated_input =
    {in_deploy : bool,
     address : Term.term,
     sources : Term.term,
     import_map : Term.term,
     storage_layout : Term.term}

  val prepare_translated_input :
    translated_input -> vyperCheckContractLib.check_input
  val prepare_check_input :
    frontend_input -> vyperCheckContractLib.check_input

  type checked_result =
    {input : vyperCheckContractLib.check_input,
     modules : Term.term,
     layouts : Term.term,
     address : Term.term,
     artifact : Term.term,
     theorem : Thm.thm}

  val check_contract_result : frontend_input -> checked_result
  val check_contract : frontend_input -> Thm.thm

  val check_contract_file :
    {in_deploy : bool, address : Term.term, path : string} -> Thm.thm

end
