signature vyperCheckContractFrontendLib = sig

  type frontend_input =
    {in_deploy : bool,
     address : Term.term,
     annotated_ast : Term.term,
     storage_layout : Term.term}

  val prepare_check_input :
    frontend_input -> vyperCheckContractLib.check_input

  val check_contract : frontend_input -> Thm.thm

  val check_contract_file :
    {in_deploy : bool, address : Term.term, path : string} -> Thm.thm

end
