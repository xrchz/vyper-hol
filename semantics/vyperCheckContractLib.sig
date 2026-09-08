signature vyperCheckContractLib = sig

  type check_input =
    {in_deploy : bool,
     layouts : Term.term,
     address : Term.term,
     modules : Term.term}

  val check_contract_compset : unit -> computeLib.compset
  val check_contract_conv : Conv.conv

  val mk_check_contract : check_input -> Term.term
  val check_contract_with : Conv.conv -> check_input -> Thm.thm
  val check_contract : check_input -> Thm.thm

end
