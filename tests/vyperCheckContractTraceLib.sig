signature vyperCheckContractTraceLib = sig

  val prepare_deployment_trace :
    Term.term -> vyperCheckContractLib.check_input

  val check_deployment_trace : Term.term -> Thm.thm

end
