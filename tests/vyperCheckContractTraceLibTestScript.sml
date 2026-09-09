Theory vyperCheckContractTraceLibTest
Ancestors
  vyperTestRunner
Libs
  vyperCheckContractTraceLib

(* Loading this theory checks the deployment-trace adapter against the concrete
   deployment_trace record API. End-to-end checking is covered through the
   shared frontend preparation tests. *)
val prepare_trace = vyperCheckContractTraceLib.prepare_deployment_trace;
val check_trace = vyperCheckContractTraceLib.check_deployment_trace;

val _ = export_theory ();
