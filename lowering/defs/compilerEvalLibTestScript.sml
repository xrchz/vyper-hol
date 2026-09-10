Theory compilerEvalLibTest
Ancestors symbolResolve
Libs compilerEvalLib

val plan_tm =
  ``execute_plan 64
      [SOInitialFmp; SOEmit "MSTORE"; SOLabel "done";
       SOPushLabel "done"]``

val plan_eval = compilerEvalLib.final_codegen_conv plan_tm
val expected_asm =
  ``[AsmPush [0x40w]; AsmOp "MSTORE"; AsmLabel "done";
     AsmPushLabel "done"]``
val () = if rhs (concl plan_eval) ~~ expected_asm then ()
         else raise Fail "incremental plan evaluation produced unexpected assembly"

val assembly_tm = ``assemble ^expected_asm``
val assembly_eval = compilerEvalLib.final_codegen_conv assembly_tm
val expected_bytes =
  ``[0x60w; 0x40w; 0x52w; 0x5Bw; 0x61w; 0x00w; 0x03w] : byte list``
val () = if rhs (concl assembly_eval) ~~ expected_bytes then ()
         else raise Fail ("incremental assembly evaluation produced: " ^
                          term_to_string (rhs (concl assembly_eval)))

val composed_eval =
  compilerEvalLib.final_codegen_conv ``assemble ^plan_tm``
val () = if rhs (concl composed_eval) ~~ expected_bytes then ()
         else raise Fail "composed final-codegen evaluation produced unexpected bytes"

(* Expand the boundary to an already-generated context plan plus data segment.
   Planning itself is deliberately not part of this layer yet. *)
val supplied_plan =
  ``<| cp_regions :=
        [<| sr_fn_name := "foo"; sr_spill_base := 64;
            sr_spill_end := 64;
            sr_plan := [SOInitialFmp; SOEmit "MSTORE"; SOLabel "done";
                        SOPushLabel "done"] |>];
      cp_max_static_eom := 64;
      cp_peak_spill_end := 0;
      cp_initial_fmp := 64 |>``
val supplied_data =
  ``[<| ds_label := "blob";
        ds_items := [DataBytes [0xAAw; 0xBBw]] |>]``
val supplied_tail_tm =
  ``assemble
      (execute_plan (^supplied_plan).cp_initial_fmp
         (context_plan_ops ^supplied_plan) ++
       data_segment_asm ^supplied_data)``
val supplied_tail_eval =
  compilerEvalLib.final_codegen_conv supplied_tail_tm
val supplied_tail_bytes =
  ``[0x60w; 0x40w; 0x52w; 0x5Bw; 0x61w; 0x00w; 0x03w;
     0x5Bw; 0x5Fw; 0x80w; 0xFDw; 0xAAw; 0xBBw] : byte list``
val () = if rhs (concl supplied_tail_eval) ~~ supplied_tail_bytes then ()
         else raise Fail
           ("supplied-plan codegen tail produced: " ^
            term_to_string (rhs (concl supplied_tail_eval)))

(* The exported instance is immutable while callers may extend a copy. *)
val copied_compset =
  compilerEvalLib.final_codegen_compset |> computeLib.copy
val copied_eval = computeLib.CBV_CONV copied_compset assembly_tm
val () = if rhs (concl copied_eval) ~~ expected_bytes then ()
         else raise Fail "copied final-codegen compset is unusable"
