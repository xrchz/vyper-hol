Theory compilerEvalLibTest
Ancestors codegen
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

(* Add context-plan generation independently of instruction planning.  The
   empty context exercises global-reserved/EOM checks and plan finalization,
   while its empty function list means no function planner is invoked. *)
val empty_context = ``mk_venom_context [] NONE``
val empty_context_plan_eval =
  compilerEvalLib.final_codegen_conv
    ``generate_context_plan_fuel 8 ^empty_context``
val empty_context_plan =
  ``SOME <| cp_regions := [];
            cp_max_static_eom := 0;
            cp_peak_spill_end := 0;
            cp_initial_fmp := 0 |>``
val () = if rhs (concl empty_context_plan_eval) ~~ empty_context_plan then ()
         else raise Fail
           ("empty context planning produced: " ^
            term_to_string (rhs (concl empty_context_plan_eval)))

val empty_context_codegen_eval =
  compilerEvalLib.final_codegen_conv
    ``case generate_context_plan_fuel 8 ^empty_context of
        NONE => NONE
      | SOME plan =>
          SOME (assemble
            (execute_plan plan.cp_initial_fmp (context_plan_ops plan)))``
val empty_context_codegen_bytes =
  ``SOME [0x5Bw; 0x5Fw; 0x80w; 0xFDw] : byte list option``
val () =
  if rhs (concl empty_context_codegen_eval) ~~ empty_context_codegen_bytes
  then ()
  else raise Fail "empty context plan-to-bytecode evaluation failed"

(* Introduce a nonempty function list while keeping the function block list
   empty. This crosses into generate_fn_plan_fuel but avoids instruction and
   CFG traversal, giving a small first diagnostic for function planning. *)
val blockless_function =
  ``(mk_raw_function "empty_fn" []) with <|
      fn_eom := SOME 0;
      fn_fmp_signature :=
        SOME <| fms_has_fmp_param := F; fms_publishes := F |> |>``
val blockless_context =
  ``mk_venom_context [^blockless_function] NONE``
val blockless_plan_eval =
  compilerEvalLib.final_codegen_conv
    ``generate_context_plan_fuel 8 ^blockless_context``
val blockless_plan_rhs = rhs (concl blockless_plan_eval)
val () = if optionSyntax.is_none blockless_plan_rhs then ()
         else raise Fail "noncanonical blockless function was not rejected"

(* Evaluate bounded liveness independently before composing it with function
   planning. A STOP-only block has no uses or definitions, so every program
   point has the empty live-variable set. *)
val stop_function =
  ``(mk_raw_function "stop_fn"
       [<| bb_label := "entry";
           bb_instructions := [mk_inst 0 STOP [] []] |>]) with <|
      fn_eom := SOME 0;
      fn_fmp_signature :=
        SOME <| fms_has_fmp_param := F; fms_publishes := F |> |>``
val stop_dfg_eval =
  compilerEvalLib.final_codegen_conv ``dfg_build_function ^stop_function``
val stop_dfg = rhs (concl stop_dfg_eval)
val stop_dfg_lookup_eval = compilerEvalLib.final_codegen_conv
  ``(FLOOKUP (^stop_dfg).dfg_ids 0,
     FLOOKUP (^stop_dfg).dfg_uses "unused",
     FLOOKUP (^stop_dfg).dfg_defs "unused")``
val stop_inst =
  ``<| inst_id := 0; inst_opcode := STOP;
      inst_operands := []; inst_outputs := [] |>``
val stop_dfg_lookups =
  ``(SOME ^stop_inst, NONE, NONE) :
      instruction option # instruction list option # instruction option``
val () = if rhs (concl stop_dfg_lookup_eval) ~~ stop_dfg_lookups then ()
         else raise Fail
           ("single-block STOP DFG produced: " ^
            term_to_string (rhs (concl stop_dfg_lookup_eval)))

val stop_liveness_eval =
  compilerEvalLib.final_codegen_conv ``liveness_analyze_fuel 8 ^stop_function``
val stop_liveness = rhs (concl stop_liveness_eval)
val stop_live_entry_eval = compilerEvalLib.final_codegen_conv
  ``(FLOOKUP (^stop_liveness).ds_boundary "entry",
     FLOOKUP (^stop_liveness).ds_inst ("entry", 0),
     FLOOKUP (^stop_liveness).ds_inst ("entry", 1))``
val stop_live_entry =
  ``(SOME [], SOME [], SOME []) :
      string list option # string list option # string list option``
val () = if rhs (concl stop_live_entry_eval) ~~ stop_live_entry then ()
         else raise Fail "single-block STOP liveness was not empty"

(* Compose the now-independent CFG, DFG, and liveness computations through
   bounded function planning. *)
val stop_plan_eval = compilerEvalLib.final_codegen_conv
  ``generate_fn_plan_fuel 8 ^stop_function 0 0``
val stop_plan_rhs = rhs (concl stop_plan_eval)
val () = if optionSyntax.is_some stop_plan_rhs then ()
         else raise Fail
           ("single-block STOP planning produced: " ^
            term_to_string stop_plan_rhs)

val prague_policy =
  ``<| rpol_target := prague_capabilities;
      rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Optimize |>``

val stop_context = ``mk_venom_context [^stop_function] (SOME "stop_fn")``
val stop_unit =
  ``<| cu_context := ^stop_context; cu_data_segment := [] |>``
val stop_codegen_eval = compilerEvalLib.final_codegen_conv
  ``OPTION_MAP assemble (codegen_assembly_fuel 8 ^prague_policy ^stop_unit)``
val stop_codegen_bytes =
  ``SOME [0x5Bw; 0x00w; 0x5Bw; 0x5Fw; 0x80w; 0xFDw] : byte list option``
val () = if rhs (concl stop_codegen_eval) ~~ stop_codegen_bytes then ()
         else raise Fail
           ("single-block STOP codegen produced: " ^
            term_to_string (rhs (concl stop_codegen_eval)))

(* Evaluate the repository's checked codegen_assembly_fuel definition on the
   same empty context, now including policy and target-safety checks. *)
val empty_unit =
  ``<| cu_context := ^empty_context;
      cu_data_segment := [] |>``
(* Exercise value production and consumption rather than only a terminator.
   ASSIGN of a literal should become a PUSH before the final STOP. *)
val literal_function =
  ``(mk_raw_function "literal_fn"
       [<| bb_label := "entry";
           bb_instructions :=
             [mk_inst 0 ASSIGN [Lit 1w] ["x"];
              mk_inst 1 STOP [] []] |>]) with <|
      fn_eom := SOME 0;
      fn_fmp_signature :=
        SOME <| fms_has_fmp_param := F; fms_publishes := F |> |>``
val literal_context =
  ``mk_venom_context [^literal_function] (SOME "literal_fn")``
val literal_unit =
  ``<| cu_context := ^literal_context; cu_data_segment := [] |>``
val literal_codegen_eval = compilerEvalLib.final_codegen_conv
  ``OPTION_MAP assemble
      (codegen_assembly_fuel 12 ^prague_policy ^literal_unit)``
val literal_codegen_bytes =
  ``SOME [0x5Bw; 0x60w; 0x01w; 0x00w;
          0x5Bw; 0x5Fw; 0x80w; 0xFDw] : byte list option``
val () = if rhs (concl literal_codegen_eval) ~~ literal_codegen_bytes then ()
         else raise Fail
           ("literal ASSIGN codegen produced: " ^
            term_to_string (rhs (concl literal_codegen_eval)))

(* Exercise multiple live values, operand reordering, and a regular binary
   opcode. *)
val add_function =
  ``(mk_raw_function "add_fn"
       [<| bb_label := "entry";
           bb_instructions :=
             [mk_inst 0 ASSIGN [Lit 1w] ["x"];
              mk_inst 1 ASSIGN [Lit 2w] ["y"];
              mk_inst 2 ADD [Var "x"; Var "y"] ["z"];
              mk_inst 3 STOP [] []] |>]) with <|
      fn_eom := SOME 0;
      fn_fmp_signature :=
        SOME <| fms_has_fmp_param := F; fms_publishes := F |> |>``
val add_context = ``mk_venom_context [^add_function] (SOME "add_fn")``
val add_unit = ``<| cu_context := ^add_context; cu_data_segment := [] |>``
val add_codegen_eval = compilerEvalLib.final_codegen_conv
  ``OPTION_MAP assemble (codegen_assembly_fuel 20 ^prague_policy ^add_unit)``
val add_codegen_bytes =
  ``SOME [0x5Bw; 0x60w; 0x01w; 0x60w; 0x02w; 0x01w; 0x00w;
          0x5Bw; 0x5Fw; 0x80w; 0xFDw] : byte list option``
val () = if rhs (concl add_codegen_eval) ~~ add_codegen_bytes then ()
         else raise Fail
           ("binary ADD codegen produced: " ^
            term_to_string (rhs (concl add_codegen_eval)))

(* Exercise multi-block CFG discovery independently before asking the bounded
   planner to traverse branches. *)
val jump_function =
  ``(mk_raw_function "jump_fn"
       [<| bb_label := "entry";
           bb_instructions := [mk_inst 0 JMP [Label "exit"] []] |>;
        <| bb_label := "exit";
           bb_instructions := [mk_inst 1 STOP [] []] |>]) with <|
      fn_eom := SOME 0;
      fn_fmp_signature :=
        SOME <| fms_has_fmp_param := F; fms_publishes := F |> |>``
val jump_cfg_eval = compilerEvalLib.final_codegen_conv
  ``let cfg = cfg_analyze ^jump_function in
      (cfg_succs_of cfg "entry", cfg_preds_of cfg "exit",
       cfg.cfg_dfs_pre, cfg.cfg_dfs_post)``
val jump_cfg =
  ``(["exit"], ["entry"], ["entry"; "exit"], ["exit"; "entry"])``
val () = if rhs (concl jump_cfg_eval) ~~ jump_cfg then ()
         else raise Fail
           ("two-block JMP CFG produced: " ^
            term_to_string (rhs (concl jump_cfg_eval)))

val jump_context = ``mk_venom_context [^jump_function] (SOME "jump_fn")``
val jump_unit = ``<| cu_context := ^jump_context; cu_data_segment := [] |>``
val jump_codegen_eval = compilerEvalLib.final_codegen_conv
  ``OPTION_MAP assemble (codegen_assembly_fuel 12 ^prague_policy ^jump_unit)``
val jump_codegen_bytes =
  ``SOME [0x5Bw; 0x61w; 0x00w; 0x05w; 0x56w; 0x5Bw; 0x00w;
          0x5Bw; 0x5Fw; 0x80w; 0xFDw] : byte list option``
val () = if rhs (concl jump_codegen_eval) ~~ jump_codegen_bytes then ()
         else raise Fail
           ("two-block JMP codegen produced: " ^
            term_to_string (rhs (concl jump_codegen_eval)))

(* Exercise divergent control flow and both symbolic targets of JNZ. *)
val branch_function =
  ``(mk_raw_function "branch_fn"
       [<| bb_label := "entry";
           bb_instructions :=
             [mk_inst 0 ASSIGN [Lit 1w] ["cond"];
              mk_inst 1 JNZ
                [Var "cond"; Label "nonzero"; Label "zero"] []] |>;
        <| bb_label := "nonzero";
           bb_instructions := [mk_inst 2 STOP [] []] |>;
        <| bb_label := "zero";
           bb_instructions := [mk_inst 3 STOP [] []] |>]) with <|
      fn_eom := SOME 0;
      fn_fmp_signature :=
        SOME <| fms_has_fmp_param := F; fms_publishes := F |> |>``
val branch_context =
  ``mk_venom_context [^branch_function] (SOME "branch_fn")``
val branch_unit =
  ``<| cu_context := ^branch_context; cu_data_segment := [] |>``
val branch_codegen_eval = compilerEvalLib.final_codegen_conv
  ``OPTION_MAP assemble
      (codegen_assembly_fuel 24 ^prague_policy ^branch_unit)``
val branch_codegen_bytes =
  ``SOME [0x5Bw; 0x60w; 0x01w; 0x61w; 0x00w; 0x0Dw; 0x57w;
          0x61w; 0x00w; 0x0Bw; 0x56w; 0x5Bw; 0x00w; 0x5Bw; 0x00w;
          0x5Bw; 0x5Fw; 0x80w; 0xFDw] : byte list option``
val () = if rhs (concl branch_codegen_eval) ~~ branch_codegen_bytes then ()
         else raise Fail
           ("three-block JNZ codegen produced: " ^
            term_to_string (rhs (concl branch_codegen_eval)))

val checked_codegen_eval =
  compilerEvalLib.final_codegen_conv
    ``codegen_assembly_fuel 8 ^prague_policy ^empty_unit``
val checked_codegen_asm =
  ``SOME [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"]``
val () = if rhs (concl checked_codegen_eval) ~~ checked_codegen_asm then ()
         else raise Fail
           ("checked empty codegen produced: " ^
            term_to_string (rhs (concl checked_codegen_eval)))

(* The exported instance is immutable while callers may extend a copy. *)
val copied_compset =
  compilerEvalLib.final_codegen_compset |> computeLib.copy
val copied_eval = computeLib.CBV_CONV copied_compset assembly_tm
val () = if rhs (concl copied_eval) ~~ expected_bytes then ()
         else raise Fail "copied final-codegen compset is unusable"
