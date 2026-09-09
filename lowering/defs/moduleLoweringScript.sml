(*
 * Module-Level Lowering: selector dispatch, external/internal functions,
 * constructor, deploy code
 *
 * TOP-LEVEL:
 *   compile_selector_dispatch_linear — O(n) linear selector matching
 *   compile_selector_dispatch_sparse — O(1) binary search on selectors
 *   compile_selector_dispatch_dense  — O(1) dense jumptable dispatch
 *   compile_internal_function       — internal function with PARAM/RET
 *   compile_entry_checks           — calldatasize + payable checks
 *   compile_constructor_epilogue   — deploy: copy runtime + RETURN
 *   compile_simple_deploy           — deploy without constructor
 *   compile_external_entry_points  — entry points for external fn w/ kwargs
 *   compile_decode_args             — unified arg decode (calldata / data section)
 *   compile_register_positional_args — wrapper: calldata positional args
 *   compile_register_constructor_args — wrapper: data section constructor args
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/module.py
 *)

Theory moduleLowering
Ancestors
  stmtLowering exprLowering context abiEncoder compileEnv venomInst
  jumptableUtils
Libs
  monadsyntax

(* SELECTOR_BYTES = 4, SELECTOR_SHIFT_BITS = 224 *)

(* Iterate through selectors, emit comparison + conditional jump *)
Definition compile_selector_checks_def:
  compile_selector_checks method_id [] = return () ∧
  compile_selector_checks method_id ((sel, fn_label)::rest) =
    do match_op <- emit_op EQ [method_id; Lit (n2w sel)];
       match_lbl <- fresh_label "match";
       next_lbl <- fresh_label "next";
       emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [];
       new_block match_lbl;
       emit_inst JMP [Label fn_label] [];
       new_block next_lbl;
       compile_selector_checks method_id rest
    od
End

(* ===== Linear Selector Dispatch ===== *)
Definition compile_selector_dispatch_linear_def:
  compile_selector_dispatch_linear selectors fallback_lbl =
    do cds <- emit_op CALLDATASIZE [];
       has_sel <- emit_op LT [cds; Lit 4w];
       has_sel2 <- emit_op ISZERO [has_sel];
       dispatch_lbl <- fresh_label "dispatch";
       emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [];
       new_block dispatch_lbl;
       raw <- emit_op CALLDATALOAD [Lit 0w];
       method_id <- emit_op SHR [Lit 224w; raw];
       compile_selector_checks method_id selectors;
       emit_inst JMP [Label fallback_lbl] []
    od
End

(* ===== Sparse Bucket Linear Search ===== *)
Definition compile_sparse_bucket_search_def:
  compile_sparse_bucket_search method_id_var [] fallback_lbl =
    emit_inst JMP [Label fallback_lbl] [] ∧
  compile_sparse_bucket_search method_id_var
      ((selector, func_lbl, has_trailing_zeroes) :: rest) fallback_lbl =
    do match_lbl <- fresh_label "match";
       next_lbl <- fresh_label "next_check";
       is_match <- emit_op EQ [method_id_var; Lit (n2w selector)];
       final_match <-
         (if has_trailing_zeroes then
            do cds <- emit_op CALLDATASIZE [];
               too_small <- emit_op LT [cds; Lit 4w];
               has_cd <- emit_op ISZERO [too_small];
               emit_op AND [has_cd; is_match]
            od
          else return is_match);
       emit_inst JNZ [final_match; Label match_lbl; Label next_lbl] [];
       new_block match_lbl;
       emit_inst JMP [Label func_lbl] [];
       new_block next_lbl;
       compile_sparse_bucket_search method_id_var rest fallback_lbl
    od
End

(* Pre-allocate bucket labels without creating blocks. *)
Definition alloc_bucket_labels_def:
  alloc_bucket_labels (0:num) = return ([] : string list) ∧
  alloc_bucket_labels n =
    do lbl <- fresh_label "bucket";
       rest <- alloc_bucket_labels (n - 1);
       return (lbl :: rest)
    od
Termination
  WF_REL_TAC `measure I`
End

(* Create bucket blocks at pre-allocated labels. *)
Definition create_bucket_blocks_def:
  create_bucket_blocks method_id_var [] [] fallback_lbl = return () ∧
  create_bucket_blocks method_id_var (lbl::lbls)
      ((_, selectors) :: rest) fallback_lbl =
    do new_block lbl;
       compile_sparse_bucket_search method_id_var selectors fallback_lbl;
       create_bucket_blocks method_id_var lbls rest fallback_lbl
    od ∧
  create_bucket_blocks _ _ _ _ = return ()
End

(* Group selectors into buckets by (selector MOD n_buckets). Pure function. *)
Definition group_into_buckets_def:
  group_into_buckets [] _ = ([] : (num # (num # string # bool) list) list) ∧
  group_into_buckets ((sel, lbl, has_tz) :: rest) n_buckets =
    let bucket_id = sel MOD n_buckets in
    let rest_buckets = group_into_buckets rest n_buckets in
    let updated = MAP (λ(bid, items).
      if bid = bucket_id then (bid, items ++ [(sel, lbl, has_tz)])
      else (bid, items)) rest_buckets in
    if EXISTS (λ(bid, _). bid = bucket_id) rest_buckets then updated
    else (bucket_id, [(sel, lbl, has_tz)]) :: rest_buckets
End

(* ===== Sparse Jumptable Dispatch ===== *)
Definition compile_selector_dispatch_sparse_def:
  compile_selector_dispatch_sparse selectors bucket_count fallback_lbl =
    do cds <- emit_op CALLDATASIZE [];
       has_sel <- emit_op LT [cds; Lit 4w];
       has_sel2 <- emit_op ISZERO [has_sel];
       dispatch_lbl <- fresh_label "dispatch";
       emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [];
       new_block dispatch_lbl;
       raw <- emit_op CALLDATALOAD [Lit 0w];
       method_id <- emit_op SHR [Lit 224w; raw];
       if bucket_count ≤ 1 then
         do compile_selector_checks method_id
              (MAP (λ(sel,lbl,_). (sel,lbl)) selectors);
            emit_inst JMP [Label fallback_lbl] []
         od
       else
         let buckets = group_into_buckets selectors bucket_count in
         do bucket_lbls <- alloc_bucket_labels (LENGTH buckets);
            bucket_id_to_lbl <- return
              (MAP2 (λ(bid, _) lbl. (bid, lbl)) buckets bucket_lbls);
            full_target_list <- return (GENLIST (λi.
              case ALOOKUP bucket_id_to_lbl i of
                SOME lbl => lbl
              | NONE => fallback_lbl) bucket_count);
            bucket_id <- emit_op Mod [method_id; Lit (n2w bucket_count)];
            sz_bucket_header <- return (2:num);
            hdr_offset <- emit_op MUL [bucket_id;
                                       Lit (n2w sz_bucket_header)];
            base_addr <- emit_op OFFSET [Lit 0w; Label "BUCKET_HEADERS"];
            hdr_loc <- emit_op ADD [base_addr; hdr_offset];
            emit_void CODECOPY [Lit 30w; hdr_loc;
                                Lit (n2w sz_bucket_header)];
            jumpdest <- emit_op MLOAD [Lit 0w];
            emit_inst DJMP
              (jumpdest :: MAP (λl. Label l) full_target_list) [];
            (* Data section: BUCKET_HEADERS with 2-byte label refs *)
            emit_data_section "BUCKET_HEADERS";
            FOLDL (λm lbl. do m; emit_data_item (DataLabel lbl) od)
                  (return ()) full_target_list;
            create_bucket_blocks method_id bucket_lbls
              buckets fallback_lbl
         od
    od
End

(* Emit data sections for dense dispatch from precomputed bucket info.
   entry_info: method_id -> (label, min_calldatasize, is_nonpayable). *)
Definition emit_dense_data_sections_def:
  emit_dense_data_sections ([] : dense_bucket list) _ _ = return () ∧
  emit_dense_data_sections (db :: rest) fn_metadata_bytes entry_info =
    let sorted_mids = method_ids_image_order db.db_method_ids db.db_magic in
    do (* Emit per-bucket data section *)
       emit_data_section ("bucket_" ++ toString db.db_id);
       FOLDL (λm mid.
         do m;
            let (lbl, min_cds, is_np) = entry_info mid in
            let metadata_val = min_cds + (if is_np then 1 else 0) in
            let b0 = (mid DIV (2 ** 24)) MOD 256 in
            let b1 = (mid DIV (2 ** 16)) MOD 256 in
            let b2 = (mid DIV (2 ** 8)) MOD 256 in
            let b3 = mid MOD 256 in
            do emit_data_item (DataBytes [n2w b0; n2w b1; n2w b2; n2w b3]);
               emit_data_item (DataLabel lbl);
               emit_data_item (DataBytes (GENLIST (λi.
                 n2w ((metadata_val DIV
                       (2 ** ((fn_metadata_bytes - 1 - i) * 8))) MOD 256))
                 fn_metadata_bytes))
            od
         od)
         (return ()) sorted_mids;
       emit_dense_data_sections rest fn_metadata_bytes entry_info
    od
End

(* ===== Dense Jumptable Dispatch ===== *)
Definition compile_selector_dispatch_dense_def:
  compile_selector_dispatch_dense selectors bucket_count
                                  fn_metadata_bytes
                                  dense_buckets
                                  (entry_info : num -> string # num # bool)
                                  entry_point_labels fallback_lbl =
    let sz_bucket_header = 5 in
    let bits_magic = 24 in
    let func_info_size = 4 + 2 + fn_metadata_bytes in
    let fn_metadata_mask = n2w (2 ** (fn_metadata_bytes * 8) - 1) : bytes32 in
    let calldatasize_mask = n2w (2 ** (fn_metadata_bytes * 8) - 2) : bytes32 in
    let label_bits_offset = fn_metadata_bytes * 8 in
    let method_id_bits_offset = (fn_metadata_bytes + 2) * 8 in
    do cds <- emit_op CALLDATASIZE [];
       has_sel <- emit_op LT [cds; Lit 4w];
       has_sel2 <- emit_op ISZERO [has_sel];
       dispatch_lbl <- fresh_label "dispatch";
       emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [];
       new_block dispatch_lbl;
       raw <- emit_op CALLDATALOAD [Lit 0w];
       method_id <- emit_op SHR [Lit 224w; raw];
       (* Step 1: bucket_id = method_id % n_buckets *)
       bucket_id <- emit_op Mod [method_id; Lit (n2w bucket_count)];
       (* Step 2: load 5-byte bucket header via CODECOPY *)
       hdr_offset <- emit_op MUL [bucket_id; Lit (n2w sz_bucket_header)];
       base_addr <- emit_op OFFSET [Lit 0w; Label "BUCKET_HEADERS"];
       hdr_loc <- emit_op ADD [base_addr; hdr_offset];
       emit_void CODECOPY [Lit 27w; hdr_loc; Lit (n2w sz_bucket_header)];
       hdr_info <- emit_op MLOAD [Lit 0w];
       (* Extract header fields *)
       shifted_for_loc <- emit_op SHR [Lit 8w; hdr_info];
       bucket_location <- emit_op AND [Lit 0xFFFFw; shifted_for_loc];
       bucket_magic <- emit_op SHR [Lit 24w; hdr_info];
       bucket_size <- emit_op AND [Lit 0xFFw; hdr_info];
       (* Step 3: func_id = ((method_id * magic) >> BITS_MAGIC) % size *)
       magic_product <- emit_op MUL [bucket_magic; method_id];
       shifted_mp <- emit_op SHR [Lit (n2w bits_magic); magic_product];
       func_id <- emit_op Mod [shifted_mp; bucket_size];
       (* Step 4: load function info via CODECOPY *)
       fi_offset <- emit_op MUL [func_id; Lit (n2w func_info_size)];
       fi_location <- emit_op ADD [bucket_location; fi_offset];
       emit_void CODECOPY [Lit (n2w (32 - func_info_size));
                           fi_location; Lit (n2w func_info_size)];
       func_info <- emit_op MLOAD [Lit 0w];
       (* Step 5: extract and verify fields *)
       is_nonpayable <- emit_op AND [Lit 1w; func_info];
       expected_calldatasize <- emit_op AND [Lit calldatasize_mask; func_info];
       shifted_for_lbl <- emit_op SHR [Lit (n2w label_bits_offset); func_info];
       function_label <- emit_op AND [Lit 0xFFFFw; shifted_for_lbl];
       function_method_id <- emit_op SHR
         [Lit (n2w method_id_bits_offset); func_info];
       (* Verify method_id and calldatasize *)
       cd_enough <- emit_op CALLDATASIZE [];
       cds_valid <- emit_op GT [cd_enough; Lit 3w];
       mid_correct <- emit_op EQ [function_method_id; method_id];
       should_continue <- emit_op AND [cds_valid; mid_correct];
       should_fallback <- emit_op ISZERO [should_continue];
       check_lbl <- fresh_label "check_passed";
       emit_inst JNZ [should_fallback; Label fallback_lbl;
                       Label check_lbl] [];
       new_block check_lbl;
       (* Assert entry conditions *)
       callvalue_op <- emit_op CALLVALUE [];
       bad_callvalue <- emit_op MUL [is_nonpayable; callvalue_op];
       bad_cds <- emit_op LT [cd_enough; expected_calldatasize];
       failed <- emit_op OR [bad_callvalue; bad_cds];
       ok <- emit_op ISZERO [failed];
       emit_void ASSERT [ok];
       (* Step 6: DJMP to function label *)
       emit_inst DJMP (function_label :: MAP (λl. Label l) entry_point_labels)
                 [];
       (* Step 7: Emit data sections *)
       let sorted_buckets = QSORT (λb1 b2. b1.db_id ≤ b2.db_id)
                                   dense_buckets in
       do emit_data_section "BUCKET_HEADERS";
          FOLDL (λm db.
            do m;
               let magic_hi = (db.db_magic DIV 256) MOD 256 in
               let magic_lo = db.db_magic MOD 256 in
               do emit_data_item (DataBytes [n2w magic_hi; n2w magic_lo]);
                  emit_data_item (DataLabel ("bucket_" ++ toString db.db_id));
                  emit_data_item (DataBytes [n2w (LENGTH db.db_method_ids)])
               od
            od)
            (return ()) sorted_buckets;
          emit_dense_data_sections sorted_buckets fn_metadata_bytes entry_info
       od
    od
End

(* ===== Argument Decoding (unified) ===== *)
Definition compile_decode_args_def:
  compile_decode_args cenv [] _ _ _ _ = return () ∧
  compile_decode_args cenv ((name, is_prim, is_dynamic, abi_size, dec_info)::rest)
                      offset load_opc hi_op base_adj =
    if is_prim then
      let clamp_info = (case dec_info of DecPrimWord c => c | _ => NoClamp) in
      do val_op <- emit_op load_opc [Lit (n2w offset)];
         compile_abi_clamp_basetype val_op clamp_info;
         (case FLOOKUP cenv.ce_vars name of
            SOME (MemLoc mem_offset _) =>
              emit_void MSTORE [Lit (n2w mem_offset); val_op]
          | _ => return ());
         compile_decode_args cenv rest (offset + abi_size) load_opc hi_op base_adj
      od
    else if is_dynamic then
      (case FLOOKUP cenv.ce_vars name of
         SOME (MemLoc mem_offset _) =>
           let dst = Lit (n2w mem_offset) in
           do offset_val <- emit_op load_opc [Lit (n2w offset)];
              actual_src <- emit_op ADD [Lit (n2w base_adj); offset_val];
              compile_abi_decode_to_buf dst actual_src
                load_opc hi_op dec_info;
              compile_decode_args cenv rest (offset + abi_size)
                load_opc hi_op base_adj
           od
       | _ => compile_decode_args cenv rest (offset + abi_size)
                load_opc hi_op base_adj)
    else
      (case FLOOKUP cenv.ce_vars name of
         SOME (MemLoc mem_offset _) =>
           let src = Lit (n2w (base_adj + offset)) in
           let dst = Lit (n2w mem_offset) in
           do compile_abi_decode_to_buf dst src load_opc hi_op dec_info;
              compile_decode_args cenv rest (offset + abi_size)
                load_opc hi_op base_adj
           od
       | _ => compile_decode_args cenv rest (offset + abi_size)
                load_opc hi_op base_adj)
End

(* ===== Internal Function ===== *)
(* Emit PARAMs in declaration order, interleaving stack and memory params.
   Returns (updated_cenv, next_param_idx). *)
Definition compile_internal_params_def:
  compile_internal_params cenv [] (idx:num) = return (cenv, idx) ∧
  compile_internal_params cenv ((name, is_stack)::rest) idx =
    do param_op <- emit_op PARAM [Lit (n2w idx)];
       if is_stack then
         do (case FLOOKUP cenv.ce_vars name of
               SOME (MemLoc offset _) =>
                 emit_void MSTORE [Lit (n2w offset); param_op]
             | _ => return ());
            compile_internal_params cenv rest (idx + 1)
         od
       else
         let mem_size = (case FLOOKUP cenv.ce_vars name of
                           SOME (MemLoc _ sz) => sz | _ => 0) in
         let cenv' = cenv with ce_vars updated_by
                       (λm. m |+ (name, PtrVar param_op mem_size)) in
         compile_internal_params cenv' rest (idx + 1)
    od
End

(* Internal entry parameters must be declared as one contiguous prefix.  Keep
   declaration separate from environment/materialization effects so callers can
   append the return-PC declaration before emitting any stores. *)
Definition compile_internal_param_decls_def:
  compile_internal_param_decls [] (idx:num) = return ([], idx) /\
  compile_internal_param_decls ((name, is_stack)::rest) idx =
    do param_op <- emit_op PARAM [Lit (n2w idx)];
       rest_result <- compile_internal_param_decls rest (idx + 1);
       return ((name, is_stack, param_op) :: FST rest_result,
               SND rest_result)
    od
End

Definition materialize_internal_params_def:
  materialize_internal_params cenv [] = return cenv /\
  materialize_internal_params cenv ((name, is_stack, param_op)::rest) =
    if is_stack then
      do (case FLOOKUP cenv.ce_vars name of
            SOME (MemLoc offset _) =>
              emit_void MSTORE [Lit (n2w offset); param_op]
          | _ => return ());
         materialize_internal_params cenv rest
      od
    else
      let mem_size = (case FLOOKUP cenv.ce_vars name of
                        SOME (MemLoc _ sz) => sz | _ => 0) in
      let cenv' = cenv with ce_vars updated_by
                    (\m. m |+ (name, PtrVar param_op mem_size)) in
      materialize_internal_params cenv' rest
End

(* ===== Constructor ===== *)
Definition compile_constructor_epilogue_def:
  compile_constructor_epilogue runtime_size immutables_len immutables_buf =
    let rt_size_op = (Lit (n2w runtime_size) : operand) in
    let total_size = runtime_size + immutables_len in
    if immutables_len > 0 then
      do deploy_buf <- emit_op ALLOCA [Lit (n2w total_size)];
         imm_dst <- emit_op ADD [deploy_buf; rt_size_op];
         emit_void MCOPY [imm_dst; immutables_buf;
                          Lit (n2w immutables_len)];
         rt_begin <- emit_op OFFSET [Lit 0w; Label "runtime_begin"];
         emit_void CODECOPY [deploy_buf; rt_begin; rt_size_op];
         emit_inst RETURN [deploy_buf; Lit (n2w total_size)] []
      od
    else
      do buf_alloc <- compile_alloc_buffer runtime_size;
         buf <- return buf_alloc.buf_operand;
         rt_begin <- emit_op OFFSET [Lit 0w; Label "runtime_begin"];
         emit_void CODECOPY [buf; rt_begin; Lit (n2w runtime_size)];
         emit_inst RETURN [buf; Lit (n2w runtime_size)] []
      od
End

(* ===== Simple Deploy (no constructor) ===== *)
Definition compile_simple_deploy_def:
  compile_simple_deploy runtime_size immutables_len =
    let total_size = runtime_size + immutables_len in
    do buf_alloc <- compile_alloc_buffer total_size;
       buf <- return buf_alloc.buf_operand;
       rt_begin <- emit_op OFFSET [Lit 0w; Label "runtime_begin"];
       emit_void CODECOPY [buf; rt_begin; Lit (n2w total_size)];
       emit_inst RETURN [buf; Lit (n2w total_size)] []
    od
End

(* ===== Kwargs Handling ===== *)

(* Create alloca for each kwarg, shared between entry points. *)
Definition compile_create_kwarg_allocas_def:
  compile_create_kwarg_allocas [] = return [] ∧
  compile_create_kwarg_allocas ((name, mem_size)::rest) =
    do ptr_op_alloc <- compile_alloc_buffer mem_size;
       ptr_op <- return ptr_op_alloc.buf_operand;
       rest_vars <- compile_create_kwarg_allocas rest;
       return ((name, ptr_op) :: rest_vars)
    od
End

(* Init kwargs: from calldata or from default expression. *)
Definition compile_init_kwargs_def:
  compile_init_kwargs cenv [] _ _ _ = return () ∧
  compile_init_kwargs cenv ((name, alloca_ptr, kwarg_type, default_e)::rest)
                      calldata_offset kwargs_from_calldata hi_op =
    if kwargs_from_calldata > 0 then
      let is_prim = is_word_type kwarg_type in
      if is_prim then
        let dec_info = type_to_abi_dec_info cenv.ce_struct_fields cenv kwarg_type in
        let clamp_info = (case dec_info of DecPrimWord c => c | _ => NoClamp) in
        do val_op <- emit_op CALLDATALOAD [Lit (n2w calldata_offset)];
           compile_abi_clamp_basetype val_op clamp_info;
           emit_void MSTORE [alloca_ptr; val_op];
           compile_init_kwargs cenv rest (calldata_offset + 32)
                               (kwargs_from_calldata - 1) hi_op
        od
      else if is_abi_dynamic cenv.ce_struct_fields kwarg_type then
        let dec_info = type_to_abi_dec_info cenv.ce_struct_fields cenv kwarg_type in
        let abi_sz = abi_embedded_static_size cenv.ce_struct_fields kwarg_type in
        do offset_val <- emit_op CALLDATALOAD [Lit (n2w calldata_offset)];
           actual_src <- emit_op ADD [Lit 4w; offset_val];
           compile_abi_decode_to_buf alloca_ptr actual_src
             CALLDATALOAD hi_op dec_info;
           compile_init_kwargs cenv rest (calldata_offset + abi_sz)
                               (kwargs_from_calldata - 1) hi_op
        od
      else
        let dec_info = type_to_abi_dec_info cenv.ce_struct_fields cenv kwarg_type in
        let src = Lit (n2w (4 + calldata_offset)) in
        let abi_sz = abi_embedded_static_size cenv.ce_struct_fields kwarg_type in
        do compile_abi_decode_to_buf alloca_ptr src
             CALLDATALOAD hi_op dec_info;
           compile_init_kwargs cenv rest (calldata_offset + abi_sz)
                               (kwargs_from_calldata - 1) hi_op
        od
    else
      do default_val <- lower_value compile_expr cenv kwarg_type default_e;
         (if is_word_type kwarg_type then
            emit_void MSTORE [alloca_ptr; default_val]
          else if is_bytestring_type kwarg_type then
            compile_store_bytestring default_val alloca_ptr
          else
            let mem_size = type_memory_bytes cenv kwarg_type in
            emit_void MCOPY [alloca_ptr; default_val;
                             Lit (n2w mem_size)]);
         compile_init_kwargs cenv rest calldata_offset 0 hi_op
      od
End

(* Generate entry point for kwargs: init kwargs, jump to common body. *)
Definition compile_entry_point_kwargs_def:
  compile_entry_point_kwargs cenv kwarg_vars calldata_offset
                             kwargs_from_calldata common_label =
    do hi_op <- emit_op CALLDATASIZE [];
       compile_init_kwargs cenv kwarg_vars calldata_offset
                            kwargs_from_calldata hi_op;
       emit_inst JMP [Label common_label] []
    od
End

(* Register pre-allocated kwarg allocas as variables. Pure function. *)
Definition compile_register_kwarg_vars_def:
  compile_register_kwarg_vars (cenv : compile_env) [] = cenv ∧
  compile_register_kwarg_vars cenv ((name, alloca_offset, mem_size)::rest) =
    compile_register_kwarg_vars
      (cenv with ce_vars := cenv.ce_vars |+ (name, MemLoc alloca_offset mem_size)) rest
End

(* ===== Calldata / Data-Section Arg Wrappers ===== *)

Definition compile_register_positional_args_def:
  compile_register_positional_args cenv args calldata_offset =
    do hi_op <- emit_op CALLDATASIZE [];
       compile_decode_args cenv args calldata_offset CALLDATALOAD hi_op 4
    od
End

Definition compile_register_constructor_args_def:
  compile_register_constructor_args cenv args data_offset data_size =
    compile_decode_args cenv args data_offset DLOAD (Lit (n2w data_size)) 0
End

(* ===== Guarded Body ===== *)
Definition compile_guarded_body_def:
  compile_guarded_body cenv is_nonreentrant nkey use_transient
                       is_view body ret_type =
    do (if is_nonreentrant then
          compile_nonreentrant_lock nkey use_transient is_view
        else return ());
       compile_stmts cenv NoLoop
         (case ret_type of SOME t => t | NONE => BaseT BoolT) body;
       cs <- comp_get;
       if block_is_terminated cs then return ()
       else
         do (if is_nonreentrant then
               compile_nonreentrant_unlock nkey use_transient is_view
             else return ());
            (case ret_type of
               SOME _ => emit_inst INVALID [] []
             | NONE => emit_inst STOP [] [])
         od
    od
End

(* ===== External Function Body ===== *)
Definition compile_external_function_body_def:
  compile_external_function_body cenv positional_args
                                 is_nonreentrant nkey use_transient
                                 is_view body ret_type =
    do compile_register_positional_args cenv positional_args 4;
       compile_guarded_body cenv is_nonreentrant nkey use_transient
                            is_view body ret_type
    od
End

(* ===== Fallback Function Body ===== *)
Definition compile_fallback_body_def:
  compile_fallback_body cenv is_payable is_nonreentrant nkey use_transient
                        is_view body ret_type =
    do (if ¬is_payable then
          do cv <- emit_op CALLVALUE [];
             no_value <- emit_op ISZERO [cv];
             emit_void ASSERT [no_value]
          od
        else return ());
       compile_guarded_body cenv is_nonreentrant nkey use_transient
                            is_view body ret_type
    od
End

(* ===== Internal Function Generation ===== *)
Definition compile_internal_function_def:
  compile_internal_function cenv params
                                 has_return_buf is_nonreentrant
                                 nkey use_transient is_view
                                 is_ctor_context immutables_len
                                 body ret_type =
    do (* Declare the complete physical entry prefix before any materialization. *)
       return_buf_var <-
         (if has_return_buf then
            do param_op <- emit_op PARAM [Lit 0w];
               return (SOME param_op)
            od
          else return NONE);
       param_idx_start <- return (if has_return_buf then 1 else 0);
       params_result <- compile_internal_param_decls params param_idx_start;
       captured_params <- return (FST params_result);
       next_idx <- return (SND params_result);
       return_pc <- emit_op PARAM [Lit (n2w next_idx)];
       (* Reserve immutables only after the canonical parameter prefix. *)
       forced_alloc_id <-
         (if is_ctor_context ∧ immutables_len > 0 then
            let touch_offset = if immutables_len > 32 then immutables_len - 32
                               else 0 in
            do alloc_result <- compile_alloc_buffer_with_id immutables_len;
               emit_op MLOAD [Lit (n2w touch_offset)];
               return (SOME (FST alloc_result))
            od
          else return NONE);
       (case return_buf_var of
          SOME param_op =>
            (case FLOOKUP cenv.ce_vars "__return_buf__" of
               SOME (MemLoc rbuf_off _) =>
                 emit_void MSTORE [Lit (n2w rbuf_off); param_op]
             | _ => return ())
        | NONE => return ());
       cenv2 <- materialize_internal_params cenv captured_params;
       (case FLOOKUP cenv2.ce_vars "__return_pc__" of
          SOME (MemLoc rpc_off _) =>
            emit_void MSTORE [Lit (n2w rpc_off); return_pc]
        | _ => return ());
       (* Nonreentrant lock *)
       (if is_nonreentrant then
          compile_nonreentrant_lock nkey use_transient is_view
        else return ());
       (* Compile body *)
       compile_stmts cenv2 NoLoop
         (case ret_type of SOME t => t | NONE => BaseT BoolT) body;
       cs <- comp_get;
       (if block_is_terminated cs then return ()
        else
          do (if is_nonreentrant then
                compile_nonreentrant_unlock nkey use_transient is_view
              else return ());
             (case ret_type of
                NONE => emit_inst RET [return_pc] []
              | SOME _ => emit_inst INVALID [] [])
          od);
       return forced_alloc_id
    od
End

(* ===== Entry Checks ===== *)
Definition compile_entry_checks_def:
  compile_entry_checks min_calldata_size is_payable =
    do (if ¬is_payable then
          do cv <- emit_op CALLVALUE [];
             no_value <- emit_op ISZERO [cv];
             emit_void ASSERT [no_value]
          od
        else return ());
       if min_calldata_size > 4 then
         do cds <- emit_op CALLDATASIZE [];
            enough <- emit_op LT [cds; Lit (n2w min_calldata_size)];
            ok <- emit_op ISZERO [enough];
            emit_void ASSERT [ok]
         od
       else return ()
    od
End

(* ===== Generate External Function Bodies ===== *)
Definition compile_external_fn_bodies_def:
  compile_external_fn_bodies [] = return () ∧
  compile_external_fn_bodies ((entry_lbl, cenv, pos_args, min_cds,
                               is_payable, is_nr, nkey, use_trans,
                               is_view, body, ret_type) :: rest) =
    do new_block entry_lbl;
       compile_entry_checks min_cds is_payable;
       compile_external_function_body cenv pos_args
         is_nr nkey use_trans is_view body ret_type;
       compile_external_fn_bodies rest
    od
End

(* ===== Generate Internal Function Bodies ===== *)
Definition compile_internal_fn_bodies_def:
  compile_internal_fn_bodies [] = return ([] : (string # num # num) list) ∧
  compile_internal_fn_bodies ((fn_lbl, cenv, params, has_ret_buf,
                               is_nr, nkey, use_trans, is_view,
                               is_ctor, imm_len,
                               body, ret_type) :: rest) =
    do new_block fn_lbl;
       forced_id <- compile_internal_function cenv params has_ret_buf
         is_nr nkey use_trans is_view
         is_ctor imm_len body ret_type;
       rest_forced <- compile_internal_fn_bodies rest;
       return
         (case forced_id of
            NONE => rest_forced
          | SOME id =>
              (fn_lbl, id,
               (if has_ret_buf then 1 else 0) + LENGTH params + 1) ::
              rest_forced)
    od
End

(* ===== Generate Runtime ===== *)
Definition compile_generate_runtime_def:
  compile_generate_runtime selectors external_fns internal_fns
                           (fallback_fn : (compile_env # bool # bool # num #
                                           bool # bool # stmt list #
                                           type option) option)
                           dispatch_strategy
                           bucket_count fn_metadata_bytes
                           dense_buckets
                           (entry_info : num -> string # num # bool) =
    let linear_sels = MAP (λ(sel,lbl,_). (sel,lbl)) selectors in
    do fallback_lbl <- fresh_label "fallback";
       (* Selector dispatch *)
       (case dispatch_strategy of
          Sparse =>
            compile_selector_dispatch_sparse selectors
              bucket_count fallback_lbl
        | Dense =>
            let entry_lbls = MAP (λ(_,lbl,_). lbl) selectors in
            compile_selector_dispatch_dense selectors
              bucket_count fn_metadata_bytes
              dense_buckets entry_info entry_lbls fallback_lbl
        | Linear =>
            compile_selector_dispatch_linear linear_sels fallback_lbl);
       (* Generate external function bodies *)
       compile_external_fn_bodies external_fns;
       (* Fallback block *)
       new_block fallback_lbl;
       (case fallback_fn of
          NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
        | SOME (fb_cenv, fb_payable, fb_nonreentrant, fb_nkey,
                fb_transient, fb_view, fb_body, fb_ret_type) =>
            compile_fallback_body fb_cenv fb_payable fb_nonreentrant fb_nkey
                                  fb_transient fb_view fb_body fb_ret_type);
       (* Runtime internal functions have no static immutable reservation. *)
       _ <- compile_internal_fn_bodies internal_fns;
       return ()
    od
End

(* ===== Generate Deploy ===== *)
Definition compile_generate_deploy_def:
  compile_generate_deploy has_constructor runtime_size immutables_len
                           constructor_args data_size
                           ctor_internal_fns
                           cenv body is_payable is_nonreentrant
                           nkey use_transient =
    if has_constructor then
      do (* Payable check *)
         (if ¬is_payable then
            do cv <- emit_op CALLVALUE [];
               no_val <- emit_op ISZERO [cv];
               emit_void ASSERT [no_val]
            od
          else return ());
         (* Reserve immutables region at position 0 and capture its owning
            entry block plus instruction ID for checked packaging. *)
         entry_cs <- comp_get;
         imm_result <-
           (if immutables_len > 0 then
              let touch_offset = if immutables_len > 32
                                 then immutables_len - 32
                                 else 0 in
              do alloc_result <- compile_alloc_buffer_with_id immutables_len;
                 imm_op <- return (SND alloc_result).buf_operand;
                 emit_op MLOAD [Lit (n2w touch_offset)];
                 return (imm_op,
                         [(entry_cs.cs_current_bb, FST alloc_result, 0)])
              od
            else return (Lit 0w, []));
         imm_alloca <- return (FST imm_result);
         entry_forced <- return (SND imm_result);
         (* Register constructor args from DATA section *)
         compile_register_constructor_args cenv constructor_args 0 data_size;
         (* Nonreentrant lock *)
         (if is_nonreentrant then
            compile_nonreentrant_lock nkey use_transient F
          else return ());
         (* Constructor body *)
         compile_stmts cenv NoLoop (BaseT BoolT) body;
         cs <- comp_get;
         (if block_is_terminated cs then return ()
          else
            do (if is_nonreentrant then
                  compile_nonreentrant_unlock nkey use_transient F
                else return ());
               compile_constructor_epilogue runtime_size immutables_len
                 imm_alloca
            od);
         (* Internal functions: generated regardless of constructor termination *)
         internal_forced <- compile_internal_fn_bodies ctor_internal_fns;
         return (entry_forced ++ internal_forced)
      od
    else
      do compile_simple_deploy runtime_size immutables_len;
         return ([] : (string # num # num) list)
      od
End

(* ===== Common Function Body ===== *)
Definition compile_common_function_body_def:
  compile_common_function_body cenv positional_args kwarg_vars
                                is_nonreentrant nkey use_transient
                                is_view body ret_type =
    let cenv1 = compile_register_kwarg_vars cenv kwarg_vars in
    do compile_register_positional_args cenv positional_args 4;
       compile_guarded_body cenv1 is_nonreentrant nkey use_transient
                            is_view body ret_type
    od
End

(* Each entry point: checks + kwarg init + JMP to common body. *)
Definition compile_external_entry_points_def:
  compile_external_entry_points [] _ _ _ _ = return () ∧
  compile_external_entry_points
    ((sel, fn_label, min_cds, is_payable, kwargs_from_calldata)::rest)
    cenv kwarg_vars calldata_offset common_label =
    do new_block fn_label;
       compile_entry_checks min_cds is_payable;
       hi_op <- emit_op CALLDATASIZE [];
       compile_init_kwargs cenv kwarg_vars calldata_offset
                            kwargs_from_calldata hi_op;
       emit_inst JMP [Label common_label] [];
       compile_external_entry_points rest cenv kwarg_vars calldata_offset
                                      common_label
    od
End
