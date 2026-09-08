(* Structural properties of checked FMP lowering. *)

Theory fmpLowerProps
Ancestors
  fmpLowerDefs fmpAnalysisProps fmpWfProps

Theorem fmp_lower_inst_no_raw:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  Cases_on `inst.inst_opcode` >>
  gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def,
      venomInstTheory.mk_inst_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_lower_insts_no_raw:
  fmp_lower_insts infos ctx runner s insts = SOME (out,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`s`] >> Induct_on `insts`
  >- simp[fmp_lower_insts_def]
  >> simp[fmp_lower_insts_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[listTheory.EVERY_APPEND] >>
  metis_tac[fmp_lower_inst_no_raw]
QED

Theorem fmp_emit_restores_no_raw:
  fmp_emit_restores runner s bases = (out,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def]
  >> simp[fmp_emit_restores_def, AllCaseEqs(),
          venomInstTheory.mk_inst_def,
          venomInstTheory.is_raw_fmp_opcode_def] >>
  rpt strip_tac >>
  gvs[venomInstTheory.is_raw_fmp_opcode_def] >>
  metis_tac[]
QED

Theorem fmp_lower_blocks_no_raw:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) out
Proof
  map_every qid_spec_tac [`s'`,`leftover`,`out`,`restores`,`s`] >>
  Induct_on `bbs`
  >- simp[fmp_lower_blocks_def]
  >> rpt gen_tac >>
  Cases_on `fmp_select_point_restores
    (h.bb_label,LENGTH h.bb_instructions) restores` >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[listTheory.EVERY_APPEND] >>
  metis_tac[fmp_lower_insts_no_raw, fmp_emit_restores_no_raw]
QED

Theorem fmp_install_root_no_raw:
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) blocks /\
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST root) /\
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST retpc) /\
  fmp_install_root ctx fn (FmpRootLayout n root retpc s) blocks =
    SOME (out,s') ==>
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) out
Proof
  Cases_on `blocks` >>
  simp[fmp_install_root_def, listTheory.EVERY_APPEND] >>
  rpt strip_tac >>
  gvs[listTheory.EVERY_APPEND] >>
  Cases_on `fn_is_context_entry ctx fn` >>
  simp[listTheory.EVERY_APPEND] >>
  metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
QED

Theorem fmp_seal_signature:
  (fmp_seal ctx fn info blocks).fn_fmp_signature =
    SOME <| fms_has_fmp_param := (info.fi_needs_fmp /\
                                   ~fn_is_context_entry ctx fn);
            fms_publishes := info.fi_publishes_fmp |>
Proof
  simp[fmp_seal_def]
QED

Theorem fmp_seal_preserves_nonfmp_metadata:
  fn_identity_metadata_eq (fmp_seal ctx fn info blocks) fn /\
  fn_static_input_eq (fmp_seal ctx fn info blocks) fn /\
  fn_static_layout_eq (fmp_seal ctx fn info blocks) fn
Proof
  simp[fmp_seal_def,
       venomInstTheory.fn_identity_metadata_eq_def,
       venomInstTheory.fn_static_input_eq_def,
       venomInstTheory.fn_static_layout_eq_def]
QED


Theorem fmp_lower_function_preserves_nonfmp_metadata:
  fmp_lower_function ctx supply fn = SOME (fn',supply') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  strip_tac >>
  gvs[fmp_checked_seal_def, fmp_seal_def,
      fmp_seal_preserves_nonfmp_metadata,
      venomInstTheory.fn_identity_metadata_eq_def,
      venomInstTheory.fn_static_input_eq_def,
      venomInstTheory.fn_static_layout_eq_def]
QED

Theorem fmp_lower_function_seals_signature_exact:
  analyze_fmp_context ctx = SOME infos /\
  fmp_lower_input infos ctx fn /\
  FLOOKUP infos fn.fn_name = SOME info /\
  fn.fn_fmp_signature = NONE /\
  fmp_lower_function ctx supply fn = SOME (fn',supply') ==>
  fn'.fn_fmp_signature =
    SOME <| fms_has_fmp_param := (info.fi_needs_fmp /\
                                   ~fn_is_context_entry ctx fn);
            fms_publishes := info.fi_publishes_fmp |>
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[fmp_checked_seal_def, fmp_seal_def, fmp_seal_signature]
QED

Theorem fmp_lower_function_seals_signature:
  analyze_fmp_context ctx = SOME infos /\
  fmp_lower_input infos ctx fn /\
  fn.fn_fmp_signature = NONE /\
  fmp_lower_function ctx supply fn = SOME (fn',supply') ==>
  ?sig. fn'.fn_fmp_signature = SOME sig
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[fmp_checked_seal_def, fmp_seal_def, fmp_seal_signature]
QED

Theorem fmp_lookup_function_self:
  ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\ MEM fn fns ==>
  lookup_function fn.fn_name fns = SOME fn
Proof
  Induct_on `fns`
  >- simp[venomInstTheory.lookup_function_def]
  >> rpt gen_tac
  >> simp[venomInstTheory.lookup_function_def, listTheory.FIND_thm]
  >> rpt strip_tac
  >> gvs[]
  >> `h.fn_name <> fn.fn_name` by
       metis_tac[listTheory.MEM_MAP]
  >> gvs[venomInstTheory.lookup_function_def]
QED

Theorem fmp_lower_function_idempotent:
  analyze_fmp_context ctx = SOME infos /\
  MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = SOME sig /\
  fmp_signature_matches_fn ctx fn /\
  no_raw_fmp_ops fn ==>
  fmp_lower_function ctx supply fn = SOME (fn,supply)
Proof
  rpt strip_tac >>
  `fmp_info_valid ctx infos` by
    metis_tac[analyze_fmp_context_valid] >>
  `lookup_function fn.fn_name ctx.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[fmpAnalysisDefsTheory.fmp_info_valid_def,
         venomWfTheory.ctx_distinct_fn_names_def,
         venomInstTheory.ctx_fn_names_def]) >>
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def]
QED

Theorem fmp_scan_insts_no_bits_no_raw:
  fmp_scan_insts insts = info /\
  ~info.fi_needs_fmp /\ ~info.fi_publishes_fmp ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) insts
Proof
  map_every qid_spec_tac [`info`] >> Induct_on `insts` >>
  simp[fmpAnalysisDefsTheory.fmp_scan_insts_def,
       fmpAnalysisDefsTheory.fmp_info_bottom_def,
       fmpAnalysisDefsTheory.fmp_info_join_def,
       fmpAnalysisDefsTheory.fmp_opcode_needs_fmp_def,
       fmpAnalysisDefsTheory.fmp_opcode_publishes_fmp_def,
       venomInstTheory.is_raw_fmp_opcode_def] >>
  rpt strip_tac >> Cases_on `h.inst_opcode` >>
  gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_direct_info_no_bits_no_raw:
  ~(fmp_direct_info fn).fi_needs_fmp /\
  ~(fmp_direct_info fn).fi_publishes_fmp ==>
  no_raw_fmp_ops fn
Proof
  simp[fmpAnalysisDefsTheory.fmp_direct_info_def,
       venomInstTheory.no_raw_fmp_ops_def,
       venomInstTheory.fn_insts_def] >> strip_tac >>
  `EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
         (fn_insts_blocks fn.fn_blocks)` by
    (irule fmp_scan_insts_no_bits_no_raw >> simp[]) >>
  gvs[listTheory.EVERY_MEM]
QED

Theorem fmp_fn_insts_blocks_mem:
  MEM inst (fn_insts_blocks blocks) ==>
  ?bb. MEM bb blocks /\ MEM inst bb.bb_instructions
Proof
  Induct_on `blocks` >>
  simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]
QED

Theorem fmp_blocks_every_no_raw:
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) blocks ==>
  no_raw_fmp_ops (fn with fn_blocks := blocks)
Proof
  simp[venomInstTheory.no_raw_fmp_ops_def,
       venomInstTheory.fn_insts_def, listTheory.EVERY_MEM] >>
  metis_tac[fmp_fn_insts_blocks_mem]
QED

Theorem fmp_option_every_no_raw:
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST opt) <=>
  !i. opt = SOME i ==> ~is_raw_fmp_opcode i.inst_opcode
Proof
  Cases_on `opt` >> EVAL_TAC >> simp[]
QED

Theorem split_fmp_entry_from_retpc_opcode:
  split_fmp_entry_from k users insts =
    SOME (FmpEntryLayout users' (SOME retpc) tailinsts) ==>
  retpc.inst_opcode = RETPC_PARAM
Proof
  map_every qid_spec_tac [`tailinsts`,`retpc`,`users'`,`users`,`k`] >>
  Induct_on `insts`
  >- simp[split_fmp_entry_from_def]
  >> simp[split_fmp_entry_from_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED


Theorem split_fmp_entry_retpc_opcode:
  split_fmp_entry fn =
    SOME (FmpEntryLayout users (SOME retpc) tailinsts) ==>
  retpc.inst_opcode = RETPC_PARAM
Proof
  simp[split_fmp_entry_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[split_fmp_entry_from_retpc_opcode]
QED
Theorem split_fmp_entry_retpc_no_raw:
  split_fmp_entry fn = SOME (FmpEntryLayout users retpc tailinsts) ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST retpc)
Proof
  simp[split_fmp_entry_def, AllCaseEqs(), fmp_option_every_no_raw] >>
  rpt strip_tac >>
  metis_tac[split_fmp_entry_from_retpc_opcode,
            venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_make_root_layout_no_raw_insertions:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root retpc s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST root) /\
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST retpc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs(), fmp_option_every_no_raw] >>
  rpt strip_tac >>
  gvs[venomInstTheory.mk_inst_def, set_param_index_def,
      venomInstTheory.is_raw_fmp_opcode_def] >>
  metis_tac[split_fmp_entry_retpc_opcode,
            venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_seal_no_raw:
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) blocks ==>
  no_raw_fmp_ops (fmp_seal ctx fn info blocks)
Proof
  strip_tac >> drule fmp_blocks_every_no_raw >>
  simp[fmp_seal_def]
QED

Theorem fmp_no_need_input_no_raw:
  analyze_fmp_context ctx = SOME infos /\
  fmp_lower_input infos ctx fn /\
  FLOOKUP infos fn.fn_name = SOME info /\
  ~info.fi_needs_fmp /\ ~info.fi_publishes_fmp ==>
  no_raw_fmp_ops fn
Proof
  simp[fmp_lower_input_def] >> rpt strip_tac >>
  `MEM fn ctx.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule_all analyze_fmp_context_unsealed_direct_fields >> strip_tac >>
  irule fmp_direct_info_no_bits_no_raw >> metis_tac[]
QED

Theorem fmp_lower_function_removes_raw_ops:
  analyze_fmp_context ctx = SOME infos /\
  fmp_lower_input infos ctx fn /\
  fmp_lower_function ctx supply fn = SOME (fn',supply') ==>
  no_raw_fmp_ops fn'
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule_all fmp_no_need_input_no_raw >>
      gvs[fmp_checked_seal_def, fmp_seal_def,
          venomInstTheory.no_raw_fmp_ops_def,
          venomInstTheory.fn_insts_def])
  >> Cases_on `root_layout` >> gvs[] >>
  drule fmp_lower_blocks_no_raw >> strip_tac >>
  drule fmp_make_root_layout_no_raw_insertions >> strip_tac >>
  drule_all fmp_install_root_no_raw >> strip_tac >>
  gvs[fmp_checked_seal_def, fmp_seal_def] >>
  irule fmp_blocks_every_no_raw >> simp[]
QED

Theorem fmp_lowered_context_wf_sealed_raw_free:
  fmp_lowered_context_wf ctx /\ MEM fn ctx.ctx_functions ==>
  (?sig. fn.fn_fmp_signature = SOME sig) /\ no_raw_fmp_ops fn
Proof
  strip_tac >>
  drule_all fmp_lowered_context_wf_function >> strip_tac >>
  conj_tac
  >- (Cases_on `fn.fn_fmp_signature` >>
      gvs[fmpWfDefsTheory.fmp_signature_matches_fn_def])
  >> simp[]
QED

Theorem fmp_lowered_context_wf_signature_matches:
  fmp_lowered_context_wf ctx /\ MEM fn ctx.ctx_functions ==>
  fmp_signature_matches_fn ctx fn
Proof
  metis_tac[fmp_lowered_context_wf_function]
QED

Theorem fmp_invalid_seal_rejected:
  analyze_fmp_context ctx = SOME infos /\
  fn.fn_fmp_signature = SOME sig /\
  (~fmp_signature_matches_fn ctx fn \/ ~no_raw_fmp_ops fn) ==>
  fmp_lower_function ctx supply fn = NONE
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def]
QED
val _ = export_theory();
