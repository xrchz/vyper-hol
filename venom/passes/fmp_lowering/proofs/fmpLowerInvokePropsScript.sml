Theory fmpLowerInvokeProps
Ancestors
  fmpLowerDefs
  fmpLowerProps
  fcgBridge

Theorem fmp_lower_insts_invokes:
  fmp_lower_insts infos ctx runner s insts = SOME (out,s') /\
  MEM out_inst out /\
  fmp_inst_invokes target out_inst ==>
  ?inst. MEM inst insts /\ fmp_inst_invokes target inst
Proof
  map_every qid_spec_tac [`s'`,`out`,`s`] >> Induct_on `insts`
  >- simp[fmp_lower_insts_def]
  >> simp[fmp_lower_insts_def, AllCaseEqs()]
  >> rpt strip_tac >> gvs[listTheory.MEM_APPEND]
  >> metis_tac[fmp_lower_inst_invokes]
QED


Theorem fmp_emit_restores_not_invokes:
  fmp_emit_restores runner s bases = (out,s') /\
  MEM out_inst out ==>
  ~fmp_inst_invokes target out_inst
Proof
  map_every qid_spec_tac [`s'`,`out`,`s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def]
  >> simp[fmp_emit_restores_def, fmp_inst_invokes_def,
          venomInstTheory.mk_inst_def, AllCaseEqs()]
  >> rpt strip_tac >> gvs[]
  >> first_x_assum (qspecl_then [`s1`,`tail`,`s'`] mp_tac)
  >> simp[fmp_inst_invokes_def]
QED

Theorem fmp_lower_blocks_invokes:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\
  MEM out_bb out /\
  MEM out_inst out_bb.bb_instructions /\
  fmp_inst_invokes target out_inst ==>
  ?bb inst. MEM bb bbs /\
            MEM inst bb.bb_instructions /\
            fmp_inst_invokes target inst
Proof
  map_every qid_spec_tac [`s'`,`leftover`,`out`,`restores`,`s`] >>
  Induct_on `bbs`
  >- simp[fmp_lower_blocks_def]
  >> rpt gen_tac
  >> Cases_on `fmp_select_point_restores
        (h.bb_label,LENGTH h.bb_instructions) restores`
  >> simp[fmp_lower_blocks_def, AllCaseEqs()]
  >> rpt strip_tac >> gvs[listTheory.MEM_APPEND]
  >> metis_tac[fmp_lower_insts_invokes, fmp_emit_restores_not_invokes]
QED


Theorem fmp_make_root_layout_not_invokes:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root retpc s') ==>
  (!i. root = SOME i ==> !target. ~fmp_inst_invokes target i) /\
  (!i. retpc = SOME i ==> !target. ~fmp_inst_invokes target i)
Proof
  Cases_on `root` >> Cases_on `retpc`
  >> simp[fmp_make_root_layout_def, fmp_inst_invokes_def, AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[venomInstTheory.mk_inst_def, set_param_index_def]
  >> drule fmpLowerPropsTheory.split_fmp_entry_retpc_opcode
  >> simp[]
QED



Theorem option_to_list_eqns[local]:
  OPTION_TO_LIST NONE = [] /\
  !x. OPTION_TO_LIST (SOME x) = [x]
Proof
  EVAL_TAC >> simp[]
QED

Theorem take_insert_drop_invokes:
  MEM out_inst (TAKE n insts ++ inserted ++ DROP m insts) /\
  (!i. MEM i inserted ==> !target. ~fmp_inst_invokes target i) /\
  fmp_inst_invokes target out_inst ==>
  MEM out_inst insts
Proof
  simp[listTheory.MEM_APPEND]
  >> rpt strip_tac >> gvs[]
  >> metis_tac[rich_listTheory.MEM_TAKE, rich_listTheory.MEM_DROP_IMP]
QED
Theorem fmp_install_root_invokes:
  (!i. root = SOME i ==> !target. ~fmp_inst_invokes target i) /\
  (!i. retpc = SOME i ==> !target. ~fmp_inst_invokes target i) /\
  fmp_install_root ctx fn (FmpRootLayout n root retpc s) blocks =
    SOME (out,s') /\
  MEM out_bb out /\
  MEM out_inst out_bb.bb_instructions /\
  fmp_inst_invokes target out_inst ==>
  ?bb inst. MEM bb blocks /\
            MEM inst bb.bb_instructions /\
            fmp_inst_invokes target inst
Proof
  Cases_on `blocks` >> gvs[fmp_install_root_def]
  >> Cases_on `root` >> Cases_on `retpc`
  >> Cases_on `fn_is_context_entry ctx fn`
  >> simp[fmp_install_root_def]
  >> rpt strip_tac >> gvs[option_to_list_eqns, listTheory.MEM_APPEND]
  >> TRY (`MEM out_inst h.bb_instructions` by
            metis_tac[rich_listTheory.MEM_TAKE,
                      rich_listTheory.MEM_DROP_IMP] >>
          qexistsl [`h`,`out_inst`] >> simp[] >> NO_TAC)
  >> TRY (qexistsl [`out_bb`,`out_inst`] >> simp[] >> NO_TAC)
  >> metis_tac[]
QED


Theorem fmp_fn_insts_blocks_intro:
  MEM bb blocks /\ MEM inst bb.bb_instructions ==>
  MEM inst (fn_insts_blocks blocks)
Proof
  Induct_on `blocks`
  >> simp[venomInstTheory.fn_insts_blocks_def]
  >> metis_tac[]
QED

Theorem fmp_lower_function_invokes:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  MEM out_inst (fn_insts fn') /\
  fmp_inst_invokes target out_inst ==>
  ?inst. MEM inst (fn_insts fn) /\
         fmp_inst_invokes target inst
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[fmp_checked_seal_def, fmp_seal_def,
         venomInstTheory.fn_insts_def]
  >> TRY (qexists `out_inst` >> simp[] >> NO_TAC)
  >> Cases_on `root_layout` >> gvs[]
  >> drule fmpLowerPropsTheory.fmp_fn_insts_blocks_mem >> strip_tac
  >> drule fmp_make_root_layout_not_invokes >> strip_tac
  >> drule_all fmp_install_root_invokes >> strip_tac
  >> drule_all fmp_lower_blocks_invokes >> strip_tac
  >> qexists `inst'` >> simp[]
  >> irule fmp_fn_insts_blocks_intro >> metis_tac[]
QED


Theorem fmp_lower_function_invoke_targets_subset:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  EVERY (\target. MEM target (MAP FST (fcg_scan_function fn)))
        (MAP FST (fcg_scan_function fn'))
Proof
  simp[listTheory.EVERY_MEM, fcgDefsTheory.fcg_scan_function_def,
       fcgBridgeTheory.mem_get_invoke_targets]
  >> rpt strip_tac
  >> `fmp_inst_invokes target inst` by
       simp[fmp_inst_invokes_def]
  >> drule_all fmp_lower_function_invokes >> strip_tac
  >> gvs[fmp_inst_invokes_def]
  >> metis_tac[]
QED
val _ = export_theory();
