(*
 * Unit-wide fresh-name and instruction-ID supply.
 *)

Theory irSupply
Ancestors
  venomCompilerWf
  ASCIInumbers
  pred_set
Libs
  listTheory

(* Collectors are deliberately list-valued: duplicates are harmless and the
   resulting definitions remain directly executable. *)
Definition operand_ir_labels_def:
  operand_ir_labels [] = [] /\
  operand_ir_labels (Label l :: ops) = l :: operand_ir_labels ops /\
  operand_ir_labels (_ :: ops) = operand_ir_labels ops
End

Definition inst_ir_vars_def:
  inst_ir_vars inst = inst.inst_outputs ++ inst_uses inst
End

Definition inst_ir_labels_def:
  inst_ir_labels inst = operand_ir_labels inst.inst_operands
End

Definition block_ir_inst_ids_def:
  block_ir_inst_ids bb = MAP (\inst. inst.inst_id) bb.bb_instructions
End

Definition block_ir_vars_def:
  block_ir_vars bb = FLAT (MAP inst_ir_vars bb.bb_instructions)
End

Definition block_ir_labels_def:
  block_ir_labels bb = bb.bb_label :: FLAT (MAP inst_ir_labels bb.bb_instructions)
End

Definition fn_ir_inst_ids_def:
  fn_ir_inst_ids fn = FLAT (MAP block_ir_inst_ids fn.fn_blocks)
End

Definition fn_ir_vars_def:
  fn_ir_vars fn = FLAT (MAP block_ir_vars fn.fn_blocks)
End

Definition fn_ir_labels_def:
  fn_ir_labels fn = fn.fn_name :: FLAT (MAP block_ir_labels fn.fn_blocks)
End

Definition data_item_ir_labels_def:
  data_item_ir_labels (DataLabel l) = [l] /\
  data_item_ir_labels (DataBytes bytes) = []
End

Definition data_section_ir_labels_def:
  data_section_ir_labels section =
    section.ds_label :: FLAT (MAP data_item_ir_labels section.ds_items)
End

Definition unit_ir_inst_ids_def:
  unit_ir_inst_ids unit =
    FLAT (MAP fn_ir_inst_ids unit.cu_context.ctx_functions)
End

Definition unit_ir_vars_def:
  unit_ir_vars unit =
    FLAT (MAP fn_ir_vars unit.cu_context.ctx_functions)
End

Definition unit_ir_labels_def:
  unit_ir_labels unit =
    (case unit.cu_context.ctx_entry of NONE => [] | SOME l => [l]) ++
    FLAT (MAP fn_ir_labels unit.cu_context.ctx_functions) ++
    FLAT (MAP data_section_ir_labels unit.cu_data_segment)
End

Theorem MEM_operand_ir_labels:
  MEM l (operand_ir_labels ops) <=> MEM (Label l) ops
Proof
  Induct_on `ops` >> simp[operand_ir_labels_def] >>
  Cases_on `h` >> simp[operand_ir_labels_def]
QED

Theorem MEM_unit_ir_inst_ids:
  MEM id (unit_ir_inst_ids unit) <=>
  ?fn bb inst.
    MEM fn unit.cu_context.ctx_functions /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    id = inst.inst_id
Proof
  simp[unit_ir_inst_ids_def, fn_ir_inst_ids_def, block_ir_inst_ids_def,
       MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem MEM_unit_ir_vars:
  MEM v (unit_ir_vars unit) <=>
  ?fn bb inst.
    MEM fn unit.cu_context.ctx_functions /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    (MEM v inst.inst_outputs \/ MEM v (inst_uses inst))
Proof
  simp[unit_ir_vars_def, fn_ir_vars_def, block_ir_vars_def,
       inst_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_entry:
  unit.cu_context.ctx_entry = SOME l ==>
  MEM l (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def]
QED

Theorem unit_ir_labels_function:
  MEM fn unit.cu_context.ctx_functions ==>
  MEM fn.fn_name (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, fn_ir_labels_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_block:
  MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
  MEM bb.bb_label (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, fn_ir_labels_def, block_ir_labels_def,
       MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_operand:
  MEM fn unit.cu_context.ctx_functions /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM (Label l) inst.inst_operands ==>
  MEM l (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, fn_ir_labels_def, block_ir_labels_def,
       inst_ir_labels_def, MEM_operand_ir_labels, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_section:
  MEM section unit.cu_data_segment ==>
  MEM section.ds_label (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, data_section_ir_labels_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_data_item:
  MEM section unit.cu_data_segment /\ MEM (DataLabel l) section.ds_items ==>
  MEM l (unit_ir_labels unit)
Proof
  strip_tac >>
  simp[unit_ir_labels_def, data_section_ir_labels_def,
       data_item_ir_labels_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  disj2_tac >> qexists `section` >> simp[] >>
  disj2_tac >> qexists `DataLabel l` >> simp[data_item_ir_labels_def]
QED

Definition fresh_name_candidate_def:
  fresh_name_candidate prefix (n:num) = STRCAT prefix (toString n)
End

Definition seek_fresh_name_def:
  seek_fresh_name prefix used n 0 = (fresh_name_candidate prefix n,n) /\
  seek_fresh_name prefix used n (SUC fuel) =
    if MEM (fresh_name_candidate prefix n) used then
      seek_fresh_name prefix used (SUC n) fuel
    else (fresh_name_candidate prefix n,n)
End

Theorem seek_fresh_name_shape:
  seek_fresh_name prefix used n fuel = (name,k) ==>
  name = fresh_name_candidate prefix k /\
  n <= k /\ k <= n + fuel
Proof
  qid_spec_tac `n` >> Induct_on `fuel`
  >- simp[seek_fresh_name_def]
  >> gen_tac >>
  Cases_on `MEM (fresh_name_candidate prefix n) used`
  >- (simp[seek_fresh_name_def] >> strip_tac >>
      first_x_assum drule >> strip_tac >> simp[] >> decide_tac)
  >> simp[seek_fresh_name_def] >> strip_tac >> gvs[]
QED

Theorem fresh_name_candidates_distinct:
  !prefix n count.
  ALL_DISTINCT
    (GENLIST (\i. fresh_name_candidate prefix (n + i)) count)
Proof
  simp[ALL_DISTINCT_GENLIST, fresh_name_candidate_def] >>
  decide_tac
QED

Theorem distinct_members_length_le:
  ALL_DISTINCT xs /\ EVERY (\x. MEM x ys) xs ==>
  LENGTH xs <= LENGTH ys
Proof
  strip_tac >>
  `set xs SUBSET set ys` by gvs[SUBSET_DEF, EVERY_MEM] >>
  `CARD (set xs) <= CARD (set ys)` by
    (irule CARD_SUBSET >> simp[]) >>
  drule ALL_DISTINCT_CARD_LIST_TO_SET >> strip_tac >> gvs[] >>
  `CARD (set ys) <= LENGTH ys` by simp[CARD_LIST_TO_SET] >>
  decide_tac
QED

Theorem seek_fresh_name_checked:
  MEM (FST (seek_fresh_name prefix used n fuel)) used ==>
  !i. i <= fuel ==> MEM (fresh_name_candidate prefix (n + i)) used
Proof
  qid_spec_tac `n` >> Induct_on `fuel`
  >- simp[seek_fresh_name_def]
  >> gen_tac >>
  Cases_on `MEM (fresh_name_candidate prefix n) used`
  >- (simp[seek_fresh_name_def] >> strip_tac >>
      Cases_on `i` >- simp[] >>
      rename1 `SUC j <= SUC fuel` >>
      first_x_assum drule >> strip_tac >> strip_tac >>
      qpat_assum `!i. i <= fuel ==> _` (qspec_then `j` mp_tac) >>
      impl_tac >- decide_tac >> strip_tac >>
      `SUC n + j = SUC j + n` by decide_tac >> gvs[])
  >> simp[seek_fresh_name_def]
QED

Theorem seek_fresh_name_fresh:
  ~MEM (FST (seek_fresh_name prefix used n (LENGTH used))) used
Proof
  strip_tac >>
  `EVERY (\x. MEM x used)
     (GENLIST (\i. fresh_name_candidate prefix (n + i))
              (SUC (LENGTH used)))` by
    (simp[EVERY_GENLIST] >> rpt strip_tac >>
     drule seek_fresh_name_checked >>
     disch_then (qspec_then `i` mp_tac) >>
     impl_tac >- decide_tac >> strip_tac >>
     `n + i = i + n` by decide_tac >> gvs[]) >>
  `ALL_DISTINCT
     (GENLIST (\i. fresh_name_candidate prefix (n + i))
              (SUC (LENGTH used)))` by
    simp[fresh_name_candidates_distinct] >>
  drule_all distinct_members_length_le >> simp[]
QED

Theorem seek_fresh_name_interface:
  seek_fresh_name prefix used n (LENGTH used) = (name,k) ==>
  name = STRCAT prefix (toString k) /\
  n <= k /\ k <= n + LENGTH used /\
  ~MEM name used
Proof
  strip_tac >>
  `name = fresh_name_candidate prefix k /\
   n <= k /\ k <= n + LENGTH used` by
    (drule seek_fresh_name_shape >> simp[]) >>
  `~MEM (FST (seek_fresh_name prefix used n (LENGTH used))) used` by
    simp[seek_fresh_name_fresh] >>
  gvs[fresh_name_candidate_def]
QED

Datatype:
  ir_supply = <|
    irs_next_inst : num;
    irs_next_var : num;
    irs_next_label : num;
    irs_used_inst_ids : num list;
    irs_used_vars : string list;
    irs_used_labels : string list
  |>
End

Definition init_ir_supply_def:
  init_ir_supply unit = <|
    irs_next_inst := SUC (FOLDL MAX 0 (unit_ir_inst_ids unit));
    irs_next_var := 0;
    irs_next_label := 0;
    irs_used_inst_ids := unit_ir_inst_ids unit;
    irs_used_vars := unit_ir_vars unit;
    irs_used_labels := unit_ir_labels unit
  |>
End

Definition fresh_inst_id_def:
  fresh_inst_id s =
    (s.irs_next_inst,
     s with <| irs_next_inst := SUC s.irs_next_inst;
               irs_used_inst_ids := s.irs_next_inst :: s.irs_used_inst_ids |>)
End

Definition fresh_ir_var_def:
  fresh_ir_var s =
    case seek_fresh_name "formal_var_" s.irs_used_vars s.irs_next_var
                         (LENGTH s.irs_used_vars) of
      (name,k) =>
        (name, s with <| irs_next_var := SUC k;
                        irs_used_vars := name :: s.irs_used_vars |>)
End

Definition fresh_ir_label_def:
  fresh_ir_label s =
    case seek_fresh_name "formal_label_" s.irs_used_labels s.irs_next_label
                         (LENGTH s.irs_used_labels) of
      (name,k) =>
        (name, s with <| irs_next_label := SUC k;
                        irs_used_labels := name :: s.irs_used_labels |>)
End

Definition ir_supply_inst_ok_def:
  ir_supply_inst_ok s <=>
    EVERY (\id. id < s.irs_next_inst) s.irs_used_inst_ids
End

Theorem foldl_max_bound:
  !(x:num) (base:num) xs.
  x <= base \/ MEM x xs ==> x <= FOLDL MAX base xs
Proof
  Induct_on `xs`
  >- simp[]
  >> rpt strip_tac >> simp[] >>
  first_x_assum irule >>
  gvs[arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem init_ir_supply_fields:
  (init_ir_supply unit).irs_used_inst_ids = unit_ir_inst_ids unit /\
  (init_ir_supply unit).irs_used_vars = unit_ir_vars unit /\
  (init_ir_supply unit).irs_used_labels = unit_ir_labels unit /\
  (init_ir_supply unit).irs_next_var = 0 /\
  (init_ir_supply unit).irs_next_label = 0
Proof
  simp[init_ir_supply_def]
QED

Theorem init_ir_supply_inst_id_bound:
  MEM id (unit_ir_inst_ids unit) ==>
  id < (init_ir_supply unit).irs_next_inst
Proof
  simp[init_ir_supply_def] >> strip_tac >>
  `id <= FOLDL MAX 0 (unit_ir_inst_ids unit)` by
    (irule foldl_max_bound >> simp[]) >>
  decide_tac
QED

Theorem init_ir_supply_inst_ok:
  ir_supply_inst_ok (init_ir_supply unit)
Proof
  simp[ir_supply_inst_ok_def, EVERY_MEM, init_ir_supply_def] >>
  rpt strip_tac >>
  `id <= FOLDL MAX 0 (unit_ir_inst_ids unit)` by
    (irule foldl_max_bound >> simp[]) >>
  decide_tac
QED

Theorem init_ir_supply_covers_inst:
  MEM fn unit.cu_context.ctx_functions /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
  MEM inst.inst_id (init_ir_supply unit).irs_used_inst_ids /\
  inst.inst_id < (init_ir_supply unit).irs_next_inst
Proof
  strip_tac >>
  `MEM inst.inst_id (unit_ir_inst_ids unit)` by
    (simp[MEM_unit_ir_inst_ids] >> metis_tac[]) >>
  conj_tac
  >- simp[init_ir_supply_def]
  >> simp[init_ir_supply_def] >>
  `inst.inst_id <= FOLDL MAX 0 (unit_ir_inst_ids unit)` by
    (irule foldl_max_bound >> simp[]) >>
  decide_tac
QED

Theorem init_ir_supply_covers_var:
  MEM fn unit.cu_context.ctx_functions /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  (MEM v inst.inst_outputs \/ MEM v (inst_uses inst)) ==>
  MEM v (init_ir_supply unit).irs_used_vars
Proof
  simp[init_ir_supply_def, MEM_unit_ir_vars] >> metis_tac[]
QED

Theorem init_ir_supply_covers_entry:
  unit.cu_context.ctx_entry = SOME l ==>
  MEM l (init_ir_supply unit).irs_used_labels
Proof
  simp[init_ir_supply_def] >> metis_tac[unit_ir_labels_entry]
QED

Theorem init_ir_supply_covers_function_label:
  MEM fn unit.cu_context.ctx_functions ==>
  MEM fn.fn_name (init_ir_supply unit).irs_used_labels
Proof
  simp[init_ir_supply_def] >> metis_tac[unit_ir_labels_function]
QED

Theorem init_ir_supply_covers_block_label:
  MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
  MEM bb.bb_label (init_ir_supply unit).irs_used_labels
Proof
  simp[init_ir_supply_def] >> metis_tac[unit_ir_labels_block]
QED

Theorem init_ir_supply_covers_operand_label:
  MEM fn unit.cu_context.ctx_functions /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM (Label l) inst.inst_operands ==>
  MEM l (init_ir_supply unit).irs_used_labels
Proof
  simp[init_ir_supply_def] >> metis_tac[unit_ir_labels_operand]
QED

Theorem init_ir_supply_covers_section_label:
  MEM section unit.cu_data_segment ==>
  MEM section.ds_label (init_ir_supply unit).irs_used_labels
Proof
  simp[init_ir_supply_def] >> metis_tac[unit_ir_labels_section]
QED

Theorem init_ir_supply_covers_data_label:
  MEM section unit.cu_data_segment /\ MEM (DataLabel l) section.ds_items ==>
  MEM l (init_ir_supply unit).irs_used_labels
Proof
  simp[init_ir_supply_def] >> metis_tac[unit_ir_labels_data_item]
QED

Theorem fresh_inst_id_contract:
  ir_supply_inst_ok s /\ fresh_inst_id s = (id,s') ==>
  id = s.irs_next_inst /\
  ~MEM id s.irs_used_inst_ids /\
  s'.irs_used_inst_ids = id :: s.irs_used_inst_ids /\
  s'.irs_next_inst = SUC s.irs_next_inst /\
  s'.irs_next_var = s.irs_next_var /\
  s'.irs_next_label = s.irs_next_label /\
  s'.irs_used_vars = s.irs_used_vars /\
  s'.irs_used_labels = s.irs_used_labels /\
  ir_supply_inst_ok s'
Proof
  simp[fresh_inst_id_def] >> strip_tac >>
  gvs[ir_supply_inst_ok_def, EVERY_MEM] >>
  conj_tac
  >- (strip_tac >> first_x_assum drule >> decide_tac)
  >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> decide_tac
QED

Theorem fresh_inst_id_preserves_old:
  fresh_inst_id s = (id,s') /\ MEM old s.irs_used_inst_ids ==>
  MEM old s'.irs_used_inst_ids
Proof
  simp[fresh_inst_id_def] >> rpt strip_tac >> gvs[]
QED

Theorem fresh_inst_id_two_calls_distinct:
  ir_supply_inst_ok s /\
  fresh_inst_id s = (id1,s1) /\
  fresh_inst_id s1 = (id2,s2) ==>
  id2 <> id1 /\ ir_supply_inst_ok s2
Proof
  strip_tac >>
  drule fresh_inst_id_contract >> disch_then drule >> strip_tac >>
  qpat_x_assum `ir_supply_inst_ok s` kall_tac >>
  qpat_x_assum `fresh_inst_id s = _` kall_tac >>
  drule fresh_inst_id_contract >> disch_then drule >> strip_tac >>
  gvs[]
QED


Theorem fresh_ir_var_contract:
  fresh_ir_var s = (v,s') ==>
  ~MEM v s.irs_used_vars /\
  s'.irs_used_vars = v :: s.irs_used_vars /\
  s.irs_next_var < s'.irs_next_var /\
  s'.irs_next_inst = s.irs_next_inst /\
  s'.irs_next_label = s.irs_next_label /\
  s'.irs_used_inst_ids = s.irs_used_inst_ids /\
  s'.irs_used_labels = s.irs_used_labels /\
  (?suffix. v = STRCAT "formal_var_" suffix)
Proof
  Cases_on `seek_fresh_name "formal_var_" s.irs_used_vars s.irs_next_var
                            (LENGTH s.irs_used_vars)` >>
  rename1 `seek_fresh_name _ _ _ _ = (name,k)` >>
  drule seek_fresh_name_interface >> strip_tac >>
  gvs[fresh_ir_var_def] >> strip_tac >> gvs[]
QED

Theorem fresh_ir_label_contract:
  fresh_ir_label s = (l,s') ==>
  ~MEM l s.irs_used_labels /\
  s'.irs_used_labels = l :: s.irs_used_labels /\
  s.irs_next_label < s'.irs_next_label /\
  s'.irs_next_inst = s.irs_next_inst /\
  s'.irs_next_var = s.irs_next_var /\
  s'.irs_used_inst_ids = s.irs_used_inst_ids /\
  s'.irs_used_vars = s.irs_used_vars /\
  (?suffix. l = STRCAT "formal_label_" suffix)
Proof
  Cases_on `seek_fresh_name "formal_label_" s.irs_used_labels s.irs_next_label
                            (LENGTH s.irs_used_labels)` >>
  rename1 `seek_fresh_name _ _ _ _ = (name,k)` >>
  drule seek_fresh_name_interface >> strip_tac >>
  gvs[fresh_ir_label_def] >> strip_tac >> gvs[]
QED

Theorem fresh_ir_var_preserves_old:
  fresh_ir_var s = (v,s') /\ MEM old s.irs_used_vars ==>
  MEM old s'.irs_used_vars
Proof
  strip_tac >> drule fresh_ir_var_contract >> strip_tac >> gvs[]
QED

Theorem fresh_ir_label_preserves_old:
  fresh_ir_label s = (l,s') /\ MEM old s.irs_used_labels ==>
  MEM old s'.irs_used_labels
Proof
  strip_tac >> drule fresh_ir_label_contract >> strip_tac >> gvs[]
QED

Theorem fresh_ir_var_two_calls_distinct:
  fresh_ir_var s = (v1,s1) /\ fresh_ir_var s1 = (v2,s2) ==>
  v2 <> v1
Proof
  strip_tac >>
  qpat_assum `fresh_ir_var s = (v1,s1)`
    (mp_tac o MATCH_MP fresh_ir_var_contract) >> strip_tac >>
  `MEM v1 s1.irs_used_vars` by gvs[] >>
  qpat_assum `fresh_ir_var s1 = (v2,s2)`
    (mp_tac o MATCH_MP fresh_ir_var_contract) >> strip_tac >>
  metis_tac[]
QED

Theorem fresh_ir_label_two_calls_distinct:
  fresh_ir_label s = (l1,s1) /\ fresh_ir_label s1 = (l2,s2) ==>
  l2 <> l1
Proof
  strip_tac >>
  qpat_assum `fresh_ir_label s = (l1,s1)`
    (mp_tac o MATCH_MP fresh_ir_label_contract) >> strip_tac >>
  `MEM l1 s1.irs_used_labels` by gvs[] >>
  qpat_assum `fresh_ir_label s1 = (l2,s2)`
    (mp_tac o MATCH_MP fresh_ir_label_contract) >> strip_tac >>
  metis_tac[]
QED

val _ = export_theory ();
