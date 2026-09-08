(*
 * Well-formedness boundaries for checked static memory layouts.
 *
 * This theory deliberately sits downstream of core Venom WF: venomWfTheory
 * must not depend on concretization vocabulary.
 *)

Theory staticLayoutWf
Ancestors
  venomWf
  staticLayoutDefs
  concretizeMemLocDefs

(* A concrete placement is representable and does not overlap any reserved
   global interval.  Zero-sized ALLOCAs remain admissible, matching the
   checked EOM fold. *)
Definition static_position_wf_def:
  static_position_wf reserved pos size <=>
    pos + w2n size < dimword (:256) /\
    (0 < w2n size ==>
     EVERY (reserved_intervals_disjoint (pos,w2n size)) reserved)
End

(* Every externally forced numeric ID must identify a well-shaped source
   ALLOCA at the supplied position. *)
Definition forced_positions_wf_def:
  forced_positions_wf reserved fn <=>
    !aid pos.
      FLOOKUP fn.fn_forced_alloc_positions aid = SOME pos ==>
      ?inst size.
        MEM inst (fn_insts fn) /\
        inst.inst_id = aid /\
        inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit size] /\
        static_position_wf reserved pos size
End

(* Every allocation-keyed map entry must likewise identify a source ALLOCA.
   Completeness of a candidate map is stated separately in
   concretize_layout_wf so consumers can use either direction directly. *)
Definition static_fn_positions_wf_def:
  static_fn_positions_wf reserved positions fn <=>
    !aid pos.
      FLOOKUP positions (Allocation aid) = SOME pos ==>
      ?inst size.
        MEM inst (fn_insts fn) /\
        inst.inst_id = aid /\
        inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit size] /\
        static_position_wf reserved pos size
End

(* Inputs at the raw/static-allocation phase boundary. *)
Definition raw_static_inputs_wf_def:
  raw_static_inputs_wf ctx <=>
    reserved_intervals_wf ctx.ctx_global_reserved /\
    ctx_inst_ids_distinct ctx /\
    !fn. MEM fn ctx.ctx_functions ==>
      fn.fn_eom = NONE /\
      fn.fn_fmp_signature = NONE /\
      forced_positions_wf ctx.ctx_global_reserved fn
End

(* Outputs after static ALLOCAs have been consumed and concretized. *)
Definition concretized_static_layouts_wf_def:
  concretized_static_layouts_wf ctx <=>
    reserved_intervals_wf ctx.ctx_global_reserved /\
    !fn. MEM fn ctx.ctx_functions ==>
      fn.fn_forced_alloc_positions = FEMPTY /\
      IS_SOME fn.fn_eom /\
      (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> ALLOCA)
End

(* A candidate certificate is total for source ALLOCAs, bounded by its EOM,
   contains no spurious allocation IDs, and agrees exactly with both checked
   folds. *)
Definition concretize_layout_wf_def:
  concretize_layout_wf reserved fn layout <=>
    static_fn_positions_wf reserved layout.cl_positions fn /\
    layout.cl_eom < dimword (:256) /\
    (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
      ?size pos.
        inst.inst_operands = [Lit size] /\
        FLOOKUP layout.cl_positions (Allocation inst.inst_id) = SOME pos /\
        pos + w2n size <= layout.cl_eom /\
        static_position_wf reserved pos size) /\
    ?global_eom.
      global_reserved_end reserved 0 = SOME global_eom /\
      allocation_eom_fold layout.cl_positions (fn_insts fn) global_eom =
        SOME layout.cl_eom
End

Theorem static_wf_dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED


Theorem static_position_wf_zero:
  static_position_wf reserved pos (0w : 256 word) <=>
  pos < dimword (:256)
Proof
  simp[static_position_wf_def]
QED

val _ = export_theory();
