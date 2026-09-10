structure compilerEvalLib :> compilerEvalLib = struct

open HolKernel
open asmIRTheory planExecTheory symbolResolveTheory

(* This first layer contains only the mechanical tail

     stack_op list -> asm_inst list -> byte list.

   Keep the datatype and theorem inventories explicit: residual constants in
   test results should lead to a deliberate addition here rather than copying
   computeLib's global compset. *)
val final_codegen_types =
  [``:venomState$operand``, ``:asmIR$asm_inst``, ``:asmIR$stack_op``,
   ``:venomInst$data_item``, ``:venomInst$data_section``,
   ``:stackPlanTypes$spill_region``, ``:stackPlanTypes$context_plan``,
   ``:'a list``, ``:'a option``, ``:'a # 'b``]

val final_codegen_defs =
  [encode_num_bytes_def,
   data_section_asm_def, data_segment_asm_def,
   swap_name_def, dup_name_def, exec_stack_op_def, execute_plan_def,
   stackPlanGenTheory.revert_postamble_def,
   stackPlanGenTheory.context_plan_ops_def,
   evm_opcode_table_def, evm_opcode_byte_def, symbol_size_def, pad_bytes_def,
   asm_inst_size_def, compute_label_offsets_def, encode_inst_def, assemble_def]

fun build_final_codegen_compset () =
  reduceLib.num_compset
  |> computeLib.copy
  |> listSimps.list_rws
  |> pairLib.add_pair_compset
  |> combinLib.add_combin_compset
  |> optionLib.OPTION_rws
  |> stringLib.add_string_compset
  |> wordsLib.add_words_compset false
  |> finite_mapLib.add_finite_map_compset
  |> alistLib.add_alist_compset
  |> computeLib.add_conv (``REPLICATE``, 2, listLib.REPLICATE_CONV)
  |> computeLib.extend_compset [computeLib.Tys final_codegen_types]
  |> computeLib.add_thms final_codegen_defs

val final_codegen_compset =
  build_final_codegen_compset () |> computeLib.seal

val final_codegen_conv = computeLib.CBV_CONV final_codegen_compset

end
