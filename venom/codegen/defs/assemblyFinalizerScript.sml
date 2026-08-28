(*
 * Optional final-assembly callback boundary.
 *)

Theory assemblyFinalizer
Ancestors
  asmIR
  venomCompilerTypes

Type assembly_finalizer =
  ``:resolved_compiler_policy -> asm_inst list -> asm_inst list option``

val _ = export_theory ();
