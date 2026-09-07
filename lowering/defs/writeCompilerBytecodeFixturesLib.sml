structure writeCompilerBytecodeFixturesLib = struct

open HolKernel

val _ = evalCompilerTheory.noop_program_def
val _ = evalCompilerBytecodeDefsTheory.formal_o1_ir_no_asm_opt_pipeline

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

fun constant thy name = prim_mk_const {Thy = thy, Name = name}
val profile_tm = constant "evalCompilerBytecodeDefs" "formal_o1_ir_no_asm_opt"
val fuel_tm = numSyntax.term_of_int 100000
fun program name = constant "evalCompiler" (name ^ "_program")
val program_ty = type_of (program "noop")
val top_ty = listSyntax.dest_list_type program_ty
val empty_program = listSyntax.mk_nil top_ty
fun compiler_tm source = list_mk_comb (profile_tm, [fuel_tm, source])

type registry_entry =
  {name : string, filename : string, source : term, fuels : int list}

val registry : registry_entry list =
  [{name = "empty", filename = "empty.hex", source = empty_program,
    fuels = [16, 32, 64, 128, 256]},
   {name = "noop", filename = "noop.hex", source = program "noop",
    fuels = [16, 32, 64, 128, 256]},
   {name = "return_uint", filename = "return_uint.hex",
    source = program "return_uint", fuels = [16, 32, 64, 128, 256]},
   {name = "return_arg", filename = "return_arg.hex",
    source = program "return_arg", fuels = [16, 32, 64, 128, 256]},
   {name = "local_uint", filename = "local_uint.hex",
    source = program "local_uint", fuels = [16, 32, 64, 128, 256]},
   {name = "add_arg", filename = "add_arg.hex", source = program "add_arg",
    fuels = [16, 32, 64, 128, 256]},
   {name = "two_external", filename = "two_external.hex",
    source = program "two_external", fuels = [16, 32, 64, 128, 256]},
   {name = "storage_read", filename = "storage_read.hex",
    source = program "storage_read", fuels = [16, 32, 64, 128, 256]},
   {name = "storage_write", filename = "storage_write.hex",
    source = program "storage_write", fuels = [16, 32, 64, 128, 256]},
   {name = "deploy_storage", filename = "deploy_storage.hex",
    source = program "deploy_storage", fuels = [16, 32, 64, 128, 256]},
   {name = "event_log", filename = "event_log.hex",
    source = program "event_log", fuels = [16, 32, 64, 128, 256]},
   {name = "indexed_event_log", filename = "indexed_event_log.hex",
    source = program "indexed_event_log", fuels = [16, 32, 64, 128, 256]},
   {name = "mixed_event_log", filename = "mixed_event_log.hex",
    source = program "mixed_event_log", fuels = [16, 32, 64, 128, 256]},
   {name = "hashmap_read", filename = "hashmap_read.hex",
    source = program "hashmap_read", fuels = [16, 32, 64, 128, 256]},
   {name = "hashmap_write", filename = "hashmap_write.hex",
    source = program "hashmap_write", fuels = [16, 32, 64, 128, 256]},
   {name = "if_bool", filename = "if_bool.hex", source = program "if_bool",
    fuels = [16, 32, 64, 128, 256]},
   {name = "if_join", filename = "if_join.hex", source = program "if_join",
    fuels = [16, 32, 64, 128, 256]},
   {name = "for_pass", filename = "for_pass.hex", source = program "for_pass",
    fuels = [16, 32, 64, 128, 256]},
   {name = "for_accum", filename = "for_accum.hex",
    source = program "for_accum", fuels = [16, 32, 64, 128, 256]},
   {name = "for_continue", filename = "for_continue.hex",
    source = program "for_continue", fuels = [100000]},
   {name = "for_break", filename = "for_break.hex",
    source = program "for_break", fuels = [16, 32, 64, 128, 256]},
   {name = "internal_call", filename = "internal_call.hex",
    source = program "internal_call", fuels = [100000]},
   {name = "internal_call_arg", filename = "internal_call_arg.hex",
    source = program "internal_call_arg", fuels = [16, 32, 64, 128, 256]}]

fun duplicates [] = []
  | duplicates (x :: xs) =
      if List.exists (fn y => y = x) xs then x :: duplicates xs
      else duplicates xs

fun validate_registry () =
  let
    val _ = if length registry = 23 then ()
            else raise Fail "bytecode fixture registry must contain exactly 23 entries"
    val names = map #name registry
    val files = map #filename registry
    val duplicate_names = duplicates names
    val duplicate_files = duplicates files
    val _ = if null duplicate_names then () else
      raise Fail ("duplicate bytecode fixture names: " ^
                  String.concatWith ", " duplicate_names)
    val _ = if null duplicate_files then () else
      raise Fail ("duplicate bytecode fixture files: " ^
                  String.concatWith ", " duplicate_files)
  in () end

fun evaluate_entry ({name, filename, source, fuels} : registry_entry) =
  let
    val _ = print ("evaluating formal O1 fixture " ^ name ^ "...\n")
    val th = evalCompilerBytecodeLib.closed_compiler_eval_with_fuels fuels
      (compiler_tm source)
    val bytes = evalCompilerBytecodeLib.extract_compiler_pair name th
    val rendered = evalCompilerBytecodeLib.render_fixture bytes
    val _ = PolyML.fullGC ()
  in
    (filename, rendered)
  end


fun lookup_entry name =
  case List.filter (fn ({name = n, ...} : registry_entry) => n = name)
         registry of
    [entry] => entry
  | [] => raise Fail ("unknown formal O1 fixture name: " ^ name)
  | _ => raise Fail ("duplicate formal O1 fixture name: " ^ name)

fun write_stage_atomic stage_dir (filename, contents) =
  let
    val path = OS.Path.concat (stage_dir, filename)
    val tmp = path ^ ".tmp"
    val _ = (OS.FileSys.remove tmp handle OS.SysErr _ => ())
    val output = TextIO.openOut tmp
    val _ = TextIO.output (output, contents)
    val _ = TextIO.closeOut output
    val _ = OS.FileSys.rename {old = tmp, new = path}
  in () end

fun stage_one name stage_dir =
  let
    val _ = validate_registry ()
    val entry = lookup_entry name
    val artifact = evaluate_entry entry
  in
    write_stage_atomic stage_dir artifact
  end

fun require_env key =
  case OS.Process.getEnv key of
    SOME value => if value = "" then raise Fail (key ^ " is empty") else value
  | NONE => raise Fail (key ^ " is not set")

fun run () =
  stage_one (require_env "FORMAL_O1_FIXTURE_NAME")
            (require_env "FORMAL_O1_FIXTURE_STAGE_DIR")

end
