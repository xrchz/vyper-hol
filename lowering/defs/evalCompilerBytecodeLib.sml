(*
 * Eval compiler bytecode fixtures
 *
 * TOP-LEVEL:
 *   read_hex_bytes -- read deploy/runtime hex fixture into a bytecode pair term
 *)

structure evalCompilerBytecodeLib = struct

open HolKernel Parse boolLib bossLib

fun read_all path =
  let
    val input = TextIO.openIn path
  in
    TextIO.inputAll input before TextIO.closeIn input
  end

fun trim s =
  let
    val len = size s
    fun left i =
      if i >= len then len
      else if Char.isSpace (String.sub (s, i)) then left (i + 1)
      else i
    fun right i =
      if i < 0 then ~1
      else if Char.isSpace (String.sub (s, i)) then right (i - 1)
      else i
    val lo = left 0
    val hi = right (len - 1)
  in
    if hi < lo then "" else String.substring (s, lo, hi - lo + 1)
  end

fun strip_comment line =
  trim (case String.fields (fn c => c = #"#") line of
          [] => line
        | before_comment :: _ => before_comment)

fun fixture_line line =
  case strip_comment line of
    "" => NONE
  | line =>
      (case String.fields (fn c => c = #"=") line of
         [key, value] => SOME (trim key, trim value)
       | _ => raise Fail ("bad bytecode fixture line: " ^ line))

fun resolve_bytecode_fixture filename =
  let
    val candidates =
      [OS.Path.concat ("bytecode", filename),
       OS.Path.concat ("lowering/defs/bytecode", filename)]
  in
    case List.find
           (fn path => OS.FileSys.access (path, [OS.FileSys.A_READ]))
           candidates of
      SOME path => path
    | NONE => raise Fail ("missing bytecode fixture: " ^ filename)
  end

fun bytecode_fixture_value filename entries key =
  case List.find (fn (entry_key, _) => entry_key = key) entries of
    SOME (_, value) => value
  | NONE => raise Fail ("missing " ^ key ^ " in bytecode fixture: " ^ filename)

fun drop_hex_prefix s =
  if String.isPrefix "0x" s orelse String.isPrefix "0X" s then
    String.extract (s, 2, NONE)
  else
    s

fun compact_hex s =
  String.implode (List.filter (not o Char.isSpace)
    (String.explode (drop_hex_prefix s)))

fun hex_digit c =
  if #"0" <= c andalso c <= #"9" then
    Char.ord c - Char.ord #"0"
  else if #"a" <= c andalso c <= #"f" then
    10 + Char.ord c - Char.ord #"a"
  else if #"A" <= c andalso c <= #"F" then
    10 + Char.ord c - Char.ord #"A"
  else
    raise Fail ("bad hex digit: " ^ String.str c)

fun hex_bytes_tm hex =
  let
    val hex = compact_hex hex
    val len = size hex
    val byte_ty = type_of (wordsSyntax.mk_wordii (0, 8))
    val _ =
      if len mod 2 = 0 then ()
      else raise Fail "hex bytecode fixture has odd length"
    fun bytes i acc =
      if i >= len then
        List.rev acc
      else
        let
          val n =
            16 * hex_digit (String.sub (hex, i)) +
            hex_digit (String.sub (hex, i + 1))
        in
          bytes (i + 2) (wordsSyntax.mk_wordii (n, 8) :: acc)
        end
  in
    listSyntax.mk_list (bytes 0 [], byte_ty)
  end

fun read_hex_bytes filename =
  let
    val path = resolve_bytecode_fixture filename
    val entries =
      List.mapPartial fixture_line
        (String.tokens (fn c => c = #"\n" orelse c = #"\r")
           (read_all path))
    val deploy = bytecode_fixture_value filename entries "deploy"
    val runtime = bytecode_fixture_value filename entries "runtime"
  in
    pairSyntax.mk_pair (hex_bytes_tm deploy, hex_bytes_tm runtime)
  end


(* Closed evaluation for the configured compiler.  Planner calls are first
   solved at small fuel and lifted to the requested bound using the proved
   stability theorem, avoiding an impractical direct evaluation. *)
val fn_plan_aux_fuel_tm = ``generate_fn_plan_aux_fuel``

fun rator_n_conv 0 conv = conv
  | rator_n_conv n conv = RATOR_CONV (rator_n_conv (n - 1) conv)

fun closed_fn_plan_aux_success_conv_with_fuels fuels tm =
  let
    val (head, args) = strip_comb tm
    val _ = if aconv head fn_plan_aux_fuel_tm andalso length args = 8
            then () else raise UNCHANGED
    val target_fuel = hd args
    val target_n = numSyntax.int_of_term target_fuel
    fun seek [] = raise Fail "no successful planner run within bounded fuel"
      | seek (n :: ns) =
          let
            val low_fuel = numSyntax.term_of_int n
            val low_tm = list_mk_comb (head, low_fuel :: tl args)
            val low_thm = computeLib.EVAL_CONV low_tm
            val low_rhs = rhs (concl low_thm)
          in
            if optionSyntax.is_some low_rhs then
              (n, low_fuel, low_thm, optionSyntax.dest_some low_rhs)
            else seek ns
          end
    val (n, low_fuel, low_thm, result) = seek fuels
    val _ = if n <= target_n then ()
            else raise Fail "successful probe fuel exceeds target fuel"
    val extra = numSyntax.term_of_int (target_n - n)
    val stable = SPECL (low_fuel :: tl args @ [result, extra])
      evalCompilerBytecodeDefsTheory.generate_fn_plan_aux_fuel_success_stable
    val lifted = MATCH_MP stable low_thm
    val normalized =
      CONV_RULE
        (LHS_CONV (rator_n_conv 7 (RAND_CONV computeLib.EVAL_CONV)))
        lifted
    val _ = if aconv (lhs (concl normalized)) tm then ()
            else raise Fail "lifted planner theorem does not match target"
  in
    normalized
  end

fun closed_compiler_eval_with_fuels fuels tm =
  let
    val partial = computeLib.RESTR_EVAL_CONV [``generate_fn_plan_aux_fuel``] tm
    val simplified =
      SIMP_RULE (srw_ss())
        [finite_mapTheory.FEVERY_FEMPTY,
         venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
        partial
    val staged =
      CONV_RULE
        (RAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_fn_plan_aux_fuel``]))
        simplified
    val planners =
      CONV_RULE
        (RAND_CONV
          (DEPTH_CONV (closed_fn_plan_aux_success_conv_with_fuels fuels)))
        staged
  in
    CONV_RULE (RAND_CONV computeLib.EVAL_CONV) planners
  end

fun closed_compiler_eval tm =
  closed_compiler_eval_with_fuels [16, 32, 64, 128, 256] tm

fun byte_values tm =
  let
    val (items, _) = listSyntax.dest_list tm
    fun one item =
      let
        val n = Arbnum.toInt (wordsSyntax.dest_word_literal item)
      in
        if 0 <= n andalso n < 256 then n
        else raise Fail "compiler produced a non-byte word"
      end
  in
    map one items
  end

fun extract_compiler_pair name th =
  let
    val result = rhs (concl th)
    val _ = if optionSyntax.is_some result then ()
            else raise Fail ("compilation failed for " ^ name)
    val pair = optionSyntax.dest_some result
    val (deploy, runtime) = pairSyntax.dest_pair pair
  in
    (byte_values deploy, byte_values runtime)
  end
  handle HOL_ERR _ =>
    raise Fail ("malformed compiler result for " ^ name ^
                ": expected SOME (deploy, runtime)")

val hex_digits = "0123456789abcdef"
fun byte_hex n =
  String.implode [String.sub (hex_digits, n div 16),
                  String.sub (hex_digits, n mod 16)]
fun bytes_hex bytes = String.concat (map byte_hex bytes)

fun render_fixture (deploy, runtime) =
  "deploy=" ^ bytes_hex deploy ^ "\n" ^
  "runtime=" ^ bytes_hex runtime ^ "\n"

fun fixture_output_dir () =
  if OS.FileSys.isDir "lowering/defs/bytecode" handle OS.SysErr _ => false
  then "lowering/defs/bytecode"
  else if OS.FileSys.isDir "bytecode" handle OS.SysErr _ => false
  then "bytecode"
  else raise Fail "cannot locate lowering/defs/bytecode fixture directory"

fun fixture_output_path filename =
  OS.Path.concat (fixture_output_dir (), filename)

fun file_contents_if_present path =
  if OS.FileSys.access (path, [OS.FileSys.A_READ]) then SOME (read_all path)
  else NONE

fun write_atomic_if_changed (filename, contents) =
  let
    val path = fixture_output_path filename
  in
    case file_contents_if_present path of
      SOME old => if old = contents then false else
        let
          val tmp = path ^ ".tmp"
          val _ = (OS.FileSys.remove tmp handle OS.SysErr _ => ())
          val output = TextIO.openOut tmp
          val _ = TextIO.output (output, contents)
          val _ = TextIO.closeOut output
          val _ = OS.FileSys.rename {old = tmp, new = path}
        in true end
    | NONE =>
        let
          val tmp = path ^ ".tmp"
          val _ = (OS.FileSys.remove tmp handle OS.SysErr _ => ())
          val output = TextIO.openOut tmp
          val _ = TextIO.output (output, contents)
          val _ = TextIO.closeOut output
          val _ = OS.FileSys.rename {old = tmp, new = path}
        in true end
  end

fun check_fixture (filename, expected) =
  case file_contents_if_present (fixture_output_path filename) of
    NONE => SOME (filename ^ " (missing)")
  | SOME actual =>
      if actual = expected then NONE else SOME (filename ^ " (stale)")
end
