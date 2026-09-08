(*
 * Eval compiler bytecode fixtures
 *
 * TOP-LEVEL:
 *   read_hex_bytes -- read deploy/runtime hex fixture into a bytecode pair term
 *)

structure evalCompilerBytecodeLib = struct

open HolKernel

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

end
