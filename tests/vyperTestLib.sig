signature vyperTestLib = sig

  val generate_tests : unit -> unit (* main generation function *)

  val test_files : unit -> (string * string) list
  val holbuild_extra_deps : string list -> unit
  val make_definitions_for_file : string * string -> unit
  val generate_defn_scripts : unit -> unit
  val generate_test_scripts : unit -> unit

end
