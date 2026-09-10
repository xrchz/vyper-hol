Theory vyperCheckContractLibTest
Ancestors
  vyperTypeContract
Libs
  vyperCheckContractLib

val empty_layouts =
  ``([] : (address # (storage_layout # storage_layout)) list)``
val empty_modules =
  ``([(NONE, [])] : (num option # toplevel list) list)``
val zero_address = ``(0w : address)``

fun assert_some th =
  if optionSyntax.is_some (rhs (concl th)) then ()
  else raise Fail "expected successful check_contract result"

fun assert_none th =
  if optionSyntax.is_none (rhs (concl th)) then ()
  else raise Fail "expected rejected check_contract result"

(* Basic API and ML-Boolean construction. *)
val empty_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = empty_modules}
val () = assert_some empty_check

(* Storage layout lookup and public getter artifact construction. *)
val storage_modules =
  ``([(NONE,
       [VariableDecl Public Storage "stored" (BaseT (UintT 256)) (SOME 0);
        FunctionDecl External View F F "read" [] [] (BaseT (UintT 256))
          [Return (SOME
             (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]])]
      : (num option # toplevel list) list)``
val storage_layouts =
  ``([((0w : address),
       ([((NONE, "stored"), 0)] : storage_layout, [] : storage_layout))]
      : (address # (storage_layout # storage_layout)) list)``
val storage_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = storage_layouts,
   address = zero_address, modules = storage_modules}
val () = assert_some storage_check

(* This requires the checker-specific existential witness conversion, default
   argument typing, string computation, and internal call-graph evaluation. *)
val internal_modules =
  ``([(NONE,
       [FunctionDecl Internal Nonpayable F F "bar"
          [("x", BaseT (UintT 256))]
          [Literal (BaseT (UintT 256)) (IntL 7)]
          (BaseT (UintT 256))
          [Return (SOME (Name (BaseT (UintT 256)) "x"))];
        FunctionDecl External Nonpayable F F "foo" [] []
          (BaseT (UintT 256))
          [Return (SOME
             (Call (BaseT (UintT 256)) (IntCall (NONE, "bar")) [] NONE))]])]
      : (num option # toplevel list) list)``
val internal_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = internal_modules}
val () = assert_some internal_check

(* Compiler-generated integer conversions require valid_conversion to compute. *)
val conversion_modules =
  ``([(NONE,
       [FunctionDecl External Pure F F "widen"
          [("x", BaseT (UintT 8))] [] (BaseT (UintT 256))
          [Return (SOME
             (TypeBuiltin (BaseT (UintT 256)) Convert
               (BaseT (UintT 256))
               [Name (BaseT (UintT 8)) "x"]))]])]
      : (num option # toplevel list) list)``
val conversion_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = conversion_modules}
val () = assert_some conversion_check

(* len() requires sized-type classification to compute. *)
val sized_modules =
  ``([(NONE,
       [FunctionDecl External Pure F F "array_len"
          [("xs", ArrayT (BaseT AddressT) (Dynamic 4))] []
          (BaseT (UintT 256))
          [Return (SOME
             (Builtin (BaseT (UintT 256)) Len
               [Name (ArrayT (BaseT AddressT) (Dynamic 4)) "xs"]))]])]
      : (num option # toplevel list) list)``
val sized_check = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = sized_modules}
val () = assert_some sized_check

(* The conversion itself computes rejection to NONE. The success-only API must
   fail closed on that result. *)
val recursive_modules =
  ``([(NONE,
       [FunctionDecl Internal Nonpayable F F "loop" [] []
          (BaseT (UintT 256))
          [Return (SOME
             (Call (BaseT (UintT 256)) (IntCall (NONE, "loop")) [] NONE))]])]
      : (num option # toplevel list) list)``
val recursive_application = vyperCheckContractLib.mk_check_contract
  {in_deploy = false, layouts = empty_layouts,
   address = zero_address, modules = recursive_modules}
val recursive_check =
  vyperCheckContractLib.check_contract_conv recursive_application
val () = assert_none recursive_check
fun fails thunk = ((thunk (); false) handle _ => true)
val () =
  if fails (fn () => ignore (vyperCheckContractLib.check_contract
       {in_deploy = false, layouts = empty_layouts,
        address = zero_address, modules = recursive_modules})) then ()
  else raise Fail "success API accepted a rejected contract"

(* Open inputs are rejected before conversion. *)
val () =
  if fails (fn () => ignore (vyperCheckContractLib.mk_check_contract
       {in_deploy = false, layouts = empty_layouts,
        address = mk_var ("address", type_of zero_address),
        modules = empty_modules})) then ()
  else raise Fail "open checker input was accepted"

(* The exported compset is cached and sealed, while copy permits functional
   caller extension without changing the library instance. *)
val checker_copy =
  vyperCheckContractLib.check_contract_compset |> computeLib.copy
val copied_empty_check = computeLib.CBV_CONV checker_copy
  (vyperCheckContractLib.mk_check_contract
    {in_deploy = false, layouts = empty_layouts,
     address = zero_address, modules = empty_modules})
val () = assert_some copied_empty_check
