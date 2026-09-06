(*
 * Concrete EVM event encoding for the Vyper semantics.
 *
 * TOP-LEVEL:
 *   event_metadata             -- resolved declaration encoding information
 *   lookup_event_metadata      -- resolve an event directly from loaded sources
 *   encode_vyper_event_metadata -- encode already-resolved metadata
 *   encode_vyper_event         -- compatibility wrapper for lookup functions
 *   encode_source_event        -- resolve and encode from authoritative sources
 *   encode_raw_event           -- construct an EVM event for raw_log
 *   encode_raw_event_values    -- construct raw_log output from Vyper values
 *)

Theory vyperEvent
Ancestors
  cv cv_std vyperABI vyperValue contractABI vfmTypes
  byte keccak words
Libs
  cv_transLib wordsLib

Type event_metadata = “:num # type list # bool list”
Type event_info = “:string -> event_metadata option”

Definition event_hash_def:
  event_hash tenv ename (arg_types : type list) =
    let abi_types = vyper_to_abi_types tenv arg_types in
    let sig_str = function_signature ename abi_types in
    let hash_bytes = Keccak_256_w64 (MAP (n2w o ORD) sig_str) in
    num_of_bytes (be_bytes 32 [] hash_bytes)
End

Definition lookup_event_metadata_in_def:
  lookup_event_metadata_in _ _ [] = NONE ∧
  lookup_event_metadata_in tenv ename (EventDecl name args_indexed :: rest) =
    (if name = ename then
       let arg_types = MAP (SND o FST) args_indexed in
       let indexed_flags = MAP SND args_indexed in
         SOME (event_hash tenv name arg_types, arg_types, indexed_flags)
     else lookup_event_metadata_in tenv ename rest) ∧
  lookup_event_metadata_in tenv ename (_ :: rest) =
    lookup_event_metadata_in tenv ename rest
End

Theorem lookup_event_metadata_in_some:
  lookup_event_metadata_in tenv ename tops = SOME metadata ⇒
  ∃args.
    MEM (EventDecl ename args) tops ∧
    metadata =
      (event_hash tenv ename (MAP (SND o FST) args),
       MAP (SND o FST) args,
       MAP SND args)
Proof
  Induct_on `tops`
  >- simp[lookup_event_metadata_in_def]
  >> Cases_on `h`
  >> gvs[lookup_event_metadata_in_def]
  >> Cases_on `s = ename`
  >> gvs[]
  >> strip_tac
  >> qexists `l`
  >> simp[]
QED

Definition lookup_event_metadata_def:
  lookup_event_metadata tenv sources target (src_id_opt, ename) =
    case ALOOKUP sources target of
    | NONE => NONE
    | SOME mods =>
        case ALOOKUP mods src_id_opt of
        | NONE => NONE
        | SOME tops => lookup_event_metadata_in tenv ename tops
End

(* A name resolves to at most one event declaration shape in a module. *)
Definition event_decl_unique_def:
  event_decl_unique ename tops ⇔
    ∀args args'.
      MEM (EventDecl ename args) tops ∧
      MEM (EventDecl ename args') tops ⇒
      args = args'
End

Definition is_event_bytestring_type_def:
  is_event_bytestring_type (BaseT (BytesT (Dynamic _))) = T ∧
  is_event_bytestring_type (BaseT (StringT _)) = T ∧
  is_event_bytestring_type _ = F
End

(* Primitive word encoding used for indexed, statically-sized arguments. *)
Definition event_value_to_word_def:
  event_value_to_word (BoolV b) = (if b then 1w else 0w : bytes32) ∧
  event_value_to_word (IntV n) = (i2w n : bytes32) ∧
  event_value_to_word (FlagV k) = (n2w k : bytes32) ∧
  event_value_to_word (DecimalV n) = (i2w n : bytes32) ∧
  event_value_to_word (BytesV bs) =
    (if LENGTH bs = 20 then word_of_bytes_be (PAD_LEFT 0w 32 bs)
     else word_of_bytes_be (PAD_RIGHT 0w 32 bs)) ∧
  event_value_to_word _ = 0w
End

Definition encode_event_topic_def:
  encode_event_topic T (BytesV bs) =
    SOME (word_of_bytes_be (Keccak_256_w64 bs)) ∧
  encode_event_topic T (StringV s) =
    SOME (word_of_bytes_be (Keccak_256_w64 (MAP (n2w o ORD) s))) ∧
  encode_event_topic T _ = NONE ∧
  encode_event_topic F v = SOME (event_value_to_word v)
End

Definition encode_indexed_event_topics_def:
  encode_indexed_event_topics [] [] [] = SOME ([] : bytes32 list) ∧
  encode_indexed_event_topics (T::fs) (ty::tys) (v::vs) =
    (case encode_event_topic (is_event_bytestring_type ty) v of
     | NONE => NONE
     | SOME topic =>
         OPTION_MAP (CONS topic) (encode_indexed_event_topics fs tys vs)) ∧
  encode_indexed_event_topics (F::fs) (_::tys) (_::vs) =
    encode_indexed_event_topics fs tys vs ∧
  encode_indexed_event_topics _ _ _ = NONE
End

Definition non_indexed_event_args_def:
  non_indexed_event_args [] [] [] = SOME ([] : (type # value) list) ∧
  non_indexed_event_args (T::fs) (_::tys) (_::vs) =
    non_indexed_event_args fs tys vs ∧
  non_indexed_event_args (F::fs) (ty::tys) (v::vs) =
    OPTION_MAP (CONS (ty,v)) (non_indexed_event_args fs tys vs) ∧
  non_indexed_event_args _ _ _ = NONE
End

val encode_indexed_event_topics_pre_def =
  cv_auto_trans_pre "encode_indexed_event_topics_pre"
                    encode_indexed_event_topics_def;

Theorem encode_indexed_event_topics_pre[cv_pre]:
  ∀flags tys vals. encode_indexed_event_topics_pre flags tys vals
Proof
  ho_match_mp_tac encode_indexed_event_topics_ind >> rw[] >>
  rw[Once encode_indexed_event_topics_pre_def]
QED

val non_indexed_event_args_pre_def =
  cv_auto_trans_pre "non_indexed_event_args_pre" non_indexed_event_args_def;

Theorem non_indexed_event_args_pre[cv_pre]:
  ∀flags tys vals. non_indexed_event_args_pre flags tys vals
Proof
  ho_match_mp_tac non_indexed_event_args_ind >> rw[] >>
  rw[Once non_indexed_event_args_pre_def]
QED

Definition encode_vyper_event_metadata_def:
  encode_vyper_event_metadata tenv (logger : address)
                              (event_hash, arg_types, indexed_flags) vals =
    case encode_indexed_event_topics indexed_flags arg_types vals of
    | NONE => NONE
    | SOME indexed_topics =>
        case non_indexed_event_args indexed_flags arg_types vals of
        | NONE => NONE
        | SOME typed_vals =>
            case vyper_to_abi_list tenv (MAP FST typed_vals)
                                        (MAP SND typed_vals) of
            | NONE => NONE
            | SOME abi_vals =>
                SOME <| logger := logger;
                        topics := n2w event_hash :: indexed_topics;
                        data := enc (Tuple (vyper_to_abi_types tenv
                                            (MAP FST typed_vals)))
                                    (ListV abi_vals) |>
End

(* Compatibility wrapper for compiler environments and other lookup maps. *)
Definition encode_vyper_event_def:
  encode_vyper_event event_info tenv logger event_name vals =
    case event_info event_name of
    | NONE => NONE
    | SOME metadata => encode_vyper_event_metadata tenv logger metadata vals
End

Definition encode_source_event_def:
  encode_source_event tenv sources target event_id vals =
    case lookup_event_metadata tenv sources target event_id of
    | NONE => NONE
    | SOME metadata => encode_vyper_event_metadata tenv target metadata vals
End

Definition encode_raw_event_def:
  encode_raw_event (logger : address) topics data : event =
    <| logger := logger; topics := topics; data := data |>
End

Definition encode_raw_event_values_def:
  encode_raw_event_values logger topic_vals data =
    encode_raw_event logger (MAP event_value_to_word topic_vals) data
End
