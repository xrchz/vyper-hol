(*
 * Venom Memory Proofs
 *
 * Workhorse memory proof theory.  Stable public theorem names are presented in
 * venomMemProps; the `_proof` theorems here are technical sources used to derive
 * that public interface during the ongoing Props/Proofs cleanup.
 *
 * TOP-LEVEL:
 *   alloca_inv_empty_proof                    — alloca_inv holds when allocas map is empty
 *   alloca_inv_step_inst_proof                 — step_inst preserves alloca_inv
 *   alloca_inv_exec_block_proof                — exec_block preserves alloca_inv
 *   alloca_inv_run_block_proof                 — run_block preserves alloca_inv
 *   alloca_inv_run_blocks_proof                — run_blocks preserves alloca_inv
 *   alloca_inv_run_function_proof              — run_function preserves alloca_inv
 *   allocas_non_overlapping_empty_proof       — empty allocas map is non-overlapping
 *   allocas_non_overlapping_step_inst_proof   — step_inst preserves allocas_non_overlapping
 *   allocas_non_overlapping_exec_block_proof  — exec_block preserves allocas_non_overlapping
 *   mload_mstore_disjoint_proof               — 32-byte mstore doesn't affect mload on disjoint region
 *   mload_mstore8_disjoint_proof              — 1-byte mstore8 doesn't affect 32-byte mload on disjoint region
 *)

Theory venomMemProofs
Ancestors
  venomMemDefs venomExecSemantics venomState venomInst venomInstProofs
  venomExecProofs stateEquiv finite_map list rich_list words byte arithmetic divides
Libs
  wordsLib dep_rewrite

(* ===================================================================
   Infrastructure: dimindex, word_to_bytes length
   =================================================================== *)

Theorem dimindex_256[local]:
  dimindex (:256) = 256
Proof
  rw[fcpTheory.index_bit0, fcpTheory.index_bit1, fcpTheory.index_one,
     fcpTheory.finite_bit0, fcpTheory.finite_bit1, fcpTheory.finite_one]
QED

Theorem len_word_to_bytes_256[local]:
  LENGTH (word_to_bytes (w:bytes32) be) = 32
Proof
  rw[byteTheory.LENGTH_word_to_bytes, dimindex_256]
QED

(* ===================================================================
   List splice lemma: replacing [a, a+n) doesn't affect [b, b+m)
   when ranges are disjoint. Used by both mstore and mstore8 proofs.
   =================================================================== *)

(* Case 1: read range entirely before write range *)
Theorem take_drop_splice_before[local]:
  !(l:'a list) a n mid b m.
    LENGTH mid = n /\ a + n <= LENGTH l /\ b + m <= a ==>
    TAKE m (DROP b (TAKE a l ++ mid ++ DROP (a + n) l)) =
    TAKE m (DROP b l)
Proof
  rw[rich_listTheory.TAKE_DROP_SWAP] >>
  `LENGTH (TAKE a l) = a` by (irule listTheory.LENGTH_TAKE >> fs[]) >>
  (* Re-associate: (TAKE a l ++ mid) ++ DROP ... => TAKE a l ++ (mid ++ DROP ...) *)
  `TAKE a l ++ mid ++ DROP (a + LENGTH mid) l =
   TAKE a l ++ (mid ++ DROP (a + LENGTH mid) l)` by
    rw[GSYM listTheory.APPEND_ASSOC] >>
  ASM_REWRITE_TAC[] >>
  (* Now TAKE (b+m) (TAKE a l ++ ...) = TAKE (b+m) (TAKE a l) since b+m <= a *)
  `TAKE (b + m) (TAKE a l ++ (mid ++ DROP (a + LENGTH mid) l)) =
   TAKE (b + m) (TAKE a l)` by
    (irule rich_listTheory.TAKE_APPEND1 >> fs[]) >>
  ASM_REWRITE_TAC[] >>
  (* TAKE (b+m) (TAKE a l) = TAKE (b+m) l since b+m <= a *)
  `TAKE (b + m) (TAKE a l) = TAKE (b + m) l` by
    (irule rich_listTheory.TAKE_TAKE_T >> fs[]) >>
  ASM_REWRITE_TAC[]
QED

(* Case 2: read range entirely after write range *)
Theorem take_drop_splice_after[local]:
  !(l:'a list) a n mid b m.
    LENGTH mid = n /\ a + n <= LENGTH l /\ a + n <= b ==>
    TAKE m (DROP b (TAKE a l ++ mid ++ DROP (a + n) l)) =
    TAKE m (DROP b l)
Proof
  rw[] >>
  (* DROP b skips past (TAKE a l ++ mid), landing in DROP (a+n) l *)
  `LENGTH (TAKE a l ++ mid) = a + LENGTH mid` by
    (rw[LENGTH_APPEND] >> irule LENGTH_TAKE >> fs[]) >>
  `DROP b (TAKE a l ++ mid ++ DROP (a + LENGTH mid) l) =
   DROP (b - (a + LENGTH mid)) (DROP (a + LENGTH mid) l)` by
    (`b - LENGTH (TAKE a l ++ mid) = b - (a + LENGTH mid)` by fs[] >>
     metis_tac[DROP_APPEND2]) >>
  ASM_REWRITE_TAC[] >>
  rw[rich_listTheory.DROP_DROP_T]
QED

(* Combined: disjoint ranges *)
Theorem take_drop_splice_disjoint[local]:
  !(l:'a list) a n mid b m.
    LENGTH mid = n /\ a + n <= LENGTH l /\
    (b + m <= a \/ a + n <= b) ==>
    TAKE m (DROP b (TAKE a l ++ mid ++ DROP (a + n) l)) =
    TAKE m (DROP b l)
Proof
  rw[] >> metis_tac[take_drop_splice_before, take_drop_splice_after]
QED

(* ===================================================================
   Padding lemma: if off + 32 <= LENGTH l, padding is irrelevant
   =================================================================== *)

Theorem take_drop_no_pad[local]:
  !(l : word8 list) off.
    off + 32 <= LENGTH l ==>
    TAKE 32 (DROP off l ++ REPLICATE 32 0w) = TAKE 32 (DROP off l)
Proof
  rw[] >>
  `LENGTH (DROP off l) = LENGTH l - off` by rw[listTheory.LENGTH_DROP] >>
  `32 <= LENGTH (DROP off l)` by fs[] >>
  irule rich_listTheory.TAKE_APPEND1 >> fs[]
QED

(* Padding-length-insensitive TAKE: only the payload matters, not how much padding *)
Theorem take_append_pad[local]:
  !n (l:'a list) a b x.
    n <= LENGTH l + a /\ n <= LENGTH l + b ==>
    TAKE n (l ++ REPLICATE a x) = TAKE n (l ++ REPLICATE b x)
Proof
  rw[LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_APPEND, LENGTH_REPLICATE] >>
  rw[EL_TAKE, EL_APPEND_EQN, EL_REPLICATE, LENGTH_REPLICATE]
QED

(* DROP distributes over APPEND with REPLICATE tail *)
(* Combined: TAKE n (DROP m (l ++ pad) ++ more_pad) = TAKE n (DROP m l ++ combined_pad) *)
Theorem take_drop_pad_irrelevant[local]:
  !off (mem : word8 list) k.
    off <= LENGTH mem ==>
    TAKE 32 (DROP off (mem ++ REPLICATE k 0w) ++ REPLICATE 32 0w) =
    TAKE 32 (DROP off mem ++ REPLICATE 32 0w)
Proof
  rw[] >>
  `DROP off (mem ++ REPLICATE k 0w) = DROP off mem ++ REPLICATE k 0w` by
    rw[DROP_APPEND1] >>
  rw[] >>
  `DROP off mem ++ REPLICATE k 0w ++ REPLICATE 32 0w =
   DROP off mem ++ REPLICATE (k + 32) (0w:word8)` by
    rw[GSYM APPEND_ASSOC, GSYM rich_listTheory.REPLICATE_APPEND] >>
  ASM_REWRITE_TAC[] >>
  irule take_append_pad >>
  rw[LENGTH_DROP, LENGTH_REPLICATE]
QED

(* When off >= LENGTH mem, padding doesn't matter for reads *)
Theorem take_drop_pad_beyond[local]:
  !off (mem : word8 list) k.
    LENGTH mem <= off ==>
    TAKE 32 (DROP off (mem ++ REPLICATE k 0w) ++ REPLICATE 32 0w) =
    TAKE 32 (DROP off mem ++ REPLICATE 32 0w)
Proof
  rw[] >>
  `DROP off mem = []` by rw[DROP_LENGTH_TOO_LONG] >> rw[] >>
  (* Both sides = REPLICATE 32 0w; prove via LIST_EQ_REWRITE *)
  rw[LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_APPEND,
     LENGTH_DROP, LENGTH_REPLICATE, EL_TAKE,
     EL_APPEND_EQN, EL_REPLICATE, EL_DROP]
QED

(* Combining both padding cases *)
Theorem take_drop_pad_combined[local]:
  !off (mem : word8 list) k.
    TAKE 32 (DROP off (mem ++ REPLICATE k 0w) ++ REPLICATE 32 0w) =
    TAKE 32 (DROP off mem ++ REPLICATE 32 0w)
Proof
  rw[] >> Cases_on `off <= LENGTH mem`
  >- rw[take_drop_pad_irrelevant]
  >- (`LENGTH mem <= off` by fs[] >> rw[take_drop_pad_beyond])
QED

(* If TAKE agrees, then TAKE-with-padding also agrees *)
Theorem take_cong_append[local]:
  !m (x:'a list) y pad.
    TAKE m x = TAKE m y ==>
    TAKE m (x ++ pad) = TAKE m (y ++ pad)
Proof
  Induct >- rw[] >>
  Cases_on `x` >> Cases_on `y` >> rw[]
QED

(* ===================================================================
   Memory disjointness: mload after mstore on disjoint regions
   =================================================================== *)

Theorem mload_mstore_disjoint_proof:
  !off1 off2 val s.
    regions_disjoint (off1, 32) (off2, 32) ==>
    mload off2 (mstore off1 val s) = mload off2 s
Proof
  rpt strip_tac >>
  fs[mload_def, mstore_def, LET_THM, regions_disjoint_def] >>
  qabbrev_tac `mem = s.vs_memory` >>
  qabbrev_tac `expanded = if off1 + 32 > LENGTH mem
    then mem ++ REPLICATE (off1 + 32 - LENGTH mem) 0w else mem` >>
  `LENGTH (word_to_bytes val T) = 32` by rw[len_word_to_bytes_256] >>
  `off1 + 32 <= LENGTH expanded` by
    (rw[Abbr `expanded`] >> rw[LENGTH_APPEND, LENGTH_REPLICATE] >> fs[]) >>
  (* Splice lemma on the inner TAKE/DROP. *)
  `TAKE 32 (DROP off2 (TAKE off1 expanded ++ word_to_bytes val T ++
     DROP (off1 + 32) expanded)) = TAKE 32 (DROP off2 expanded)` by
    (irule take_drop_splice_disjoint >> rw[]) >>
  (* Lift to the padded version via take_cong_append. *)
  `TAKE 32 (DROP off2 (TAKE off1 expanded ++ word_to_bytes val T ++
     DROP (off1 + 32) expanded) ++ REPLICATE 32 0w) =
   TAKE 32 (DROP off2 expanded ++ REPLICATE 32 0w)` by
    (irule take_cong_append >> rw[]) >>
  (* Padding irrelevance. *)
  `TAKE 32 (DROP off2 expanded ++ REPLICATE 32 0w) =
   TAKE 32 (DROP off2 mem ++ REPLICATE 32 0w)` by
    (rw[Abbr `expanded`] >> rw[take_drop_pad_combined]) >>
  ASM_REWRITE_TAC[]
QED

Theorem mload_mstore8_disjoint_proof:
  !off1 off2 val s.
    regions_disjoint (off1, 1) (off2, 32) ==>
    mload off2 (mstore8 off1 val s) = mload off2 s
Proof
  rpt strip_tac >>
  fs[mload_def, mstore8_def, LET_THM, regions_disjoint_def] >>
  qabbrev_tac `mem = s.vs_memory` >>
  qabbrev_tac `expanded = if off1 + 1 > LENGTH mem
    then mem ++ REPLICATE (off1 + 1 - LENGTH mem) 0w else mem` >>
  `LENGTH [w2w val : word8] = 1` by rw[] >>
  `off1 + 1 <= LENGTH expanded` by
    (rw[Abbr `expanded`] >> rw[LENGTH_APPEND, LENGTH_REPLICATE] >> fs[]) >>
  `TAKE 32 (DROP off2 (TAKE off1 expanded ++ [w2w val] ++
     DROP (off1 + 1) expanded)) = TAKE 32 (DROP off2 expanded)` by
    (irule take_drop_splice_disjoint >> rw[]) >>
  `TAKE 32 (DROP off2 (TAKE off1 expanded ++ [w2w val] ++
     DROP (off1 + 1) expanded) ++ REPLICATE 32 0w) =
   TAKE 32 (DROP off2 expanded ++ REPLICATE 32 0w)` by
    (irule take_cong_append >> rw[]) >>
  `TAKE 32 (DROP off2 expanded ++ REPLICATE 32 0w) =
   TAKE 32 (DROP off2 mem ++ REPLICATE 32 0w)` by
    (rw[Abbr `expanded`] >> rw[take_drop_pad_combined]) >>
  ASM_REWRITE_TAC[]
QED

(* ===================================================================
   allocas_non_overlapping + alloca_next_valid preservation
   =================================================================== *)

(* Combined alloca invariant: non-overlapping + bump pointer valid *)
(* vs_alloca_next >= base + sz for any existing alloca (conditional) *)
Theorem alloca_next_ge[local]:
  !s aid base sz.
    alloca_next_valid s /\
    FLOOKUP s.vs_allocas aid = SOME (base, sz) ==>
    base + sz <= s.vs_alloca_next
Proof
  rw[alloca_next_valid_def] >>
  res_tac >> fs[]
QED

(* exec_alloca preserves alloca_inv *)
Theorem exec_alloca_preserves_inv[local]:
  !inst s s' alloc_size.
    exec_alloca inst s alloc_size = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rw[exec_alloca_def, LET_THM] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> gvs[]
  >- ((* NONE — fresh allocation *)
      fs[alloca_inv_def, allocas_non_overlapping_def,
         alloca_next_valid_def, update_var_def] >>
      rpt strip_tac >> gvs[FLOOKUP_UPDATE] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
      res_tac >> fs[])
  >- ((* SOME — already allocated, state unchanged except var *)
      Cases_on `x` >> gvs[update_var_def, alloca_inv_def,
        allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[])
QED

(* exec_alloca: vs_alloca_next monotone *)
Theorem exec_alloca_next_mono[local]:
  !inst s s' alloc_size.
    exec_alloca inst s alloc_size = OK s' ==>
    s.vs_alloca_next <= s'.vs_alloca_next
Proof
  rw[exec_alloca_def, LET_THM, update_var_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> gvs[] >>
  TRY (Cases_on `x` >> gvs[]) >>
  simp[]
QED

Triviality exec_ext_call_preserves_alloca_fields[local]:
  !inst s s' gas addr value ao asz ro rs is_static.
    exec_ext_call inst s gas addr value ao asz ro rs is_static = OK s' ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rw[exec_ext_call_def, extract_venom_result_def, update_var_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])))
QED

Triviality exec_delegatecall_preserves_alloca_fields[local]:
  !inst s s' gas addr ao asz ro rs.
    exec_delegatecall inst s gas addr ao asz ro rs = OK s' ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rw[exec_delegatecall_def, extract_venom_result_def, update_var_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])))
QED

Triviality exec_create_preserves_alloca_fields[local]:
  !inst s s' value offset sz salt.
    exec_create inst s value offset sz salt = OK s' ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rw[exec_create_def, extract_venom_result_def, update_var_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])))
QED

Triviality exec_pure1_result_alloca_fields[local]:
  !f inst (s:venom_state) r.
    exec_pure1 f inst s = r ==>
    case r of
      OK s' => s'.vs_allocas = s.vs_allocas /\
               s'.vs_alloca_next = s.vs_alloca_next
    | Halt s' => s'.vs_allocas = s.vs_allocas /\
                 s'.vs_alloca_next = s.vs_alloca_next
    | Abort a s' => s'.vs_allocas = s.vs_allocas /\
                    s'.vs_alloca_next = s.vs_alloca_next
    | IntRet v s' => s'.vs_allocas = s.vs_allocas /\
                     s'.vs_alloca_next = s.vs_alloca_next
    | Error e => T
Proof
  rpt gen_tac >> Cases_on `r` >>
  rw[exec_pure1_def, update_var_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_pure2_result_alloca_fields[local]:
  !f inst (s:venom_state) r.
    exec_pure2 f inst s = r ==>
    case r of
      OK s' => s'.vs_allocas = s.vs_allocas /\
               s'.vs_alloca_next = s.vs_alloca_next
    | Halt s' => s'.vs_allocas = s.vs_allocas /\
                 s'.vs_alloca_next = s.vs_alloca_next
    | Abort a s' => s'.vs_allocas = s.vs_allocas /\
                    s'.vs_alloca_next = s.vs_alloca_next
    | IntRet v s' => s'.vs_allocas = s.vs_allocas /\
                     s'.vs_alloca_next = s.vs_alloca_next
    | Error e => T
Proof
  rpt gen_tac >> Cases_on `r` >>
  rw[exec_pure2_def, update_var_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_pure3_result_alloca_fields[local]:
  !f inst (s:venom_state) r.
    exec_pure3 f inst s = r ==>
    case r of
      OK s' => s'.vs_allocas = s.vs_allocas /\
               s'.vs_alloca_next = s.vs_alloca_next
    | Halt s' => s'.vs_allocas = s.vs_allocas /\
                 s'.vs_alloca_next = s.vs_alloca_next
    | Abort a s' => s'.vs_allocas = s.vs_allocas /\
                    s'.vs_alloca_next = s.vs_alloca_next
    | IntRet v s' => s'.vs_allocas = s.vs_allocas /\
                     s'.vs_alloca_next = s.vs_alloca_next
    | Error e => T
Proof
  rpt gen_tac >> Cases_on `r` >>
  rw[exec_pure3_def, update_var_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_read0_result_alloca_fields[local]:
  !f inst (s:venom_state) r.
    exec_read0 f inst s = r ==>
    case r of
      OK s' => s'.vs_allocas = s.vs_allocas /\
               s'.vs_alloca_next = s.vs_alloca_next
    | Halt s' => s'.vs_allocas = s.vs_allocas /\
                 s'.vs_alloca_next = s.vs_alloca_next
    | Abort a s' => s'.vs_allocas = s.vs_allocas /\
                    s'.vs_alloca_next = s.vs_alloca_next
    | IntRet v s' => s'.vs_allocas = s.vs_allocas /\
                     s'.vs_alloca_next = s.vs_alloca_next
    | Error e => T
Proof
  rpt gen_tac >> Cases_on `r` >>
  rw[exec_read0_def, update_var_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_read1_result_alloca_fields[local]:
  !f inst (s:venom_state) r.
    exec_read1 f inst s = r ==>
    case r of
      OK s' => s'.vs_allocas = s.vs_allocas /\
               s'.vs_alloca_next = s.vs_alloca_next
    | Halt s' => s'.vs_allocas = s.vs_allocas /\
                 s'.vs_alloca_next = s.vs_alloca_next
    | Abort a s' => s'.vs_allocas = s.vs_allocas /\
                    s'.vs_alloca_next = s.vs_alloca_next
    | IntRet v s' => s'.vs_allocas = s.vs_allocas /\
                     s'.vs_alloca_next = s.vs_alloca_next
    | Error e => T
Proof
  rpt gen_tac >> Cases_on `r` >>
  rw[exec_read1_def, update_var_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_pure1_not_terminal[local,simp]:
  (!f inst (s:venom_state) s'. exec_pure1 f inst s <> Halt s') /\
  (!f inst (s:venom_state) a s'. exec_pure1 f inst s <> Abort a s') /\
  (!f inst (s:venom_state) v s'. exec_pure1 f inst s <> IntRet v s')
Proof
  rw[exec_pure1_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_pure2_not_terminal[local,simp]:
  (!f inst (s:venom_state) s'. exec_pure2 f inst s <> Halt s') /\
  (!f inst (s:venom_state) a s'. exec_pure2 f inst s <> Abort a s') /\
  (!f inst (s:venom_state) v s'. exec_pure2 f inst s <> IntRet v s')
Proof
  rw[exec_pure2_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_pure3_not_terminal[local,simp]:
  (!f inst (s:venom_state) s'. exec_pure3 f inst s <> Halt s') /\
  (!f inst (s:venom_state) a s'. exec_pure3 f inst s <> Abort a s') /\
  (!f inst (s:venom_state) v s'. exec_pure3 f inst s <> IntRet v s')
Proof
  rw[exec_pure3_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_read0_not_terminal[local,simp]:
  (!f inst (s:venom_state) s'. exec_read0 f inst s <> Halt s') /\
  (!f inst (s:venom_state) a s'. exec_read0 f inst s <> Abort a s') /\
  (!f inst (s:venom_state) v s'. exec_read0 f inst s <> IntRet v s')
Proof
  rw[exec_read0_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_read1_not_terminal[local,simp]:
  (!f inst (s:venom_state) s'. exec_read1 f inst s <> Halt s') /\
  (!f inst (s:venom_state) a s'. exec_read1 f inst s <> Abort a s') /\
  (!f inst (s:venom_state) v s'. exec_read1 f inst s <> IntRet v s')
Proof
  rw[exec_read1_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_write2_not_terminal[local,simp]:
  (!f inst (s:venom_state) s'. exec_write2 f inst s <> Halt s') /\
  (!f inst (s:venom_state) a s'. exec_write2 f inst s <> Abort a s') /\
  (!f inst (s:venom_state) v s'. exec_write2 f inst s <> IntRet v s')
Proof
  rw[exec_write2_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_ext_call_not_terminal[local,simp]:
  (!inst (s:venom_state) gas addr value ao asz ro rs is_static s'.
     exec_ext_call inst s gas addr value ao asz ro rs is_static <> Halt s') /\
  (!inst (s:venom_state) gas addr value ao asz ro rs is_static a s'.
     exec_ext_call inst s gas addr value ao asz ro rs is_static <> Abort a s') /\
  (!inst (s:venom_state) gas addr value ao asz ro rs is_static v s'.
     exec_ext_call inst s gas addr value ao asz ro rs is_static <> IntRet v s')
Proof
  rw[exec_ext_call_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])))
QED

Triviality exec_delegatecall_not_terminal[local,simp]:
  (!inst (s:venom_state) gas addr ao asz ro rs s'.
     exec_delegatecall inst s gas addr ao asz ro rs <> Halt s') /\
  (!inst (s:venom_state) gas addr ao asz ro rs a s'.
     exec_delegatecall inst s gas addr ao asz ro rs <> Abort a s') /\
  (!inst (s:venom_state) gas addr ao asz ro rs v s'.
     exec_delegatecall inst s gas addr ao asz ro rs <> IntRet v s')
Proof
  rw[exec_delegatecall_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])))
QED

Triviality exec_create_not_terminal[local,simp]:
  (!inst (s:venom_state) value offset sz salt s'.
     exec_create inst s value offset sz salt <> Halt s') /\
  (!inst (s:venom_state) value offset sz salt a s'.
     exec_create inst s value offset sz salt <> Abort a s') /\
  (!inst (s:venom_state) value offset sz salt v s'.
     exec_create inst s value offset sz salt <> IntRet v s')
Proof
  rw[exec_create_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[])))
QED

Triviality exec_alloca_not_terminal[local,simp]:
  (!inst (s:venom_state) alloc_size s'.
     exec_alloca inst s alloc_size <> Halt s') /\
  (!inst (s:venom_state) alloc_size a s'.
     exec_alloca inst s alloc_size <> Abort a s') /\
  (!inst (s:venom_state) alloc_size v s'.
     exec_alloca inst s alloc_size <> IntRet v s')
Proof
  rw[exec_alloca_def] >> gvs[AllCaseEqs()]
QED

val alloca_field_solve_tac =
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
      write_memory_with_expansion_def, mcopy_def,
      revert_state_def, eval_operands_def, jump_to_def,
      lookup_var_def, FLOOKUP_UPDATE, halt_state_def, set_returndata_def];

val effect_free_alloca_tac =
  fs[step_inst_base_def] >>
  FIRST [
    drule exec_pure1_result_alloca_fields >> simp[],
    drule exec_pure2_result_alloca_fields >> simp[],
    drule exec_pure3_result_alloca_fields >> simp[],
    drule exec_read0_result_alloca_fields >> simp[],
    drule exec_read1_result_alloca_fields >> simp[],
    alloca_field_solve_tac
  ];

val alloca_field_finish_tac =
  FIRST [
    qpat_x_assum `(_ \/ _ \/ _ \/ _) /\ _` mp_tac,
    qpat_x_assum `step_inst_base inst s = _` mp_tac
  ] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >>
  FIRST [
    rw[exec_pure1_def] >> alloca_field_solve_tac >> NO_TAC,
    rw[exec_pure2_def] >> alloca_field_solve_tac >> NO_TAC,
    rw[exec_pure3_def] >> alloca_field_solve_tac >> NO_TAC,
    rw[exec_read0_def] >> alloca_field_solve_tac >> NO_TAC,
    rw[exec_read1_def] >> alloca_field_solve_tac >> NO_TAC,
    rw[exec_write2_def] >> alloca_field_solve_tac >> NO_TAC,
    rw[] >>
      imp_res_tac exec_ext_call_preserves_alloca_fields >>
      imp_res_tac exec_delegatecall_preserves_alloca_fields >>
      imp_res_tac exec_create_preserves_alloca_fields >>
      alloca_field_solve_tac >> NO_TAC
  ];

val effect_free_not_terminal_tac =
  rpt strip_tac >>
  gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >>
  simp[exec_pure1_not_terminal, exec_pure2_not_terminal,
       exec_pure3_not_terminal, exec_read0_not_terminal,
       exec_read1_not_terminal] >>
  BasicProvers.every_case_tac >>
  simp[exec_pure1_not_terminal, exec_pure2_not_terminal,
       exec_pure3_not_terminal, exec_read0_not_terminal,
       exec_read1_not_terminal];

Triviality effect_free_pure1_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = ISZERO \/ inst.inst_opcode = NOT) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  effect_free_not_terminal_tac
QED

Triviality effect_free_pure2_arith_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
     inst.inst_opcode = MUL \/ inst.inst_opcode = Div \/
     inst.inst_opcode = SDIV \/ inst.inst_opcode = Mod \/
     inst.inst_opcode = SMOD \/ inst.inst_opcode = Exp) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  effect_free_not_terminal_tac
QED

Triviality effect_free_pure2_cmp_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/
     inst.inst_opcode = GT \/ inst.inst_opcode = SLT \/
     inst.inst_opcode = SGT) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  effect_free_not_terminal_tac
QED

Triviality effect_free_pure2_bits_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = AND \/ inst.inst_opcode = OR \/
     inst.inst_opcode = XOR \/ inst.inst_opcode = SHL \/
     inst.inst_opcode = SHR \/ inst.inst_opcode = SAR \/
     inst.inst_opcode = SIGNEXTEND \/ inst.inst_opcode = BYTE \/
     inst.inst_opcode = OFFSET) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  effect_free_not_terminal_tac
QED

Triviality effect_free_pure3_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = ADDMOD \/ inst.inst_opcode = MULMOD) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  effect_free_not_terminal_tac
QED

Triviality effect_free_read0_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = CALLER \/ inst.inst_opcode = ADDRESS \/
     inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS \/
     inst.inst_opcode = ORIGIN \/ inst.inst_opcode = GASPRICE \/
     inst.inst_opcode = CHAINID \/ inst.inst_opcode = COINBASE \/
     inst.inst_opcode = TIMESTAMP \/ inst.inst_opcode = NUMBER \/
     inst.inst_opcode = PREVRANDAO \/ inst.inst_opcode = GASLIMIT \/
     inst.inst_opcode = BASEFEE \/ inst.inst_opcode = BLOBBASEFEE \/
     inst.inst_opcode = SELFBALANCE \/ inst.inst_opcode = CALLDATASIZE \/
     inst.inst_opcode = RETURNDATASIZE \/ inst.inst_opcode = MEMTOP \/
     inst.inst_opcode = CODESIZE) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  effect_free_not_terminal_tac
QED

Triviality effect_free_read1_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = MLOAD \/ inst.inst_opcode = SLOAD \/
     inst.inst_opcode = TLOAD \/ inst.inst_opcode = ILOAD \/
     inst.inst_opcode = DLOAD \/ inst.inst_opcode = BLOCKHASH \/
     inst.inst_opcode = BLOBHASH \/ inst.inst_opcode = BALANCE \/
     inst.inst_opcode = CALLDATALOAD \/
     inst.inst_opcode = EXTCODESIZE \/
     inst.inst_opcode = EXTCODEHASH) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  effect_free_not_terminal_tac
QED

Triviality effect_free_direct_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = SHA3 \/ inst.inst_opcode = PHI \/
     inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PARAM \/
     inst.inst_opcode = NOP) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def]
  >- simp[AllCaseEqs()]
  >- simp[AllCaseEqs()]
  >- simp[AllCaseEqs()]
  >- simp[AllCaseEqs()]
  >- simp[AllCaseEqs()]
QED

Triviality effect_free_fmp_not_terminal[local]:
  !inst (s:venom_state).
    (inst.inst_opcode = FMP_PARAM \/ inst.inst_opcode = RETPC_PARAM \/
     inst.inst_opcode = GETFMP \/ inst.inst_opcode = INITIAL_FMP \/
     inst.inst_opcode = BUMP) ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def]
  >- simp[AllCaseEqs()]
  >- simp[AllCaseEqs()]
  >- simp[AllCaseEqs()]
  >- simp[AllCaseEqs()]
  >- simp[AllCaseEqs()]
QED

Triviality effect_free_opcode_cases[local]:
  !op. is_effect_free_op op ==>
    (op = ISZERO \/ op = NOT) \/
    (op = ADD \/ op = SUB \/ op = MUL \/ op = Div \/
     op = SDIV \/ op = Mod \/ op = SMOD \/ op = Exp) \/
    (op = EQ \/ op = LT \/ op = GT \/ op = SLT \/ op = SGT) \/
    (op = AND \/ op = OR \/ op = XOR \/ op = SHL \/
     op = SHR \/ op = SAR \/ op = SIGNEXTEND \/ op = BYTE \/
     op = OFFSET) \/
    (op = ADDMOD \/ op = MULMOD) \/
    (op = CALLER \/ op = ADDRESS \/ op = CALLVALUE \/ op = GAS \/
     op = ORIGIN \/ op = GASPRICE \/ op = CHAINID \/
     op = COINBASE \/ op = TIMESTAMP \/ op = NUMBER \/
     op = PREVRANDAO \/ op = GASLIMIT \/ op = BASEFEE \/
     op = BLOBBASEFEE \/ op = SELFBALANCE \/ op = CALLDATASIZE \/
     op = RETURNDATASIZE \/ op = MEMTOP \/ op = CODESIZE) \/
    (op = MLOAD \/ op = SLOAD \/ op = TLOAD \/ op = ILOAD \/
     op = DLOAD \/ op = BLOCKHASH \/ op = BLOBHASH \/ op = BALANCE \/
     op = CALLDATALOAD \/ op = EXTCODESIZE \/ op = EXTCODEHASH) \/
    (op = SHA3 \/ op = PHI \/ op = ASSIGN \/ op = PARAM \/ op = NOP) \/
    (op = FMP_PARAM \/ op = RETPC_PARAM \/ op = GETFMP \/
     op = INITIAL_FMP \/ op = BUMP)
Proof
  Cases >> EVAL_TAC
QED

Triviality effect_free_step_not_terminal[local]:
  !inst (s:venom_state).
    is_effect_free_op inst.inst_opcode ==>
    (!s'. step_inst_base inst s <> Halt s') /\
    (!a s'. step_inst_base inst s <> Abort a s') /\
    (!v s'. step_inst_base inst s <> IntRet v s')
Proof
  rpt strip_tac >>
  drule_all effect_free_opcode_cases >> strip_tac >>
  FIRST [
    qspecl_then [`inst`, `s`] mp_tac effect_free_pure1_not_terminal >> gvs[] >> NO_TAC,
    qspecl_then [`inst`, `s`] mp_tac effect_free_pure2_arith_not_terminal >> gvs[] >> NO_TAC,
    qspecl_then [`inst`, `s`] mp_tac effect_free_pure2_cmp_not_terminal >> gvs[] >> NO_TAC,
    qspecl_then [`inst`, `s`] mp_tac effect_free_pure2_bits_not_terminal >> gvs[] >> NO_TAC,
    qspecl_then [`inst`, `s`] mp_tac effect_free_pure3_not_terminal >> gvs[] >> NO_TAC,
    qspecl_then [`inst`, `s`] mp_tac effect_free_read0_not_terminal >> gvs[] >> NO_TAC,
    qspecl_then [`inst`, `s`] mp_tac effect_free_read1_not_terminal >> gvs[] >> NO_TAC,
    qspecl_then [`inst`, `s`] mp_tac effect_free_direct_not_terminal >> gvs[] >> NO_TAC,
    qspecl_then [`inst`, `s`] mp_tac effect_free_fmp_not_terminal >> gvs[] >> NO_TAC
  ]
QED

Triviality pack_dret_dynamic_preserves_alloca_fields[local]:
  !pairs cursor (s:venom_state) ptrs final_cursor s'.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,s') ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Once pack_dret_dynamic_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[]
QED

Triviality opcode_alloca_field_class[local]:
  !op. op <> INVOKE /\ op <> ALLOCA ==>
    is_effect_free_op op \/
    is_mem_write_op op \/
    is_ext_call_op op \/
    op = SSTORE \/ op = TSTORE \/ op = ISTORE \/ op = LOG \/
    op = ASSERT \/ op = ASSERT_UNREACHABLE \/
    op = DALLOCA \/ op = SETFMP \/ is_terminator op
Proof
  Cases >> EVAL_TAC
QED

Triviality step_inst_base_effect_free_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    is_effect_free_op inst.inst_opcode ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac
        venomInstProofsTheory.step_inst_base_effect_free_state_equiv >>
      simp[] >> rw[state_equiv_def, execution_equiv_def])
  >- (qspecl_then [`inst`, `s`] mp_tac effect_free_step_not_terminal >> gvs[])
  >- (qspecl_then [`inst`, `s`] mp_tac effect_free_step_not_terminal >> gvs[])
  >- (qspecl_then [`inst`, `s`] mp_tac effect_free_step_not_terminal >> gvs[])
QED

Triviality step_inst_base_fmp_write_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/ step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    (inst.inst_opcode = DALLOCA \/ inst.inst_opcode = SETFMP) ==>
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> alloca_field_finish_tac
QED

Triviality step_inst_base_mem_write_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    is_mem_write_op inst.inst_opcode ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> DISCH_TAC >>
  Cases_on `inst.inst_opcode` >> gvs[is_mem_write_op_def] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >>
  strip_tac >>
  fs[exec_write2_def] >>
  gvs[AllCaseEqs()] >>
  fs[mstore_def, mstore8_def, mcopy_def, write_memory_with_expansion_def,
     lookup_var_def, update_var_def, contract_storage_def,
     halt_state_def, set_returndata_def] >>
  TRY (pairarg_tac >> gvs[] >>
       drule pack_dret_dynamic_preserves_alloca_fields >> simp[])
QED

Triviality step_inst_base_ext_call_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    is_ext_call_op inst.inst_opcode ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> DISCH_TAC >>
  Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >>
  simp[exec_ext_call_not_terminal, exec_delegatecall_not_terminal,
       exec_create_not_terminal] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  imp_res_tac exec_ext_call_preserves_alloca_fields >>
  imp_res_tac exec_delegatecall_preserves_alloca_fields >>
  imp_res_tac exec_create_preserves_alloca_fields >>
  gvs[]
QED

Triviality step_inst_base_sstore_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/ step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode = SSTORE ==>
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> alloca_field_finish_tac
QED

Triviality step_inst_base_tstore_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/ step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode = TSTORE ==>
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> alloca_field_finish_tac
QED

Triviality istore_preserves_alloca_fields[local,simp]:
  (istore offset value s).vs_allocas = s.vs_allocas /\
  (istore offset value s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[istore_def, mstore_def]
QED

Triviality step_inst_base_istore_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/ step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode = ISTORE ==>
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> alloca_field_finish_tac
QED

Triviality step_inst_base_log_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/ step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode = LOG ==>
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> alloca_field_finish_tac
QED

Triviality step_inst_base_assert_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/ step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode = ASSERT ==>
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> alloca_field_finish_tac
QED

Triviality step_inst_base_assert_unreachable_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/ step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode = ASSERT_UNREACHABLE ==>
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> alloca_field_finish_tac
QED

Triviality step_inst_base_terminator_alloca_fields[local]:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/ step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    is_terminator inst.inst_opcode ==>
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> DISCH_TAC >>
  Cases_on `inst.inst_opcode = DRET`
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac
        step_inst_base_mem_write_alloca_fields >>
      impl_tac >- gvs[is_mem_write_op_def] >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >>
  simp[] >>
  strip_tac >>
  alloca_field_solve_tac
QED

(* Combined non-ALLOCA, non-INVOKE step_inst_base alloca-field preservation. *)
Theorem step_inst_base_preserves_alloca_fields:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> DISCH_TAC >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `inst.inst_opcode <> ALLOCA` by gvs[] >>
  drule_all opcode_alloca_field_class >> strip_tac
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_effect_free_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_mem_write_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_ext_call_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_sstore_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_tstore_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_istore_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_log_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_assert_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_assert_unreachable_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_fmp_write_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_fmp_write_alloca_fields >> impl_tac >- gvs[] >> gvs[])
  >- (qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_terminator_alloca_fields >> impl_tac >- gvs[] >> gvs[])
QED

Theorem step_inst_base_preserves_allocas:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_preserves_alloca_fields >>
  impl_tac >- gvs[] >> gvs[]
QED

Theorem step_inst_base_preserves_alloca_next:
  !inst (s:venom_state) s'.
    (step_inst_base inst s = OK s' \/
     step_inst_base inst s = Halt s' \/
     (?a. step_inst_base inst s = Abort a s') \/
     (?v. step_inst_base inst s = IntRet v s')) /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA ==>
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_preserves_alloca_fields >>
  impl_tac >- gvs[] >> gvs[]
QED

(* Result predicate: alloca_inv + monotonicity *)
Definition result_alloca_inv_def:
  result_alloca_inv n0 (OK s') =
    (alloca_inv s' /\ n0 <= s'.vs_alloca_next) /\
  result_alloca_inv n0 (IntRet vals s') =
    (alloca_inv s' /\ n0 <= s'.vs_alloca_next) /\
  result_alloca_inv n0 (Halt s') =
    (alloca_inv s' /\ n0 <= s'.vs_alloca_next) /\
  result_alloca_inv n0 (Abort a s') =
    (alloca_inv s' /\ n0 <= s'.vs_alloca_next) /\
  result_alloca_inv n0 (Error e) = T   (* Error carries no state, invariant vacuous *)
End

(* exec_alloca lifted to result *)
Theorem exec_alloca_result_inv[local]:
  !inst (s:venom_state) alloc_size.
    alloca_inv s ==>
    result_alloca_inv s.vs_alloca_next (exec_alloca inst s alloc_size)
Proof
  rw[exec_alloca_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[result_alloca_inv_def]
  >- ((* NONE — fresh allocation *)
      `exec_alloca inst s alloc_size =
         OK (update_var h (n2w s.vs_alloca_next)
           (s with <| vs_allocas :=
              s.vs_allocas |+ (inst.inst_id, (s.vs_alloca_next, w2n alloc_size));
              vs_alloca_next := s.vs_alloca_next + w2n alloc_size |>))` by
        simp[exec_alloca_def] >>
      metis_tac[exec_alloca_preserves_inv, exec_alloca_next_mono])
  >- ((* SOME — idempotent *)
      `exec_alloca inst s alloc_size = OK (update_var h (n2w q) s)` by
        simp[exec_alloca_def] >>
      metis_tac[exec_alloca_preserves_inv, exec_alloca_next_mono])
QED

(* FOLDL of update_var preserves vs_allocas and vs_alloca_next *)
Theorem foldl_update_var_alloca_fields[local]:
  !kvs base.
    (FOLDL (\s' (k,v). update_var k v s') base kvs).vs_allocas =
      base.vs_allocas /\
    (FOLDL (\s' (k,v). update_var k v s') base kvs).vs_alloca_next =
      base.vs_alloca_next
Proof
  Induct >> rw[] >> Cases_on `h` >> rw[update_var_def]
QED

Theorem setup_callee_inv[local]:
  !fn args s s'.
    setup_callee fn args s = SOME s' ==>
    alloca_inv s' /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rw[setup_callee_def, alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[FLOOKUP_DEF]
QED

Theorem merge_callee_inv[local]:
  !caller callee.
    alloca_inv caller /\
    caller.vs_alloca_next <= callee.vs_alloca_next ==>
    alloca_inv (merge_callee_state caller callee)
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def, merge_callee_state_def] >>
  res_tac >> fs[]
QED

Theorem foldl_update_var_inv[local]:
  !kvs base.
    alloca_inv base ==>
    alloca_inv (FOLDL (\s' (k,v). update_var k v s') base kvs)
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  gvs[foldl_update_var_alloca_fields] >> metis_tac[]
QED

Theorem alloca_fields_eq_inv[local]:
  !s s'.
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem adopt_return_fmp_alloca_inv[local]:
  !ir s. alloca_inv s ==> alloca_inv (adopt_return_fmp ir s)
Proof
  rpt strip_tac >> Cases_on `ir.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, alloca_inv_def,
      allocas_non_overlapping_def, alloca_next_valid_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem result_alloca_inv_mono[local]:
  !n0 n1 r. n0 <= n1 /\ result_alloca_inv n1 r ==> result_alloca_inv n0 r
Proof
  rpt gen_tac >> Cases_on `r` >> rw[result_alloca_inv_def]
QED

(* Setting vs_inst_idx preserves alloca_inv *)
Theorem alloca_inv_set_inst_idx[local]:
  !s n. alloca_inv s ==> alloca_inv (s with vs_inst_idx := n)
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

(* Joint induction: step_inst/exec_block/run_blocks preserve alloca_inv *)
Theorem alloca_inv_joint[local]:
  (!fuel ctx inst s.
     alloca_inv s ==>
     result_alloca_inv s.vs_alloca_next (step_inst fuel ctx inst s)) /\
  (!fuel ctx bb s.
     alloca_inv s ==>
     result_alloca_inv s.vs_alloca_next (exec_block fuel ctx bb s)) /\
  (!fuel ctx fn s.
     alloca_inv s ==>
     result_alloca_inv s.vs_alloca_next (run_blocks fuel ctx fn s))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac >> rpt strip_tac
  >- (
    (* step_inst case *)
    Cases_on `inst.inst_opcode = INVOKE`
    >- (
      ONCE_REWRITE_TAC[step_inst_def] >> simp[] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[result_alloca_inv_def]) >>
      imp_res_tac setup_callee_inv >> gvs[] >>
      gvs[bind_outputs_def, AllCaseEqs()] >>
      conj_tac
      >- (irule foldl_update_var_inv >>
          irule adopt_return_fmp_alloca_inv >>
          irule merge_callee_inv >> gvs[])
      >- (Cases_on `i.iret_adopt_fmp` >>
          gvs[adopt_return_fmp_def, foldl_update_var_alloca_fields,
              merge_callee_state_def])
    )
    >> Cases_on `inst.inst_opcode = ALLOCA`
    >- (
      ONCE_REWRITE_TAC[step_inst_def] >> simp[step_inst_base_def] >>
      gvs[venomInstTheory.is_alloca_op_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[result_alloca_inv_def]) >>
      metis_tac[exec_alloca_result_inv]
    )
    >> (
      (`step_inst fuel ctx inst s = step_inst_base inst s` by
        (ONCE_REWRITE_TAC[step_inst_def] >> simp[])) >>
      Cases_on `step_inst_base inst s` >>
      gvs[result_alloca_inv_def] >>
      imp_res_tac step_inst_base_preserves_alloca_fields >>
      imp_res_tac alloca_fields_eq_inv >> gvs[]
    )
  )
  >- (
    (* exec_block case *)
    ONCE_REWRITE_TAC[exec_block_def] >> simp[] >>
    rpt (BasicProvers.TOP_CASE_TAC >> gvs[result_alloca_inv_def]) >>
    (* Remaining: recursive case, ¬is_terminator *)
    `alloca_inv (v with vs_inst_idx := SUC s.vs_inst_idx)` by
      (irule alloca_fields_eq_inv >> qexists_tac `v` >> simp[]) >>
    first_x_assum drule >> strip_tac >>
    irule result_alloca_inv_mono >>
    qexists_tac `v.vs_alloca_next` >> gvs[]
  )
  >- (
    (* run_blocks case *)
    ONCE_REWRITE_TAC[run_blocks_def] >> simp[] >>
    Cases_on `fuel` >> gvs[result_alloca_inv_def] >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[result_alloca_inv_def] >>
    mp_tac (Q.SPECL [`s`,`x.bb_instructions`] eval_phis_ok_or_error_defs) >>
    Cases_on `eval_phis s x.bb_instructions` >> gvs[exec_result_distinct] >>
    imp_res_tac eval_phis_preserves_alloca_fields >>
    imp_res_tac alloca_fields_eq_inv >>
    imp_res_tac alloca_inv_set_inst_idx >>
    Cases_on `run_block_non_phis n ctx x
      (v with vs_inst_idx := phi_prefix_length x.bb_instructions)` >>
    gvs[result_alloca_inv_def] >>
    Cases_on `v'.vs_halted` >> gvs[result_alloca_inv_def] >>
    irule result_alloca_inv_mono >>
    qexists_tac `v'.vs_alloca_next` >> simp[]
  )
QED

(* ===== Exported theorems ===== *)

Theorem allocas_non_overlapping_empty_proof:
  !s. s.vs_allocas = FEMPTY ==> allocas_non_overlapping s
Proof
  rw[allocas_non_overlapping_def, FLOOKUP_DEF]
QED

Theorem alloca_inv_empty_proof:
  !s. s.vs_allocas = FEMPTY ==> alloca_inv s
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def, FLOOKUP_DEF]
QED

Theorem alloca_inv_step_inst_proof:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  metis_tac[alloca_inv_joint, result_alloca_inv_def]
QED

Theorem alloca_inv_exec_block_proof:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  metis_tac[alloca_inv_joint, result_alloca_inv_def]
QED

Theorem alloca_inv_run_block_proof:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rw[run_block_def] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`s`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_distinct] >>
  imp_res_tac eval_phis_preserves_alloca_fields >>
  imp_res_tac alloca_fields_eq_inv >>
  imp_res_tac alloca_inv_set_inst_idx >>
  metis_tac[alloca_inv_exec_block_proof]
QED

Theorem alloca_inv_run_blocks_proof:
  !fuel ctx fn s s'.
    run_blocks fuel ctx fn s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  metis_tac[alloca_inv_joint, result_alloca_inv_def]
QED

Theorem alloca_inv_run_function_proof:
  !fuel ctx fn s s'.
    run_function fuel ctx fn s = OK s' /\
    alloca_inv s ==>
    alloca_inv s'
Proof
  rw[run_function_def] >> rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  `alloca_inv (s with <| vs_current_bb := x; vs_inst_idx := 0 |>)` by
    (irule alloca_fields_eq_inv >> qexists_tac `s` >> simp[]) >>
  metis_tac[alloca_inv_run_blocks_proof]
QED

(* Backward-compatible: allocas_non_overlapping preserved under alloca_inv *)
Theorem allocas_non_overlapping_step_inst_proof:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    alloca_inv s ==>
    allocas_non_overlapping s'
Proof
  metis_tac[alloca_inv_step_inst_proof, alloca_inv_def]
QED

Theorem allocas_non_overlapping_run_block_proof:
  !fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' /\
    alloca_inv s ==>
    allocas_non_overlapping s'
Proof
  metis_tac[alloca_inv_run_block_proof, alloca_inv_def]
QED

Theorem allocas_non_overlapping_exec_block_proof:
  ∀fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    allocas_non_overlapping s'
Proof
  metis_tac[alloca_inv_exec_block_proof, alloca_inv_def]
QED

Theorem did8[local] = EVAL``dimindex(:256) DIV 8``

Theorem mload_mstore_same_proof:
  ∀off val s.
    mload off (mstore off val s) = val
Proof
  simp[mload_def, mstore_def] >>
  rpt gen_tac >>
  rewrite_tac[TAKE_APPEND] >>
  rewrite_tac[DROP_APPEND, DROP_TAKE_EQ_NIL] >>
  simp_tac (std_ss ++ listSimps.LIST_ss)
    [LENGTH_word_to_bytes, LENGTH_TAKE_EQ] >>
  IF_CASES_TAC >- (
    simp_tac (std_ss ++ listSimps.LIST_ss)
      [did8,
       iterateTheory.ADD_SUBR2, TAKE_APPEND,
       LENGTH_word_to_bytes] >>
    simp[LENGTH_word_to_bytes, TAKE_LENGTH_TOO_LONG]) >>
  IF_CASES_TAC >- (
    simp_tac (std_ss ++ listSimps.LIST_ss)
      [LENGTH_REPLICATE, did8, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
    simp[iterateTheory.ADD_SUBR2, TAKE_APPEND,
         TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG] ) >>
  fs[]
QED

Theorem word_bytes_roundtrip_proof:
  ∀ (bytes : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bytes = dimindex(:α) DIV 8 ⇒
    word_to_bytes (word_of_bytes T (0w : α word) bytes) T = bytes
Proof
  rw[LIST_EQ_REWRITE, LENGTH_word_to_bytes]
  >> fs[]
  >> rw[word_to_bytes_def]
  >> simp[EL_word_to_bytes_aux]
  >> simp[get_byte_word_of_bytes_be]
  >> DEP_REWRITE_TAC[first_byte_at_0w]
  >> rw[DIV_LE_X, dimindex_lt_dimword]
QED

Theorem word_of_bytes_be_inj_proof:
  ∀ (bs1 : byte list) (bs2 : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bs1 = dimindex(:α) DIV 8 ∧
    LENGTH bs2 = dimindex(:α) DIV 8 ∧
    word_of_bytes T (0w : α word) bs1 = word_of_bytes T (0w : α word) bs2 ⇒
    bs1 = bs2
Proof
  rw[] >>
  `word_to_bytes (word_of_bytes T 0w bs1 : α word) T =
   word_to_bytes (word_of_bytes T 0w bs2 : α word) T` by simp[] >>
  metis_tac[word_bytes_roundtrip_proof]
QED

Theorem word_to_bytes_be_w2w_proof:
  ∀ (w : α word).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β)
    ⇒
    word_to_bytes (w2w w : β word) T =
    PAD_LEFT 0w (dimindex(:β) DIV 8) (word_to_bytes w T)
Proof
  rw[PAD_LEFT, GSYM REPLICATE_GENLIST] >>
  simp[word_to_bytes_be_def, word_to_bytes_def] >>
  simp[LIST_EQ_REWRITE, LENGTH_word_to_bytes_aux] >>
  rw[]
  >- (
    irule $ GSYM SUB_ADD >>
    gvs[DIV_LE_X, LEFT_ADD_DISTRIB, DIVIDES_DIV] ) >>
  simp[EL_word_to_bytes_aux, EL_APPEND,
       LENGTH_word_to_bytes_aux, EL_REPLICATE] >>
  IF_CASES_TAC >- (
    simp[word_eq_0, w2w, word_lsr_def, get_byte_def, byte_index_def] >>
    simp[fcpTheory.FCP_BETA] >>
    gen_tac >> strip_tac >>
    qmatch_goalsub_abbrev_tac`x MOD db MOD b8` >>
    disj2_tac >>
    qmatch_goalsub_abbrev_tac`w2w w ' ii` >>
    `b8 < dimindex(:'b)` by gvs[Abbr`b8`] >>
    `dimindex(:'b) < db` by gvs[dimindex_lt_dimword,Abbr`db`] >>
    `x < db` by gvs[] >> gvs[] >>
    gvs[LEFT_SUB_DISTRIB] >>
    `8 * b8 = dimindex(:'b)` by gvs[Abbr`b8`, DIVIDES_DIV] >>
    gvs[] >>
    `8 * (dimindex(:'a) DIV 8) ≤ dimindex(:'b)` by simp[DIVIDES_DIV] >>
    drule_at(Pos(el 2))DIV_SUB >>
    impl_tac >- rw[] >> simp[DIVIDES_DIV] >>
    strip_tac >> gvs[X_LT_DIV] >>
    `ii < dimindex(:'b)` by gvs[Abbr`ii`] >>
    simp[w2w] >> gvs[Abbr`ii`] ) >>
  `8 * (dimindex(:'a) DIV 8) ≤ dimindex(:'b)` by simp[DIVIDES_DIV] >>
  drule_at(Pos(el 2))DIV_SUB >>
  impl_tac >- rw[] >> simp[DIVIDES_DIV] >>
  disch_then (strip_assume_tac o SYM) >> gvs[X_LT_DIV] >>
  simp[get_byte_def] >>
  qmatch_goalsub_abbrev_tac`ba DIV 8` >>
  qmatch_asmsub_abbrev_tac`db - da = _`>>
  simp[byte_index_def] >>
  assume_tac(INST_TYPE[alpha|->beta]dimindex_lt_dimword) >>
  gvs[] >>
  `x < db` by gvs[Abbr`db`,X_LT_DIV] >> gvs[] >>
  qmatch_goalsub_abbrev_tac`xxx MOD dw MOD da` >>
  `da < dimindex(:'a)` by simp[Abbr`da`] >>
  `dimindex(:'a) < dimword(:'a)` by simp[dimindex_lt_dimword] >> gvs[] >>
  `xxx < dw` by gvs[Abbr`xxx`] >> gvs[] >>
  `xxx < da` by gvs[Abbr`xxx`,Abbr`da`,X_LT_DIV] >> gvs[] >>
  `db - (x + 1) = da - (xxx + 1)` by (
    gvs[Abbr`xxx`] >>
    rewrite_tac[SUB_PLUS] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    qspecl_then[`x`,`ba DIV 8`]mp_tac SUB_SUB >>
    impl_tac >- simp[DIV_LE_X] >> simp[] >> disch_then kall_tac >>
    AP_THM_TAC >> AP_TERM_TAC >>
    `da <= db` suffices_by gvs[] >>
    unabbrev_all_tac >>
    irule DIV_LE_MONOTONE >> rw[] ) >>
  gvs[] >>
  simp[GSYM WORD_EQ, word_bit_def, w2w, word_lsr_def, fcpTheory.FCP_BETA]
QED

Theorem w2w_word_of_bytes_be_pad_left_proof:
  ∀ (l : byte list).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β) ∧
    LENGTH l = dimindex(:α) DIV 8
    ⇒
    w2w (word_of_bytes_be l : α word) =
    (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word)
Proof
  rw[] >>
  `word_to_bytes (w2w (word_of_bytes_be l : α word) : β word) T =
   word_to_bytes (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word) T`
    suffices_by metis_tac[word_of_bytes_word_to_bytes] >>
  simp[GSYM word_to_bytes_be_def, GSYM word_of_bytes_be_def] >>
  DEP_REWRITE_TAC[word_to_bytes_be_w2w_proof] >> simp[] >>
  simp[word_to_bytes_be_def, word_of_bytes_be_def] >>
  DEP_REWRITE_TAC[word_bytes_roundtrip_proof] >>
  simp[bitstringTheory.length_pad_left, DIV_LE_MONOTONE] >>
  rw[] >> gvs[NOT_LESS]
  >- (qspec_then`8`imp_res_tac DIV_LE_MONOTONE >> gvs[]) >>
  DEP_REWRITE_TAC[word_to_bytes_be_w2w_proof] >> simp[] >>
  DEP_REWRITE_TAC[word_bytes_roundtrip_proof] >> simp[]
QED
