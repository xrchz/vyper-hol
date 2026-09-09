(* Generic nested induction for MakeSSA dominator trees. *)
Theory makeSsaCurrentInduct
Ancestors
  makeSsaCurrentDefs
  list

Definition current_dom_tree_size_def:
  (current_dom_tree_size (DNode lbl children) =
     SUC (current_dom_trees_size children)) /\
  (current_dom_trees_size [] = 0) /\
  (current_dom_trees_size (child::rest) =
     SUC (current_dom_tree_size child + current_dom_trees_size rest))
End

Theorem current_dom_tree_induction:
  !P Q.
    (!lbl children. Q children ==> P (DNode lbl children)) /\
    Q [] /\
    (!child rest. P child /\ Q rest ==> Q (child::rest)) ==>
    (!t. P t) /\ (!ts. Q ts)
Proof
  rpt gen_tac >> strip_tac >>
  `!n.
     (!t. current_dom_tree_size t < n ==> P t) /\
     (!ts. current_dom_trees_size ts < n ==> Q ts)` by (
    completeInduct_on `n` >>
    conj_asm2_tac
    >- (rpt strip_tac >> Cases_on `t` >>
        first_x_assum irule >>
        first_x_assum irule >>
        gvs[current_dom_tree_size_def])
    >> rpt strip_tac >> Cases_on `ts`
    >- simp[]
    >> first_x_assum irule >> conj_tac
    >- (first_x_assum (qspec_then `SUC (current_dom_tree_size h)` mp_tac) >>
        (impl_tac >- gvs[current_dom_tree_size_def]) >> strip_tac >>
        first_x_assum (qspec_then `h` mp_tac) >> simp[])
    >> first_x_assum
         (qspec_then `SUC (current_dom_trees_size t)` mp_tac) >>
       (impl_tac >- gvs[current_dom_tree_size_def]) >> strip_tac >>
       first_x_assum (qspec_then `t` mp_tac) >> simp[]) >>
  conj_tac
  >- (gen_tac >>
      first_x_assum (qspec_then `SUC (current_dom_tree_size t)` mp_tac) >>
      simp[])
  >> gen_tac >>
     first_x_assum (qspec_then `SUC (current_dom_trees_size ts)` mp_tac) >>
     simp[]
QED

val _ = export_theory();
