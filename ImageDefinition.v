Add LoadPath "~/Documents/UniMath".
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.

Definition weq_compose
           {A B C : Type}
           (f : A ≃ B)
           (g : B ≃ C)
  : A ≃ C.
Proof.
  induction f as [f wef].
  induction g as [g weg].
  exists (g ∘ f).
  apply twooutof3c ; assumption.
Defined.

Section PermutationGroup.
  Variable (A : UU)
           (isasetA : isaset A).
    
  Definition perm_op : setwithbinop.
  Proof.
    unfold setwithbinop.
    use tpair.
    - use tpair.
      + exact (weq A A).
      + simpl.
        apply isasetweqtoset.
        exact isasetA.
    - simpl.
      intros g f.
      apply (weq_compose f g).
  Defined.

  Definition perm_group : gr.
  Proof.
    unfold gr.
    exists perm_op.
    use tpair.
    - unfold ismonoidop.
      use tpair.
      + intros f g h.
        use pair_path_in2.
        apply isapropisweq.
      + simpl.
        unfold isunital, isunit, islunit, isrunit.
        exists (idweq A).
        use tpair.
        * simpl.
          intros f.
          induction f as [f wef].
          use pair_path_in2.
          apply isapropisweq.
        * simpl.
          intros f.
          induction f as [f wef].
          use pair_path_in2.
          apply isapropisweq.
    - use tpair.
      + simpl.
        apply invweq.
      + use tpair.
        * intros f.
          unfold unel_is.
          simpl.
          use total2_paths2_f.
          -- apply funextfun.
             intros z.
             apply homotinvweqweq.
          -- apply isapropisweq.
        * intros f.
          unfold unel_is.
          simpl.
          use total2_paths2_f.
          -- apply funextfun.
             intros z.
             apply homotweqinvweq.
          -- apply isapropisweq.
  Defined.
End PermutationGroup.

Section FinitePermutations.
  Variable (A : UU)
           (dec_A : forall (a b : A), decidable (paths a b))
           (isasetA : isaset A).

  Definition swap := A × A.

  Definition swap_map : swap -> A -> A.
  Proof.
    intros s a.
    induction s as [a_from a_to].
    induction (dec_A a a_from).
    - exact a_to.
    - induction (dec_A a a_to).
      + exact a_from.
      + exact a.
  Defined.

  Definition swap_map_inv : swap -> A -> A.
  Proof.
    intros s a.
    induction s as [a_from a_to].
    induction (dec_A a a_to).
    - exact a_from.
    - induction (dec_A a a_from).
      + exact a_to.
      + exact a.
  Defined.

  Definition swap_to_weq : swap -> weq A A.
  Proof.
    intros s.
    use tpair.
    - apply swap_map.
      apply s.
    - simpl.
      use gradth.
      + apply swap_map_inv.
        apply s.
      + intros a.
        induction s as [a_from a_to].
        unfold swap_map, swap_map_inv.
        induction (dec_A a a_from) as [q | nq] ; cbn.
        * induction (dec_A a_to a_to) as [ | n] ; cbn.
          -- symmetry.
             assumption.
          -- use fromempty.
             apply n.
             reflexivity.
        * induction (dec_A a a_to) as [p0 | np0] ; cbn.
          -- induction (dec_A a_from a_from) as [p1 | np1] ; cbn.
             ++ induction (dec_A a_from a_to) as [p2 | np2] ; cbn.
                ** use (p2 @ _).
                   symmetry ; exact p0.
                ** symmetry ; exact p0.
             ++ use fromempty.
                apply np1.
                reflexivity.
          -- induction (dec_A a a_from) as [p1 | np1] ; cbn.
             ++ induction (dec_A a a_to) as [p2 | np2] ; cbn.
                ** symmetry ; exact p1.
                ** use fromempty.
                   apply nq.
                   exact p1.
             ++ induction (dec_A a a_to) as [p3 | np3] ; cbn.
                ** use fromempty.
                   apply np0.
                   exact p3.
                ** reflexivity.
      + intros a.
        induction s as [a_from a_to].
        unfold swap_map, swap_map_inv.
        induction (dec_A a a_to) as [q | nq] ; cbn.
        * induction (dec_A a_from a_from) as [p0 | np0] ; cbn.
          -- symmetry.
             exact q.
          -- use fromempty.
             apply np0.
             reflexivity.
        * induction (dec_A a a_from) as [p1 | np1] ; cbn.
          -- induction (dec_A a_to a_from) as [p2 | np2] ; cbn.
             ++ refine (p2 @ _).
                symmetry.
                exact p1.
             ++ induction (dec_A a_to a_to) as [p3 | np3] ; cbn.
                ** symmetry.
                   exact p1.
                ** use fromempty.
                   apply np3.
                   reflexivity.
          -- induction (dec_A a a_from) as [p2 | np2] ; cbn.
             ++ use fromempty.
                apply np1.
                exact p2.
             ++ induction (dec_A a a_to) as [p3 | np3] ; cbn.
                ** use fromempty.
                   apply nq.
                   exact p3.
                ** reflexivity.
  Defined.

  Definition swap_list := list swap.

  Definition swap_list_to_weq : swap_list -> weq A A.
  Proof.
    intros l.
    induction l as [n l].
    induction n as [ | n IHn].
    - apply idweq.
    - induction l as [p H].
      specialize (IHn H).
      pose (swap_to_weq p) as w.
      apply (weq_compose w IHn).
  Defined.

  Definition finite_perms : hsubtype (perm_group A isasetA).
  Proof.
    intros w.
    use hexists.
    - apply swap_list.
    - intros s.
      exact (w = swap_list_to_weq s).
  Defined.

  Definition is_sub_gr_finite_perms : issubgr finite_perms.
  Proof.
    use tpair.
    - use tpair.
      + unfold issubsetwithbinop ; cbn.
        intros f1 f2.
        induction f1 as [w1 l1].
        induction f2 as [w2 l2].
        cbn.
        admit.
      + cbn.
        admit.
    - cbn.
      intros f.
      induction f as [w l].
      intros H.
      admit.
  Admitted.

End FinitePermutations.