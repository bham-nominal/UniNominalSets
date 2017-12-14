Add LoadPath "~/Documents/UniMath".
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.

Definition reverse {X : UU} : list X -> list X.
Proof.
  use list_ind.
  - apply nil.
  - intros x ? rev.
    exact (concatenate rev (cons x nil)).
Defined.

Definition reverse_cons {X : UU} (x : X) (l : list X)
  : reverse (cons x l) = concatenate (reverse l) (cons x nil).
Proof.
  reflexivity.
Defined.

Definition nil_concat {X : UU} : forall (l : list X), concatenate nil l = l.
Proof.
  reflexivity.
Defined.

Definition concat_nil {X : UU} : forall (l : list X), concatenate l nil = l.
Proof.
  use list_ind.
  - reflexivity.
  - simpl ; intros x xs IH.
    rewrite concatenateStep, IH.
    reflexivity.
Defined.

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
           (dec_A : isdeceq A).

  Definition isasetA : isaset A.
  Proof.
    use isasetifdeceq.
    assumption.
  Defined.

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
    use list_ind.
    - apply idweq.
    - intros p xs IHn.
      pose (swap_to_weq p) as w.
      apply (weq_compose IHn w).
  Defined.

  Definition swap_list_to_weq_nil : swap_list_to_weq nil = (idweq _).
  Proof.
    reflexivity.
  Defined.

  Definition swap_list_to_weq_cons (a : swap) (ls : swap_list)
    : swap_list_to_weq (cons a ls) = weq_compose (swap_list_to_weq ls) (swap_to_weq a).
  Proof.
    reflexivity.
  Defined.

  Definition swap_list_to_weq_concat : forall (l1 l2 : swap_list),
      weq_compose (swap_list_to_weq l2) (swap_list_to_weq l1)
      = swap_list_to_weq (concatenate l1 l2).
  Proof.
    intros l1 l2. revert l1.
    use list_ind.
    -- simpl.
       rewrite nil_concat.
       use total2_paths2_f.
       ++ use funextfun.
          intros z.
          reflexivity.
       ++ apply isapropisweq.
    -- simpl ; intros x xs IH.
       rewrite concatenateStep.
       rewrite !swap_list_to_weq_cons.
       rewrite <- IH.
       use total2_paths2_f.
       ++ use funextfun.
          intros z.
          reflexivity.
       ++ apply isapropisweq.
  Defined.

  Definition finite_perms : hsubtype (perm_group A isasetA).
  Proof.
    intros w.
    use hexists.
    - apply swap_list.
    - intros s.
      exact (w = swap_list_to_weq s).
  Defined.


  Lemma has_inverse_list (w : A → A) (we : isweq w) (l : swap_list) :
    ∑ s : swap_list, invweq (swap_list_to_weq l) = swap_list_to_weq s.
  Proof.
    use tpair.
    + apply (reverse l).
    + simpl.
      revert l.
      use list_ind.
      -- cbn.
         symmetry.
         exact inv_idweq_is_idweq.
      -- simpl ; intros x xs IH.
         rewrite swap_list_to_weq_cons.
         rewrite invweqcomp.
         rewrite reverse_cons.
         rewrite IH.
         rewrite <- swap_list_to_weq_concat.
         use total2_paths2_f.
         ++ use funextfun.
            intros z.
            cbn.
            assert (swap_map x = swap_map_inv x) as X.
            {
              use funextfun.
              induction x as [xf xt].
              intros a.
              unfold swap_map, swap_map_inv.
              induction (dec_A a xt) as [p1 | n1]
              ; induction (dec_A a xf) as [p2 | n2] ; try reflexivity.
              cbn.
              rewrite <- p1, <- p2.
              reflexivity.
            }
            rewrite X.
            reflexivity.
         ++ apply isapropisweq.
  Qed.

  Definition is_sub_gr_finite_perms : issubgr finite_perms.
  Proof.
    use tpair.
    - use tpair.
      + intros f1 f2.
        induction f1 as [w1 l1'].
        induction f2 as [w2 l2'].
        unfold finite_perms in *.
        apply (Propositions.squash_to_hProp l1').
        intro l1.
        apply (Propositions.squash_to_hProp l2').
        intro l2.
        apply total2tohexists ; cbn.
        clear l1' l2'.
        induction l1 as [l1 p1].
        induction l2 as [l2 p2].
        rewrite p1, p2. clear p1. clear p2.
        use tpair.
        * exact (concatenate l1 l2).
        * cbn.
          apply swap_list_to_weq_concat.
      + cbn.
        apply total2tohexists.
        use tpair.
        * exact nil.
        * reflexivity.
    - intros w.
      induction w as [w we].
      intros l'.
      unfold finite_perms in *.
      apply (Propositions.squash_to_hProp l').
      intro l. clear l'.
      induction l as [l p].
      rewrite p. clear p.
      apply total2tohexists ; cbn.
      now apply has_inverse_list with (w := w).
  Defined.

End FinitePermutations.
