Require Import UniMath.Foundations.PartA.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.

Require Import MoreLists.


Section PermLists.
  Context  {A : hSet}
           (dec_A : isdeceq A).

  Definition swap := setdirprod A A.
  Definition swap_list := setlist swap.

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

  Definition swap_list_to_weq : swap_list -> weq A A.
  Proof.
    use list_ind.
    - apply idweq.
    - intros p xs IHn.
      pose (swap_to_weq p) as w.
      apply (weqcomp IHn w).
  Defined.

  Definition swap_list_to_weq_nil : swap_list_to_weq nil = (idweq _).
  Proof.
    reflexivity.
  Defined.

  Definition swap_list_to_weq_cons (a : swap) (ls : swap_list)
    : swap_list_to_weq (cons a ls) = weqcomp (swap_list_to_weq ls) (swap_to_weq a).
  Proof.
    reflexivity.
  Defined.

  Definition swap_list_to_weq_concat : forall (l1 l2 : swap_list),
      weqcomp (swap_list_to_weq l2) (swap_list_to_weq l1)
      = swap_list_to_weq (concatenate l1 l2).
  Proof.
    intros l1 l2. revert l1.
    use list_ind.
    -- simpl.
       rewrite concatenate_nil_lunit.
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


  Definition weq_inverse_list (l : swap_list) :
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
  Defined.


End PermLists.
