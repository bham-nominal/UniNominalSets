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
  induction s as [b c].
  induction (dec_A a b).
  - exact c.
  - induction (dec_A a c).
    + exact b.
    + exact a.
Defined.

Lemma dec_A_eq {x y : A} (e : x = y) : dec_A x y = inl e.
Proof.
  induction (dec_A x y) as [e' | n].
  - assert (h : e = e').
    { apply uip. apply setproperty. }
    rewrite h. apply idpath.
  - use fromempty. apply n. apply e.
Defined.

Corollary dec_A_triv (x : A) : dec_A x x = inl (idpath _).
Proof.
  apply dec_A_eq.
Defined.

Lemma dec_A_neq {x y : A} (n : x != y) : dec_A x y = inr n.
Proof.
  induction (dec_A x y) as [e | n'].
  - use fromempty. apply n. apply e.
  - assert (h : n = n').
    { use proofirrelevance. apply isapropneg. }
    rewrite h. apply idpath.
Defined.

Lemma swap_auto_inv (s : swap) : ∏ x : A, swap_map s (swap_map s x) = x.
Proof.
  intro a. induction s as [x y].
  unfold swap_map.
  induction (dec_A a x) as [q | nq] ; cbn.
  - rewrite (dec_A_triv y). cbn. rewrite q.
    induction (dec_A y x) as [q' | nq'] ; cbn.
    + assumption.
    + apply idpath.
  - induction (dec_A a y) as [q' | nq'] ; cbn.
    + rewrite q'. rewrite (dec_A_triv x). cbn.
      apply idpath.
    + rewrite (dec_A_neq nq). cbn.
      rewrite (dec_A_neq nq'). cbn.
      apply idpath.
Defined.

Definition swap_to_weq : swap -> weq A A.
Proof.
  intros s.
  use weqgradth.
  - exact (swap_map s).
  - exact (swap_map s).
  - apply swap_auto_inv.
  - apply swap_auto_inv.
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
          reflexivity.
       ++ apply isapropisweq.
Defined.


End PermLists.
