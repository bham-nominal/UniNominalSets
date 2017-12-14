Require Import UniMath.Foundations.PartA.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Combinatorics.Lists.

Require Import MoreLists.

Section PermLists.
Variable (A : hSet).
Variable (dec_A : isdeceq A).

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
  intros l.
  induction l as [n l].
  induction n as [ | n IHn].
  - apply idweq.
  - induction l as [p H].
    specialize (IHn H).
    pose (swap_to_weq p) as w.
    apply (weqcomp w IHn).
Defined.

End PermLists.
