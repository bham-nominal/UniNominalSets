Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Ktheory.GroupAction.
Require Import UniMath.Foundations.Sets.

Require Import MoreLists.
Require Import PermLists.

Section Perm.

  Context {A : hSet}.
  Context (dec_A : isdeceq A).

  Definition carrier : hSet := @swap_list A.

  Definition actA_f : carrier -> A -> A.
    intros l a.
    apply (@list_ind (setdirprod A A)).
    - exact a.
    - intros x xs a'.
      (* actA xs a = a' *)
      exact (swap_map dec_A x a').
    - exact l.
  Defined.

  Local Notation "l₁ @ l₂" := (concatenate l₁ l₂).
  Local Notation "x :: xs" := (cons x xs).

  Fact act_cons_swap : forall x xs, actA_f (x :: xs) = swap_map dec_A x ∘ actA_f xs.
  Proof.
    intros.
    unfold actA_f.
    apply funextfun.
    intros a.
    simpl.
    rewrite list_ind_compute_2.
    unfold funcomp.
    reflexivity.
  Defined.

  Lemma act_concat_comp : forall l1 l2, actA_f (concatenate l1 l2) = (actA_f l1) ∘ (actA_f l2).
  Proof.
    intros l1 l2.
    apply (@list_ind (setdirprod A A)
                     (λ l1, actA_f (concatenate l1 l2) = actA_f l1 ∘ actA_f l2)).
    - apply idpath.
    - intros.
      rewrite concatenateStep.
      idtac.
      pose (act_cons_swap x (xs @ l2)).
      rewrite X in p.
      rewrite funcomp_assoc in p.
      rewrite <- (act_cons_swap x xs) in p.
      exact p.
  Defined.

  Lemma act_reverse_inverse (l : carrier) :
    ∏ x : A, actA_f (reverse l) (actA_f l x) = x.
  Proof.
    intro a.
    apply (@list_ind (setdirprod A A) (fun l => actA_f (reverse l) (actA_f l a) = a)).
    - cbn. apply idpath.
    - intros x xs h.
      rewrite reverse_cons. rewrite act_concat_comp.
      rewrite 2 act_cons_swap.
      unfold funcomp. cbn.
      rewrite swap_auto_inv. exact h.
  Defined.

  (* Coming soon in MoreLists *)
  Axiom reverse_involution : forall (l : carrier), l = reverse (reverse l).

  Definition actA : carrier -> A ≃ A.
    intros l.
    use weqgradth.
    - exact (actA_f l).
    - exact (actA_f (reverse l)).
    - apply act_reverse_inverse.
    - pose (act_reverse_inverse (reverse l)).
      rewrite <- reverse_involution in p. apply p.
  Defined.

  Definition hrel_gr : hrel carrier.
    unfold hrel.
    intros l₁ l₂.
    use hProppair.
    - exact (actA_f l₁ = actA_f l₂).
    - assert (isaset (A -> A)).
      + apply isaset_forall_hSet.
      + apply X.
  Defined.

  Definition equiv_gr : eqrel carrier.
    use eqrelconstr.
    - exact hrel_gr.
    - intros l₁ l₂ l₃.
      intros H₁ H₂.
      unfold hrel_gr in *.
      simpl in *.
      rewrite H₁. exact H₂.
    - intros l. simpl. reflexivity.
    - intros l₁ l₂ H. simpl in *. symmetry. exact H.
  Defined.

  Definition carrier_q : hSet := setquotinset equiv_gr.

  Definition unit : carrier_q.
    use setquotpair.
    - exact (setquotpr equiv_gr nil).
    - use iseqclassconstr.
      + apply hinhpr.
        simpl.
        use (carrierpair).
        * exact nil.
        * simpl.
          reflexivity.
      + intros.
        simpl in *.
        rewrite X0. exact X.
      + intros. simpl in *.
        rewrite <- X.
        exact X0.
  Defined.

  Definition concatenate_q (l₁ l₂ : carrier) : carrier_q.
    use setquotpair.
    - exact (setquotpr equiv_gr (concatenate l₁ l₂)).
    - use iseqclassconstr.
      + apply hinhpr.
        use carrierpair.
        * exact (concatenate l₁ l₂).
        * simpl. reflexivity.
      + intros. simpl in *.
        rewrite X in X0.
        exact X0.
      + intros. simpl in *.
        rewrite X in X0. exact X0.
  Defined.

  Fact compat_concat : iscomprelfun2 equiv_gr concatenate_q.
    intros x ? y y' R_x_x' R_y_y'.
    simpl in R_x_x', R_y_y'.
    apply subtypeEquality'.
    - simpl. change (fun x => ?h x) with h.
      pose @funextfun. unfold funextfunStatement in f.
      apply f. intro l.
      apply subtypeEquality'.
      + simpl. rewrite 2 act_concat_comp.
        now rewrite R_x_x', R_y_y'.
      + apply isapropisaprop.
    - apply isapropiseqclass.
  Defined.

  Definition mult : carrier_q -> carrier_q -> carrier_q.
    intros g₁ g₂.
    exact (setquotuniv2 equiv_gr carrier_q concatenate_q compat_concat g₁ g₂).
  Defined.

  Definition inv_q (l : carrier) : carrier_q.
    use setquotpair.
    - exact (setquotpr equiv_gr (reverse l)).
    - use iseqclassconstr.
      + apply hinhpr.
        use carrierpair.
        * exact (reverse l).
        * simpl. apply idpath.
      + intros l1 l2 R_l1_l2 Rl1. simpl in *.
        rewrite Rl1. assumption.
      + intros l1 l2 h h'. simpl in *.
        rewrite <- h. exact h'.
  Defined.

  Lemma act_rev : forall l, actA_f (reverse l) = invmap (actA l).
  Proof.
    intro l.
    pose (isasetweqtoset A A (setproperty A)).
    unfold invmap.
    (* So what? *)
  Admitted.

  Fact compat_inv : iscomprelfun equiv_gr inv_q.
  Proof.
    intros l1 l2 R_l1_l2. simpl in *.
    apply subtypeEquality'.
    - simpl. change (fun x => ?h x) with h.
      pose @funextfun. unfold funextfunStatement in f.
      apply f. intro l.
      apply subtypeEquality'.
      + simpl. rewrite 2 act_rev.
        assert (h : actA l1 = actA l2).
        { apply subtypeEquality'.
          - simpl. assumption.
          - apply isapropisweq.
        }
        rewrite h. apply idpath.
      + apply isapropisaprop.
    - apply isapropiseqclass.
  Defined.

  (* Definition assoc : isassoc mult := concatenate_assoc (setdirprod A A). *)

  Definition unital : isunital mult.
    use isunitalpair.
    - exact unit.
    - split.
      + unfold islunit.
        (* reflexivity. *)
        admit.
      + unfold isrunit.
        intros.
        (* apply concatenate_nil_lunit. *)
        admit.
  (* Defined. *)
  Admitted.

  Definition monoidop : ismonoidop mult.
  apply mk_ismonoidop.
  (* - exact assoc. *)
  (* - exact unital. *)
  (* Defined. *)
  Admitted.

  Definition invstruct : invstruct mult monoidop.
  use mk_invstruct.
  (* - exact inv. *)
  (* - unfold unel_is. simpl. *)
  (*   apply mk_isinv. *)
  (*   + unfold islinv. *)
  (*     intros. *)

  (*   + unfold isrinv. *)
  (*     intros. *)
  (*     admit. *)
  Admitted.

  Definition grop : isgrop mult.
  use mk_isgrop.
  - exact monoidop.
  - exact invstruct.
  Defined.


  Definition Perm : gr.
    use grconstr.
    - use setwithbinoppair.
      + exact carrier.
      (* + exact mult. *)
    (* - simpl. exact grop. *)
  (* Defined. *)
  Admitted.

End Perm.



Section Nom.
  Context (AtomSet : hSet).
  Context (PermASet : UU).
  (* Context (finitelySupported : ∀ {X : PermASet}, X -> UU). *)

  (* Definition isNominalSet (X : PermASet) := *)
  (*   ∀ x : X, finitelySupported x. *)

End Nom.
