
Require Import List.

Section NI.

  Variables S D A O : Set.
  Variable s0 : S.
  Variable step : S -> A -> S.
  Variable output : S -> A -> O.
  Variable interferes : D -> D -> Prop.
  Variable dom : A -> D.

  Notation "A ~> B" := (interferes A B) (at level 80).

  Hypothesis interferes_dec : forall u v, {u ~> v} + {not (u ~> v)}.

  Hypothesis interferes_refl :
    forall u, u ~> u.

  Fixpoint run (s: S) (l: list A) : S :=
    match l with
    | x :: xs => run (step s x) xs
    | nil => s
    end.

  Fixpoint purge (l: list A) (u: D) : list A :=
    match l with
    | nil => nil
    | x :: xs =>
      if interferes_dec (dom x) u
      then x :: purge xs u
      else purge xs u
    end.

  Definition do a := run s0 a.
  Definition test a b := output (do a) b.

  Definition secure : Prop :=
    forall a b,
      test a b = test (purge a (dom b)) b.

  Section Unwinding.

    Variable eqv : D -> S -> S -> Prop.

    Hypothesis eqv_refl : forall x d, eqv d x x.
    Hypothesis eqv_sym : forall d x y, eqv d x y -> eqv d y x.
    Hypothesis eqv_trans :
      forall d x y z, eqv d x y -> eqv d y z -> eqv d x z.

    Hypothesis output_consistent :
      forall a s t,
        eqv (dom a) s t ->
        output s a = output t a.

    Lemma eqv_do_purge_same :
      (forall a u,
          eqv u (do a) (do (purge a u))) ->
      secure.
    Proof.
      unfold secure, test.
      intros H a b.
      apply output_consistent.
      now apply H.
    Qed.

    Hypothesis local_respect :
      forall a u s,
        not (dom a ~> u) ->
        eqv u s (step s a).

    Hypothesis step_consistent :
      forall u s t a,
        eqv u s t ->
        eqv u (step s a) (step t a).

    Lemma unwinding_helper :
      forall a s t u,
        eqv u s t ->
        eqv u (run s a) (run t (purge a u)).
    Proof.
      intros a; induction a; intros; simpl; auto.
      destruct (interferes_dec (dom a) u); simpl.
      - apply IHa; auto.
      - apply IHa.
        apply eqv_sym.
        eapply eqv_trans.
        apply local_respect.
        exact n.
        auto.
     Qed.


    Theorem unwinding : secure.
    Proof.
      unfold secure, test.
      intros a b.
      apply output_consistent.
      unfold do.
      apply unwinding_helper; auto.
    Qed.

  End Unwinding.

End NI.
