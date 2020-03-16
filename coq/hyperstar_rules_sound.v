Require Import List.
Require FunInd.

Section NI.

  (* State Action Output Name Value *)
  Variables S A O : Set.
  Variable s0 : S.
  Variable step : S -> A -> S.
  Variable output : S -> A -> O.

  Function run (s: S) (a: list A) : S :=
    match a with
    | nil => s
    | x :: xs => run (step s x) xs
    end.

  Definition do a :=
    run s0 a.

  Definition test alpha a :=
    output (do alpha) a.

  (* Domains *)
  Variable D : Set.
  Variable dom : A -> S -> D.

  Definition policy : Type := D -> D -> Prop.
  Section Intransitive. 
    Variable interferes : policy.

    Notation "A ~> B" := (interferes A B) (at level 10).

    Variable interferes_dec : forall (u v: D), {u ~> v} + {~ u ~> v}.

    Hypothesis interferes_refl : forall u, u ~> u.

    Inductive sources : list A -> D -> S -> D -> Prop :=
    | sources_nil :
        forall d s,
          sources nil d s d
    | sources_recurse :
        forall alpha u s a v,
          sources alpha u (step s a) v ->
          sources (a :: alpha) u s v
    | sources_contains :
        forall alpha u s a v,
          sources alpha u (step s a) v ->
          dom a s ~> v ->
          sources (a :: alpha) u s (dom a s).

    Lemma sources_has_u :
      forall a u s,
        sources a u s u.
    Proof.
      induction a.
      intros; constructor.
      intros; apply sources_recurse.
      apply IHa.
    Qed.

     Inductive ipurge : list A -> D -> S -> list A -> Prop :=
     | ipurge_nil :
         forall u s,
           ipurge nil u s nil
     | ipurge_nopurge :
         forall a alpha u s alpha',
         sources (a :: alpha) u s (dom a s) ->
         ipurge alpha u (step s a) alpha' ->
         ipurge (a :: alpha) u s (a :: alpha')
     | ipurge_purge :
         forall a alpha u s alpha',
           ~ (sources (a :: alpha) u s (dom a s)) ->
           ipurge alpha u s alpha' ->
           ipurge (a :: alpha) u s alpha'.

    Definition security : Prop :=
      forall alpha a alpha',
        ipurge alpha (dom a (run s0 alpha)) s0 alpha' ->
        test alpha a = test alpha' a.

    Section Hyperstar.
      Variables N V : Set.
      Variable contents : S -> N -> V.
      Variable label : S -> N -> D.

      Variable can_read : policy.
      Variable can_write : policy.

      Notation "A ⊑r B" := (can_read B A) (at level 10).
      Notation "A ⊑w B" := (can_write A B) (at level 10).
      Notation "A ⊑* B" := (interferes A B) (at level 10).

      Variable can_write_dec : forall (u v: D), {u ⊑w v} + {~ u ⊑w v}.
      Variable can_read_dec : forall (u v: D), {u ⊑r v} + {~ u ⊑r v}.

      Variable contents_eqv_dec : forall (s t: S) (n : N),
          {contents s n = contents t n} + {~ contents s n = contents t n}.

      Hypothesis can_read_write_interferes :
        forall T1 T2,
          (exists T3, T1 ⊑w T3 /\ T3 ⊑r T2) <-> 
          T1 ⊑* T2.

      Hypothesis can_write_refl :
        forall T, T ⊑w T.


      Hypothesis can_read_refl :
        forall T, T ⊑r T.

      Lemma can_write_interferes :
        forall T1 T2,
          T1 ⊑w T2 ->
          T1 ⊑* T2.
      Proof.
        intros.
        apply can_read_write_interferes.
        exists T2.
        auto.
      Qed.

      Lemma can_read_interferes :
        forall T1 T2,
          T1 ⊑r T2 ->
          T1 ⊑* T2.
      Proof.
        intros.
        apply can_read_write_interferes.
        exists T1.
        auto.
       Qed.

      Definition eqv u s t :=
        forall n,
          (label s n ⊑r u \/ label t n ⊑r u) ->
          (contents s n = contents t n).

      Hypothesis contents_equals_labels :
        forall s t n,
          contents s n = contents t n ->
          label s n = label t n.

      Lemma eqv_refl : forall d x, eqv d x x.
      Proof.
        unfold eqv; auto.
      Qed.

      Lemma eqv_sym : forall d x y, eqv d x y -> eqv d y x.
      Proof.
        firstorder.
      Qed.

      Hint Resolve eqv_refl eqv_sym.

      Lemma label_eqv_equal_r :
        forall u s t n,
          eqv u s t ->
          label s n ⊑r u ->
          label s n = label t n.
      Proof.
        firstorder.
      Qed.

      Lemma eqv_trans : forall d x y z, eqv d x y -> eqv d y z -> eqv d x z.
      Proof.
        unfold eqv; intros.
        destruct H1.
        - assert (label x n = label y n).
          firstorder.
          assert (label y n ⊑r d); try congruence.
          assert (contents x n = contents y n); auto.
          assert (contents y n = contents z n); auto.
          congruence.
        - assert (label z n = label y n).
          firstorder.
          assert (label y n ⊑r d); try congruence.
          assert (contents y n = contents z n); auto.
          assert (contents x n = contents y n); auto.
          congruence.
      Qed.

      Hypothesis eqv_dec : forall (d: D) (s t: S),
          {eqv d s t} + {~ eqv d s t}.

      Hypothesis dom_eqv_equal :
        forall u s t a,
          eqv u s t ->
          (dom a s) ⊑* u -> 
          dom a t = dom a s.

      Lemma dom_consistent :
        forall u s t a,
          eqv u s t ->
          (dom a s ⊑* u) <->
          (dom a t ⊑* u).
      Proof.
        intros.
        split; intros.
        - erewrite dom_eqv_equal; eauto.
        - erewrite dom_eqv_equal; eauto.
      Qed.

      Hypothesis label_eqv_equal :
        forall u s t n,
          eqv u s t ->
          label s n ⊑w u -> 
          label t n = label s n.

      Lemma label_consistent_w :
        forall u s t n,
          eqv u s t ->
          (label s n ⊑w u) <->
          (label t n ⊑w u).
      Proof.
        intros.
        split; intros.
        - erewrite label_eqv_equal; eauto.
        - erewrite label_eqv_equal; eauto.
      Qed.

      Lemma label_consistent_r :
        forall u s t n,
          eqv u s t ->
          (label s n ⊑r u) <->
          (label t n ⊑r u).
      Proof.
        split; intros; assert (label s n = label t n); auto; congruence.
      Qed.

      Hypothesis output_consistent :
        forall s t a,
          eqv (dom a s) s t ->
          output s a = output t a.

      Hypothesis downgrade_consistency :
        forall s a L,
          forall n,
            label (step s a) n ⊑r L ->
            (label s n ⊑r L \/ label s n ⊑r (dom a s)).

      Hypothesis write_consistency :
        forall a s t,
          forall n,
            ((dom a s) ⊑w (label s n) ->
            (dom a t) ⊑w (label t n) ->
            eqv (dom a s) s t ->
            contents s n = contents t n) ->
            contents (step s a) n = contents (step t a) n.

      Hypothesis write_safety :
        forall a s,
          forall n,
            ~ (contents (step s a) n = contents s n) ->
            (dom a s) ⊑w (label s n) /\ (dom a s) ⊑w (label (step s a) n).

      Lemma local_respect :
        forall s a u,
          ~ dom a s ⊑* u ->
          eqv u s (step s a).
      Proof.
        unfold eqv; intros.
        destruct H0.
        - destruct (contents_eqv_dec (step s a) s n); auto.
          exfalso.
          apply write_safety in n0.
          pose proof can_read_write_interferes.
          specialize (H1 (dom a s) (u)).
          firstorder.
        - destruct (contents_eqv_dec (step s a) s n); auto.
          exfalso.
          apply write_safety in n0.
          pose proof can_read_write_interferes.
          specialize (H1 (dom a s) (u)).
          firstorder.
      Qed.

      Lemma weak_step_consistency :
        forall s t u a,
          eqv u s t ->
          eqv (dom a s) s t ->
          eqv u (step s a) (step t a).
      Proof.
        unfold eqv; intros.
        intuition.
        - destruct (contents_eqv_dec s t n).
          + apply write_consistency.
            intuition.
          + exfalso. apply f.
            apply downgrade_consistency in H2.
            intuition.
        - destruct (contents_eqv_dec s t n).
          + apply write_consistency.
            intuition.
          + exfalso. apply f.
            apply downgrade_consistency in H2.
            intuition.
            erewrite dom_eqv_equal with (s := s) (u := (dom a s)) in H1; auto.
      Qed.

      Definition eqv_list (C: D -> Prop) s t :=
        forall u,
          C u ->
          eqv u s t.

      Lemma two :
        (forall alpha u alpha',
          ipurge alpha u s0 alpha' ->
          eqv u (do alpha) (do alpha')) -> security.
      Proof.
        unfold security, test, do.
        intros.
        auto.
      Qed.

      Lemma three :
        forall a alpha u s t,
          eqv_list (sources (a :: alpha) u s) s t ->
          eqv_list (sources alpha u (step s a)) (step s a) (step t a).
      Proof.
        unfold eqv_list.
        intros a alpha u s t H.
        unfold eqv_list in *; intros v.
        intros.

        destruct (interferes_dec (dom a s) v).
        - apply weak_step_consistency.
          + apply H.
            apply sources_recurse; eauto.
          + apply H.
            eapply sources_contains; eauto.

        - apply eqv_trans with (y := s).
          + apply eqv_sym.
            now apply local_respect.
          + assert (~ (dom a t)  ⊑* v).
            * unfold not; intros; apply n.
              erewrite dom_consistent; eauto.
              apply H.
              apply sources_recurse; auto.

            * apply eqv_trans with (y := t); auto.
              apply H.
              apply sources_recurse; auto.
              apply local_respect. auto.
      Qed.

      Lemma four :
        forall alpha a u s,
        ~ (sources (a :: alpha) u s (dom a s)) ->
        eqv_list (sources alpha u (step s a)) s (step s a).
      Proof.
        unfold eqv_list.
        intros.
        apply local_respect.
        contradict H.
        eapply sources_contains; eauto.
      Qed.

      Lemma source_consistent' :
        forall alpha u s t,
          eqv_list (sources alpha u s) s t ->
          forall v,
            sources alpha u s v ->
            sources alpha u t v.
        Proof.
        induction alpha; intros.
        - inversion H0.
          constructor.
        - inversion H0.
          + apply sources_recurse.
            eapply IHalpha; eauto.
            apply three; auto.
          + rewrite dom_eqv_equal with (s := t) (u := v0).
            * apply sources_contains with (v := v0).
              {
                apply IHalpha with (s := (step s a)) (t := (step t a)); auto.
                apply three; auto.
              }
              {
                pose proof dom_consistent.
                specialize (H8 v0 s t a).
                apply H8; auto.
                apply H.
                apply sources_recurse.
                auto.
              }
            * apply eqv_sym.
              apply H.
              constructor.
              auto.
            * eapply dom_consistent with (t := s); auto.
              apply eqv_sym.
              apply H.
              apply sources_recurse.
              auto.
        Qed.

      Lemma five :
        forall alpha u t alpha',
          ipurge alpha u t alpha' ->
            forall s,
            eqv_list (sources alpha u s) s t ->
            eqv u (run s alpha) (run t alpha').
      Proof.
        intros alpha u t alpha' H.
        induction H; intros.
        - simpl.
          unfold eqv_list in H.
          apply H.
          constructor.
        - unfold eqv_list in *.
          apply IHipurge.
          apply three.
          auto.
        - apply IHipurge.
          apply four in H.

          unfold eqv_list in *.
          intros.

          eapply eqv_trans with (y := (step s a)).

          * eapply three; eauto.
          * apply eqv_sym.
            apply H.
            eapply source_consistent'; eauto.
            apply three; auto.
      Qed.

      Theorem unwinding : security.
      Proof.
        unfold security.
        apply two.
        intros.
        now apply five.
     Qed.

    End Hyperstar.
  End Intransitive.
End NI.
