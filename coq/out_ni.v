Require Import Bool List.

Section Metasystem.

Variables A O D: Set.

Class M : Type := {
  S: Set;
  init: S;
  step: S -> A -> S;
  output : D -> S -> O;
  safe : S -> Prop;
  safe_init: safe init;
  safe_step: forall s a, safe s -> safe (step s a);
}.

Section Policy.

Variable interferes: D -> D -> bool.

Section Machine.
  Variable m : M.

  Definition run {m: M} (s: S) (a: list A) : S :=
    fold_left step a s.

  Definition do {m: M} (alpha: list A) : S :=
    run init alpha.

  Inductive Reachable {m: M} : S -> Set :=
  | Reachable_init : Reachable init
  | Reachable_step : forall s a,
      Reachable s ->
      Reachable (step s a).

  Definition SR {m: M} := sigT Reachable.

  Definition init_r {m: M} : SR := existT _ init Reachable_init.

  Definition step_r {m: M} (sr: SR) (a: A) : SR :=
    match sr with
    | existT _ s r =>
      existT _ (step s a) (Reachable_step s a r)
    end.

  Definition run_r {m: M} (sr: SR) (a: list A) : SR :=
    fold_left step_r a sr.

  Definition do_r {m: M} (alpha: list A) : SR :=
    run_r init_r alpha.

  Lemma do_run :
    forall alpha a s,
    forall m: M,
      run s (alpha ++ (a :: nil)) = step (run s alpha) a.
  Proof.
    intros.
    apply fold_left_app.
  Qed.

  Lemma do_run_r :
    forall alpha a sr,
      run_r sr (alpha ++ (a :: nil)) = step_r (run_r sr alpha) a.
  Proof.
    intros.
    apply fold_left_app.
  Qed.

  Fixpoint extract_trace {m: M} (s: S) (r: Reachable s) : list A :=
    match r with
    | Reachable_init => nil
    | Reachable_step s' a r' => extract_trace s' r' ++ (a :: nil)
    end.

  Fixpoint extract_trace_r {m: M} (sr: SR) : list A :=
    match sr with
    | existT _ s r => extract_trace s r
    end.

  Hint Resolve Reachable_init Reachable_step.
  Hint Resolve safe_init safe_step.

  Lemma reachable_safe :
    forall s, Reachable s -> safe s.
  Proof.
    intros; induction H; auto.
  Qed.

  Lemma safe_r :
    forall sr: SR, safe (projT1 sr).
  Proof.
    intros.
    apply reachable_safe.
    destruct sr; auto.
  Qed.

  Lemma safe_run :
    forall s alpha,
      safe s ->
      safe (run s alpha).
  Proof.
    intros; induction alpha using rev_ind; auto.
    rewrite do_run; auto.
  Qed.

  Hint Resolve safe_r safe_run.
  Hint Resolve reachable_safe.

  Definition rev_list_rect A (P: list A -> Type) H H0 l : P (rev l) :=
    list_rect (fun l => P (rev l)) H H0 _.

  Definition rev_rect A (P: list A -> Type) H (H0: forall x l, P l -> P (l ++ x :: nil)) l : P l :=
    eq_rect _ _ (rev_list_rect _ _ H (fun a l => H0 a (rev l)) _) _ (rev_involutive _).

  Lemma run_reachable :
    forall s alpha,
      Reachable s ->
      Reachable (run s alpha).
  Proof.
    intros.
    induction alpha using rev_rect; auto.
    rewrite do_run; auto.
  Qed.

  Lemma step_r_step :
    forall sr a,
      projT1 (step_r sr a) = step (projT1 sr) a.
  Proof.
    destruct sr.
    reflexivity.
  Qed.

  Lemma run_r_run :
    forall sr alpha,
      projT1 (run_r sr alpha) = run (projT1 sr) alpha.
  Proof.
    intros.
    destruct sr.
    induction alpha using rev_ind.
    - auto.
    - simpl.
      rewrite do_run; auto.
      rewrite do_run_r.
      rewrite step_r_step.
      rewrite IHalpha.
      reflexivity.
  Qed.

  Lemma do_extract :
    forall s r,
      s = run init (extract_trace s r).
  Proof.
    intros.
    induction r; auto.
    unfold do in *.
    simpl.
    rewrite do_run; auto.
    congruence.
  Qed.

  Lemma do_extract_r :
    forall sr: SR,
      projT1 sr = run init (extract_trace_r sr).
  Proof.
    intros.
    destruct sr.
    apply do_extract.
  Qed.

  Lemma do_r_extract :
    forall s r,
      s = projT1 (run_r init_r (extract_trace s r)).
  Proof.
    intros.
    induction r; auto.
    simpl.
    erewrite do_run_r with (alpha := extract_trace s r); auto.
    rewrite step_r_step.
    f_equal.
    destruct r; auto.
  Qed.

  Lemma do_r_extract_r :
    forall sr: SR,
      sr = run_r init_r (extract_trace_r sr).
  Proof.
    intros.
    destruct sr.
    unfold extract_trace_r.
    induction r; auto.
    simpl.
    erewrite do_run_r with (alpha := extract_trace s r); auto.
    rewrite <- IHr.
    auto.
  Qed.

  Lemma proj_init_r :
    projT1 init_r = init.
  Proof.
    auto.
  Qed.

  Lemma proj_s :
    forall s r,
      s = projT1 (existT Reachable s r).
  Proof.
    auto.
  Qed.

  Hint Resolve run_reachable do_extract do_extract_r.
End Machine.

Section Noninterference.
  Variable Spec : M.
  Variable dom : A -> S -> D.

  Section Intransitive.

    Inductive sources : list A -> D -> S -> D -> Prop :=
    | sources_nil :
        forall u s,
          sources nil u s u
    | sources_recurse :
        forall alpha u s a v,
          sources alpha u (step s a) v ->
          sources (a :: alpha) u s v
    | sources_contains :
        forall alpha u s a v,
          sources alpha u (step s a) v ->
          interferes (dom a s) v = true ->
          sources (a :: alpha) u s (dom a s).

    Lemma sources_has_u :
      forall a u s,
        sources a u s u.
    Proof.
      induction a; constructor; auto.
    Qed.

    Inductive ipurge : list A -> D -> S -> list A -> Prop :=
    | ipurge_nil :
        forall u s,
          ipurge nil u s nil
    | ipurge_nopurge :
        forall a alpha u s alpha',
          (* sources (a :: alpha) u s (dom a s) -> *)
          ipurge alpha u (step s a) alpha' ->
          ipurge (a :: alpha) u s (a :: alpha')
    | ipurge_purge :
        forall a alpha u s alpha',
          ~ (sources (a :: alpha) u s (dom a s)) ->
          ipurge alpha u s alpha' ->
          ipurge (a :: alpha) u s alpha'.

    Definition noninterference : Prop :=
      forall s s' alpha alpha' u,
        s = run init alpha ->
        s' = run init alpha' ->
        ipurge alpha u init alpha' ->
        output u s = output u s'.

    Section Unwinding.
      Variable eqv : D -> S -> S -> Prop.

      Section Relation.
        Set Implicit Arguments.
        Variable T: Set.
        Variable R: T -> T -> Prop.

        Definition reflexive := forall x, R x x.
        Definition symmetric := forall x y, R x y -> R y x.
        Definition transitive := forall x y z, R x y -> R y z ->  R x z.

        Hint Unfold reflexive transitive symmetric.

        Unset Implicit Arguments.
      End Relation.

      Hypothesis eqv_refl : forall d, reflexive (eqv d).
      Hypothesis eqv_sym : forall d, symmetric (eqv d).
      Hypothesis eqv_trans : forall d, transitive (eqv d).

      Definition dom_consistency :=
        forall s t a,
          safe s ->
          safe t ->
          eqv (dom a s) s t ->
          dom a s = dom a t.

      Definition dom_respect :=
        forall u s t a,
          safe s ->
          safe t ->
          eqv u s t ->
          interferes (dom a s) u =
          interferes (dom a t) u.

      Definition output_consistency :=
        forall s t u,
          safe s ->
          safe t ->
          eqv u s t ->
          output u s = output u t.

      Definition local_respect :=
        forall s a u,
          safe s ->
          (interferes (dom a s) u) = false ->
          eqv u s (step s a).

      Definition weak_step_consistency :=
        forall s t u a,
          safe s ->
          safe t ->
          eqv u s t ->
          eqv (dom a s) s t ->
          eqv u (step s a) (step t a).

      Definition step_consistency :=
        forall s t u a,
          safe s ->
          safe t ->
          eqv u s t ->
          eqv u (step s a) (step t a).

      Definition step_respect :=
        forall s t u a,
          safe s ->
          safe t ->
          (interferes (dom a s) u) = false ->
          eqv u s t ->
          eqv u (step s a) (step t a).

      Lemma local_respect_step_respect :
        dom_respect ->
        local_respect ->
        step_respect.
      Proof.
        unfold dom_respect, local_respect, step_respect.
        intros.
        assert (interferes (dom a t) u = false).
        erewrite <- H; eauto.
        assert (eqv u t (step t a)); auto.
        assert (eqv u s (step s a)); auto.
        eapply eqv_trans; eauto.
        eapply eqv_trans; eauto.
        apply eqv_sym.
        auto.
      Qed.

      Definition eqv_list (C: D -> Prop) (s t: S) : Prop :=
        forall u,
          C u ->
          eqv u s t.

      Hypothesis dom_consistency: dom_consistency.
      Hypothesis dom_respect: dom_respect.
      Hypothesis output_consistency: output_consistency.
      Hypothesis local_respect: local_respect.
      Hypothesis weak_step_consistency: weak_step_consistency.
      Hypothesis step_consistency: step_consistency.
      Hypothesis step_respect: step_respect.

      Hint Resolve safe_init safe_step safe_run.
      Hint Resolve reachable_safe Reachable_step.

      Lemma two :
        (forall alpha u alpha',
            ipurge alpha u init alpha' ->
            eqv u (do alpha) (do alpha')) -> noninterference.
      Proof.
        unfold noninterference.
        intros.
        subst.
        apply output_consistency; auto.
        apply H.
        auto.
      Qed.

      Lemma three :
        forall a alpha u s t,
          safe s ->
          safe t ->
          eqv_list (sources (a :: alpha) u s) s t ->
          eqv_list (sources alpha u (step s a)) (step s a) (step t a).
      Proof.
        unfold eqv_list.
        intros a alpha u s t Hs Ht H.
        unfold eqv_list in *; intros v.
        intros.

        destruct (interferes (dom a s) v) eqn:?.
        - apply weak_step_consistency; auto.
          + apply H.
            apply sources_recurse; eauto.
          + apply H.
            eapply sources_contains; eauto.

        - apply eqv_trans with (y := s).
          + apply eqv_sym.
            now apply local_respect.
          + assert (interferes (dom a t) v = false).
            * rewrite <- Heqb.
              unfold Unwinding.dom_respect in dom_respect.
              erewrite dom_respect; eauto.
              apply eqv_sym.
              apply H.
              apply sources_recurse; auto.

            * apply eqv_trans with (y := t); auto.
              apply H.
              apply sources_recurse; auto.
      Qed.

      Lemma four :
        forall alpha a u s,
          safe s ->
          ~ (sources (a :: alpha) u s (dom a s)) ->
          eqv_list (sources alpha u (step s a)) s (step s a).
      Proof.
        unfold eqv_list.
        intros alpha a u s Hs H; intros.
        apply local_respect; auto.
        assert (~ interferes (dom a s) u0 = true).
        contradict H.
        eapply sources_contains; eauto.
        destruct (interferes (dom a s) u0) eqn:?; subst; intuition.
      Qed.

      Lemma source_consistent :
        forall alpha u s t,
          safe s ->
          safe t ->
          eqv_list (sources alpha u s) s t ->
          forall v,
            sources alpha u s v ->
            sources alpha u t v.
      Proof.
        induction alpha; intros u s t Hs Ht H v H0.
        - inversion H0.
          constructor.
        - inversion H0.
          + apply sources_recurse.
            eapply IHalpha with (s := step s a); eauto.
            apply three; auto.
          + rewrite dom_consistency with (t := t); auto.
            * apply sources_contains with (v := v0).
              {
                apply IHalpha with (s := (step s a)) (t := (step t a)); auto.
                apply three; auto.
              }
              {
                subst.
                rewrite dom_respect with (u := v0) (s := s) (t := t) in H7; auto.
                apply H; constructor; auto.
              }
            * apply H.
              congruence.
      Qed.

      Lemma five :
        forall alpha u t alpha',
          safe t ->
          ipurge alpha u t alpha' ->
          forall s,
            safe s ->
            eqv_list (sources alpha u s) s t ->
            eqv u (run s alpha) (run t alpha').
      Proof.
        intros alpha u t alpha' Ht H.
        induction H; intros.
        - apply H0.
          constructor.
        - unfold eqv_list in *.
          apply IHipurge; auto.
          apply three; auto.
        - apply IHipurge; auto.
          apply four in H.

          unfold eqv_list in *.
          intros.
          eapply eqv_trans with (y := (step s a)); auto.
          * eapply three; eauto.
          * apply eqv_sym.
            apply H.
            eapply source_consistent with (s := step s0 a); eauto.
            apply three; auto.
          * auto.
      Qed.

      Definition nonleakage :=
        forall (alpha: list A) s t u,
          Reachable s ->
          Reachable t ->
          eqv_list (sources alpha u s) s t ->
          output u (run s alpha) = output u (run t alpha).

      Definition noninfluence :=
        forall (alpha alpha': list A) s t u,
          Reachable s ->
          Reachable t ->
          eqv_list (sources alpha u s) s t ->
          ipurge alpha u t alpha' ->
          output u (run s alpha) = output u (run t alpha').

      Lemma eqv_list_refl :
        forall C s,
          eqv_list C s s.
      Proof.
        unfold eqv_list.
        intros.
        apply eqv_refl.
      Qed.

      Lemma noninfluence_noninterference :
        noninfluence -> noninterference.
      Proof.
        unfold noninfluence, noninterference.
        intros.
        subst s s'.
        apply H; try (apply Reachable_init); auto.
        apply eqv_list_refl.
      Qed.

      Lemma ipurge_refl :
        forall alpha u s,
          ipurge alpha u s alpha.
      Proof.
        induction alpha; intros; constructor; auto.
      Qed.

      Lemma noninfluence_nonleakage :
        noninfluence -> nonleakage.
      Proof.
        unfold noninfluence, nonleakage.
        intros.
        eapply H; eauto.
        apply ipurge_refl.
      Qed.

      Theorem noninfluence_unwinding :
        noninfluence.
      Proof.
        unfold noninfluence.
        intros.
        apply output_consistency; auto.
        apply five; auto.
      Qed.

      Theorem noninterference_unwinding :
        noninterference.
      Proof.
        apply noninfluence_noninterference.
        apply noninfluence_unwinding.
      Qed.

      Theorem nonleakage_unwinding :
        nonleakage.
      Proof.
        unfold nonleakage, eqv_list.
        induction alpha; intros.
        - apply output_consistency; auto.
          apply H1.
          constructor.
        - apply IHalpha; auto.
          + intros.
            destruct (interferes (dom a s) u0) eqn:?.
            * apply weak_step_consistency; auto.
              apply H1.
              now constructor.
              apply H1.
              eapply sources_contains; eauto.
            * apply step_respect; auto.
              apply H1.
              now constructor.
      Qed.

      Definition transitive_nonleakage :=
        forall alpha s t u,
          Reachable s ->
          Reachable t ->
          eqv u s t ->
          eqv u (run s alpha) (run t alpha).

      Theorem transitive_nonleakage_unwinding :
        transitive_nonleakage.
      Proof.
        unfold transitive_nonleakage.
        induction alpha; intros.
        - auto.
        - apply IHalpha; auto.
      Qed.

    End Unwinding.
  End Intransitive.

  Section Transitive.

    (* Transitive and intransitive cases agree with each other *)

    Definition interferes_p u v : Prop := interferes u v = true.

    Lemma interferes_p_neg :
      forall u v, ~interferes_p u v <-> interferes u v = false.
    Proof.
      intros.
      apply not_true_iff_false.
    Qed.

    Hypothesis interferes_refl:
      reflexive interferes_p.

    Hypothesis interferes_trans:
      transitive interferes_p.

    Lemma transitive_sources:
      forall alpha u s v,
        sources alpha u s v ->
        interferes_p v u.
    Proof.
      induction alpha; intros; inversion H; subst.
      - apply interferes_refl.
      - eapply IHalpha; eauto.
      - eapply interferes_trans; eauto.
    Qed.

    Variable eqv : D -> S -> S -> Prop.

    Hypothesis eqv_refl : forall d, reflexive (eqv d).
    Hypothesis eqv_sym : forall d, symmetric (eqv d).
    Hypothesis eqv_trans : forall d, transitive (eqv d).

    Hypothesis dom_respect : dom_respect eqv.
    Hypothesis local_respect : local_respect eqv.
    Hypothesis weak_step_consistency : weak_step_consistency eqv.

    Definition eqv_t (u : D) (s t : S) :=
       forall v, interferes v u = true -> eqv v s t.

    Lemma transitive_step_consistency :
      step_consistency eqv_t.
    Proof.
      unfold step_consistency, eqv_t; intros.
      destruct (interferes (dom a s) u) eqn:?.
      - eapply weak_step_consistency; eauto.
      - assert (interferes (dom a s) v = false).
        rewrite <- interferes_p_neg in *.
        firstorder.
        assert (eqv v s (step s a)).
        apply local_respect; auto.
        assert (eqv v t (step t a)).
        apply local_respect; auto.
        rewrite <- dom_respect with (s := s); auto.
        apply eqv_trans with (y := t); auto.
        eapply eqv_trans; eauto.
        apply eqv_sym; auto.
    Qed.

  End Transitive.

End Noninterference.

Section ReachableNoninterference.
  Variable Impl : M.
  Variable dom_r: A -> SR -> D.

  Section Intransitive.

    Inductive sources_r : list A -> D -> SR -> D -> Prop :=
    | sources_r_nil :
        forall u s,
          sources_r nil u s u
    | sources_r_recurse :
        forall alpha u s a v,
          sources_r alpha u (step_r s a) v -> sources_r (a :: alpha) u s v
    | sources_r_contains :
        forall alpha u s a v,
          sources_r alpha u (step_r s a) v ->
          interferes (dom_r a s) v = true ->
          sources_r (a :: alpha) u s (dom_r a s).

    Lemma sources_r_has_u :
      forall a u s,
        sources_r a u s u.
    Proof.
      induction a; constructor; auto.
    Qed.

    Inductive ipurge_r : list A -> D -> SR -> list A -> Prop :=
    | ipurge_r_nil :
        forall u s,
          ipurge_r nil u s nil
    | ipurge_r_nopurge :
        forall a alpha u s alpha',
          (* sources_r (a :: alpha) u s (dom_r a s) -> *)
          ipurge_r alpha u (step_r s a) alpha' ->
          ipurge_r (a :: alpha) u s (a :: alpha')
    | ipurge_r_purge :
        forall a alpha u s alpha',
          ~ (sources_r (a :: alpha) u s (dom_r a s)) ->
          ipurge_r alpha u s alpha' ->
          ipurge_r (a :: alpha) u s alpha'.

    Definition noninterference_r : Prop :=
      forall s s' alpha alpha' u,

        s = run_r init_r alpha ->
        s' = run_r init_r alpha' ->

        ipurge_r alpha u init_r alpha' ->
        output u (projT1 s) = output u (projT1 s').

    Section Unwinding.

      Variable eqv_r : forall (_: D) (s t: SR), Prop.
      Hypothesis eqv_r_refl : forall x d, eqv_r d x x.
      Hypothesis eqv_r_sym : forall d x y, eqv_r d x y -> eqv_r d y x.
      Hypothesis eqv_r_trans : forall d x y z, eqv_r d x y -> eqv_r d y z -> eqv_r d x z.

      Definition dom_consistency_r :=
        forall s t a,
          eqv_r (dom_r a s) s t ->
          dom_r a s = dom_r a t.

      Definition dom_respect_r :=
        forall u s t a,
          eqv_r u s t ->
          interferes (dom_r a s) u = interferes (dom_r a t) u.

      Definition output_consistency_r :=
        forall s t u,
          eqv_r u s t ->
          output u (projT1 s) = output u (projT1 t).

      Definition local_respect_r :=
        forall s a u,
          interferes (dom_r a s) u = false ->
          eqv_r u s (step_r s a).

      Definition weak_step_consistency_r :=
        forall s t u a,
          eqv_r u s t ->
          eqv_r (dom_r a s) s t ->
          eqv_r u (step_r s a) (step_r t a).

      Definition step_consistency_r :=
        forall s t u a,
          eqv_r u s t  ->
          eqv_r u (step_r s a) (step_r t a).

      Definition step_respect_r :=
        forall s t u a,
          interferes (dom_r a s) u = false ->
          eqv_r u s t  ->
          eqv_r u (step_r s a) (step_r t a).

      Hypothesis dom_consistency_r: dom_consistency_r.
      Hypothesis dom_respect_r: dom_respect_r.
      Hypothesis output_consistency_r: output_consistency_r.
      Hypothesis local_respect_r: local_respect_r.
      Hypothesis weak_step_consistency_r: weak_step_consistency_r.
      Hypothesis step_consistency_r: step_consistency_r.
      Hypothesis step_respect_r: step_respect_r.

      Hint Resolve eqv_r_refl eqv_r_sym eqv_r_trans.

      Definition eqv_r_list (C: D -> Prop) (s t: SR) : Prop :=
        forall u,
          C u ->
          eqv_r u s t.

      Hint Resolve safe_init safe_step safe_run.

      Lemma two_r :
        (forall alpha u alpha',
            ipurge_r alpha u init_r alpha' ->
            eqv_r u (do_r alpha) (do_r alpha')) -> noninterference_r.
      Proof.
        unfold noninterference_r.
        intros.
        eapply output_consistency_r.
        subst.
        eapply H.
        auto.
      Qed.

      Lemma three_r :
        forall a alpha u s t,
          eqv_r_list (sources_r (a :: alpha) u s) s t ->
          eqv_r_list (sources_r alpha u (step_r s a)) (step_r s a) (step_r t a).
      Proof.
        unfold eqv_r_list.
        intros a alpha u s t H.
        unfold eqv_list in *; intros v.
        intros.

        destruct (interferes (dom_r a s) v) eqn:?; subst.
        - apply weak_step_consistency_r; auto.
          + apply H.
            apply sources_r_recurse; eauto.
          + apply H.
            eapply sources_r_contains; eauto.

        - apply eqv_r_trans with (y := s).
          + apply eqv_r_sym.
            now apply local_respect_r.
          + assert (interferes (dom_r a t) v = false).
            * rewrite <- Heqb.
              unfold Unwinding.dom_respect_r in dom_respect_r.
              erewrite dom_respect_r. eauto.
              apply eqv_r_sym.
              apply H.
              apply sources_r_recurse; auto.

            * apply eqv_r_trans with (y := t); auto.
              apply H.
              apply sources_r_recurse; auto.
      Qed.

      Lemma four_r :
        forall alpha a u s,
          ~ (sources_r (a :: alpha) u s (dom_r a s)) ->
          eqv_r_list (sources_r alpha u (step_r s a)) s (step_r s a).
      Proof.
        unfold eqv_r_list.
        intros alpha a u s; intros.
        apply local_respect_r; auto.
        assert (interferes (dom_r a s) u0 <> true).
        contradict H.
        eapply sources_r_contains; eauto.
        destruct (interferes (dom_r a s)) eqn:?; subst; auto.
        contradict H1; auto.
      Qed.

      Lemma source_consistent_r :
        forall alpha u s t,
          eqv_r_list (sources_r alpha u s) s t ->
          forall v,
            sources_r alpha u s v ->
            sources_r alpha u t v.
      Proof.
        induction alpha; intros u s t H v H0.
        - inversion H0.
          constructor.
        - inversion H0.
          + apply sources_r_recurse.
            eapply IHalpha with (s := step_r s a); eauto.
            apply three_r; auto.
          + rewrite dom_consistency_r with (t := t).
            * apply sources_r_contains with (v := v0).
              {
                apply IHalpha with (s := (step_r s a)) (t := (step_r t a)); auto.
                apply three_r; auto.
              }
              {
                subst.
                rewrite dom_respect_r with (u := v0) (s := s) (t := t) in H7; auto.
                apply H; constructor; auto.
              }
            * apply H.
              congruence.
      Qed.

      Lemma five_r :
        forall alpha u t alpha',
          ipurge_r alpha u t alpha' ->
          forall s,
            eqv_r_list (sources_r alpha u s) s t ->
            eqv_r u (run_r s alpha) (run_r t alpha').
      Proof.
        intros alpha u t alpha' H.
        induction H; intros.
        - simpl.
          unfold eqv_r_list in *.
          apply H.
          constructor.
        - unfold eqv_r_list in *.
          apply IHipurge_r; auto.
          apply three_r; auto.
        - apply IHipurge_r; auto.
          apply four_r in H.

          unfold eqv_r_list in *.
          intros.
          eapply eqv_r_trans with (y := (step_r s a)); auto.
          * eapply three_r; eauto.
          * apply eqv_r_sym.
            apply H.
            eapply source_consistent_r with (s := step_r s0 a); eauto.
            apply three_r; auto.
      Qed.

      Definition nonleakage_r :=
        forall (alpha: list A) s t u,
          eqv_r_list (sources_r alpha u s) s t ->
          output u (projT1 (run_r s alpha)) = output u (projT1 (run_r t alpha)).

      Definition noninfluence_r :=
        forall (alpha alpha': list A) s t u,
          eqv_r_list (sources_r alpha u s) s t ->
          ipurge_r alpha u t alpha' ->
          output u (projT1 (run_r s alpha)) = output u (projT1 (run_r t alpha')).

      Lemma eqv_r_list_refl :
        forall C s,
          eqv_r_list C s s.
      Proof.
        unfold eqv_r_list.
        intros.
        apply eqv_r_refl.
      Qed.

      Lemma noninfluence_r_noninterference_r :
        noninfluence_r -> noninterference_r.
      Proof.
        unfold noninfluence_r, noninterference_r.
        intros.
        subst s s'.
        apply H; try (apply Reachable_init); auto.
        apply eqv_r_list_refl.
      Qed.

      Lemma ipurge_r_refl :
        forall alpha u s,
          ipurge_r alpha u s alpha.
      Proof.
        induction alpha; intros; constructor; auto.
      Qed.

      Lemma noninfluence_r_nonleakage_r :
        noninfluence_r -> nonleakage_r.
      Proof.
        unfold noninfluence_r, nonleakage_r.
        intros.
        eapply H; eauto.
        apply ipurge_r_refl.
      Qed.

      Theorem noninfluence_unwinding_r :
        noninfluence_r.
      Proof.
        unfold noninfluence_r.
        intros.
        apply output_consistency_r.
        apply five_r; auto.
      Qed.

      Theorem noninterference_unwinding_r :
        noninterference_r.
      Proof.
        apply noninfluence_r_noninterference_r.
        apply noninfluence_unwinding_r.
      Qed.

      Theorem nonleakage_unwinding_r :
        nonleakage_r.
      Proof.
        unfold nonleakage_r, eqv_r_list.
        induction alpha; intros.
        - apply output_consistency_r.
          apply H.
          constructor.
        - apply IHalpha; auto.
          intros.
          destruct (interferes (dom_r a s) u0) eqn:?.
          + apply weak_step_consistency_r; auto.
            apply H.
            now constructor.
            apply H.
            eapply sources_r_contains; eauto.
          + apply step_respect_r; auto.
            apply H.
            now constructor.
      Qed.

      Definition transitive_nonleakage_r :=
        forall alpha s t u,
          eqv_r u s t ->
          eqv_r u (run_r s alpha) (run_r t alpha).

      Theorem transitive_nonleakage_unwinding_r :
        transitive_nonleakage_r.
      Proof.
        unfold transitive_nonleakage_r.
        induction alpha; intros.
        - auto.
        - apply IHalpha; auto.
      Qed.

    End Unwinding.
  End Intransitive.
End ReachableNoninterference.

Section NI_NIR.

  Lemma sources_sources_r :
    forall M alpha dom dom_r,
      (forall (sr: SR) a,
          dom a (projT1 sr) = dom_r a sr) ->
      forall sr u u',
        sources M dom alpha u (projT1 sr) u' ->
        sources_r M dom_r alpha u sr u'.
  Proof.
    intros M alpha dom dom_r dom_consistent.
    induction alpha; intros.
    - inversion H. subst.
      apply sources_r_has_u.
    - inversion H.
      + subst.
        apply sources_r_recurse.
        eapply IHalpha with (sr := (step_r sr a)); eauto.
        rewrite step_r_step.
        apply H5.
      + rewrite dom_consistent.
        apply sources_r_contains with (v := v).
        {
          apply IHalpha.
          rewrite step_r_step.
          apply H2.
        }
        {
          subst.
          now rewrite <- dom_consistent.
        }
  Qed.

  Lemma sources_r_sources :
    forall M alpha dom dom_r,
      (forall (sr: SR) a,
          dom a (projT1 sr) = dom_r a sr) ->
      forall sr u u',
        sources_r M dom_r alpha u sr u' ->
        sources M dom alpha u (projT1 sr) u'.
  Proof.
    intros M alpha dom dom_r dom_consistent.
    induction alpha; intros.
    - inversion H. subst.
      apply sources_has_u.
    - inversion H.
      + subst.
        apply sources_recurse.
        rewrite <- step_r_step.
        apply IHalpha.
        apply H5.
      + rewrite <- dom_consistent.
        apply sources_contains with (v := v).
        {
          rewrite <- step_r_step.
          apply IHalpha.
          apply H2.
        }
        {
          subst.
          now rewrite dom_consistent.
        }
  Qed.

  Lemma ipurge_ipurge_r :
    forall M dom dom_r,
      (forall (sr: SR) a,
          dom a (projT1 sr) = dom_r a sr) ->
      forall alpha alpha' (sr sr': SR) u,
        ipurge M dom alpha u (projT1 sr') alpha' ->
        ipurge_r M dom_r alpha u sr' alpha'.
  Proof.
    intros M dom dom_r dom_consistent.
    induction alpha; intros; inversion H; subst.
    - apply ipurge_r_nil.
    - apply ipurge_r_nopurge.
      apply IHalpha; auto.
      rewrite step_r_step.
      apply H5.
    - apply ipurge_r_purge; auto.
      unfold not in *.
      intros.
      apply H2.
      eapply sources_r_sources with (alpha := a :: alpha) in H0; auto.
      rewrite dom_consistent.
      apply H0.
  Qed.

  Hint Resolve Reachable_init Reachable_step.

  Lemma noninfluence_r_noninfluence :
    forall M dom dom_r eqv eqv_r,
      (forall (sr: SR) a,
          dom a (projT1 sr) = dom_r a sr) ->
      (forall (sr tr: SR) d,
          eqv d (projT1 sr) (projT1 tr) = eqv_r d sr tr) ->
      noninfluence_r M dom_r eqv_r ->
      noninfluence M dom eqv.
  Proof.
    unfold noninfluence_r, noninfluence.
    intros M dom dom_r eqv eqv_r dom_consistent eqv_consistent.
    intuition.
    specialize H with (s := existT _ s H0)
                      (t := existT _ t H1)
                      (alpha := alpha)
                      (alpha' := alpha')
                      (u := u).
    repeat (erewrite <- eqv_consistent in H).
    repeat (rewrite run_r_run in H).
    repeat (erewrite <- proj_s in H).
    apply H.
    unfold eqv_r_list in *.
    intros.
    rewrite <- eqv_consistent.
    apply H2.
    assert (s = (projT1 (existT _ s H0))); auto.
    rewrite H5.
    eapply sources_r_sources; auto.
    assert (t = (projT1 (existT _ t H1))); auto.
    rewrite H4 in H3.
    simpl in H3.
    eapply ipurge_ipurge_r; auto.
    exists init; auto.
  Qed.

  Lemma noninterference_r_noninterference :
    forall M dom dom_r,
      (forall (sr: SR) a,
          dom a (projT1 sr) = dom_r a sr) ->
      noninterference_r M dom_r ->
      noninterference M dom.
  Proof.
    unfold noninterference, noninterference_r.
    intros M dom dom_r dom_consistent.
    intuition.
    subst.
    specialize H with (s := run_r init_r alpha)
                      (s' := run_r init_r alpha')
                      (alpha := alpha)
                      (alpha' := alpha').
    rewrite run_r_run in H.
    rewrite run_r_run in H.
    rewrite proj_init_r in H.
    apply H; auto.
    eapply ipurge_ipurge_r; eauto.
    exists init; auto.
  Qed.

  Lemma nonleakage_r_nonleakage :
    forall M dom dom_r eqv eqv_r,
      (forall (sr: SR) a,
          dom a (projT1 sr) = dom_r a sr) ->
      (forall (sr tr: SR) d,
          eqv d (projT1 sr) (projT1 tr) = eqv_r d sr tr) ->
      nonleakage_r M dom_r eqv_r ->
      nonleakage M dom eqv.
  Proof.
    unfold nonleakage_r, nonleakage.
    intros M dom dom_r eqv eqv_r dom_consistent eqv_consistent.
    intuition.
    specialize H with (s := existT _ s H0)
                      (t := existT _ t H1)
                      (alpha := alpha)
                      (u := u).
    rewrite run_r_run in H.
    rewrite run_r_run in H.
    erewrite <- proj_s in H.
    erewrite <- proj_s in H.
    apply H.
    unfold eqv_r_list.
    unfold eqv_list in H2.
    intros.
    rewrite <- eqv_consistent.
    apply H2.
    assert (s = (projT1 (existT _ s H0))); auto.
    rewrite H4.
    eapply sources_r_sources; auto.
  Qed.

  Lemma transitive_nonleakage_r_transitive_nonleakage :
    forall M eqv eqv_r,
      (forall (sr tr: SR) d,
          eqv d (projT1 sr) (projT1 tr) = eqv_r d sr tr) ->
      transitive_nonleakage_r M eqv_r ->
      transitive_nonleakage M eqv.
  Proof.
    unfold transitive_nonleakage_r, transitive_nonleakage.
    intros M eqv eqv_r eqv_consistent.
    intuition.
    assert (s = (projT1 (existT _ s H0))); auto.
    assert (t = (projT1 (existT _ t H1))); auto.
    rewrite H3.
    rewrite H5.
    rewrite <- run_r_run.
    rewrite <- run_r_run.
    rewrite eqv_consistent.
    apply H.
    rewrite <- eqv_consistent.
    rewrite <- proj_s.
    rewrite <- proj_s.
    auto.
  Qed.
End NI_NIR.

Section Refinement.
  Variable Spec : M.
  Variable Impl : M.

  Variable sim : (@S Impl) -> (@S Spec) -> Prop.

  Notation "s0 ~ s1" := (sim s0 s1) (at level 10).

  Hypothesis sim_init :
    init ~ init.

  Hypothesis sim_step:
    forall (i: @S Impl) (s: @S Spec) a,
      safe i ->
      i ~ s ->
      (step i a) ~ (step s a).

  Hypothesis sim_output :
    forall i s u,
      safe i ->
      i ~ s ->
      output u i = output u s.

  Hint Resolve sim_init sim_step sim_output.

  Hint Resolve safe_init safe_run.

  Lemma bisimulation_do :
    forall alpha,
    @do Impl alpha ~ @do Spec alpha.
  Proof.
    unfold do; induction alpha using rev_ind; simpl; intros; auto.
    repeat (rewrite do_run; auto).
  Qed.

  Lemma bisimulation :
    forall alpha u,
    output u (@do Impl alpha) = output u (@do Spec alpha).
  Proof.
    intros.
    apply sim_output; auto.
    - unfold do; auto.
    - apply bisimulation_do.
  Qed.

  Hint Resolve reachable_safe.

  Definition abs (i: @SR Impl) : (@SR Spec) :=
    do_r (extract_trace_r i).

  Lemma abs_sim :
    forall (i: SR),
      (projT1 i) ~ (projT1 (abs i)).
  Proof.
    intros.
    destruct i as [s r].
    unfold abs, do_r, extract_trace_r.
    induction r; simpl; auto.
    rewrite do_run_r.
    rewrite do_extract_r.
    rewrite <- do_extract_r.
    rewrite step_r_step.
    apply sim_step; auto.
  Qed.

  Lemma abs_step :
    forall i a,
      abs (step_r i a) = step_r (abs i) a.
  Proof.
    intros.
    destruct i as [s r].
    unfold abs, do_r.
    induction r; simpl; auto.
    rewrite do_run_r.
    auto.
  Qed.

  Section ImplementationNoninterference.

    Variable spec_dom : A -> (@S Spec) -> D.
    Variable spec_eqv : D -> (@S Spec) -> (@S Spec) -> Prop.

    Hypothesis eqv_refl : forall d, reflexive (spec_eqv d).
    Hypothesis eqv_sym : forall d, symmetric (spec_eqv d).
    Hypothesis eqv_trans : forall d, transitive (spec_eqv d).

    Hint Resolve eqv_refl eqv_sym eqv_trans.

    Definition impl_dom (a: A) (sr: SR) : D :=
      spec_dom a (projT1 (abs sr)).

    Definition impl_eqv (u: D) (sr tr: SR) : Prop :=
      spec_eqv u (projT1 (abs sr)) (projT1 (abs tr)).

    Hypothesis spec_dom_consistency : dom_consistency Spec spec_dom spec_eqv.
    Hypothesis spec_dom_respect : dom_respect Spec spec_dom spec_eqv.
    Hypothesis spec_output_consistency : output_consistency Spec spec_eqv.
    Hypothesis spec_local_respect : local_respect Spec spec_dom spec_eqv.
    Hypothesis spec_weak_step_consistency : weak_step_consistency Spec spec_dom spec_eqv.
    Hypothesis spec_step_consistency : step_consistency Spec spec_eqv.
    Hypothesis spec_step_respect : step_respect Spec spec_dom spec_eqv.

    Hint Resolve safe_r.

    Lemma impl_dom_consistency :
      dom_consistency_r Impl impl_dom impl_eqv.
    Proof.
      unfold dom_consistency_r.
      eauto.
    Qed.

    Lemma impl_dom_respect :
      dom_respect_r Impl impl_dom impl_eqv.
    Proof.
      unfold dom_respect_r.
      eauto.
    Qed.

    Hint Resolve safe_r abs_sim.

    Lemma impl_output_consistency :
      output_consistency_r Impl impl_eqv.
    Proof.
      unfold output_consistency_r.
      intros.
      rewrite sim_output with (s := projT1 (abs s)); eauto.
      rewrite sim_output with (s := projT1 (abs t)); eauto.
    Qed.

    Lemma impl_local_respect :
      local_respect_r Impl impl_dom impl_eqv.
    Proof.
      unfold local_respect_r.
      intros.
      unfold impl_eqv.
      rewrite abs_step.
      rewrite step_r_step.
      auto.
    Qed.

    Lemma impl_weak_step_consistency :
      weak_step_consistency_r Impl impl_dom impl_eqv.
    Proof.
      unfold weak_step_consistency_r.
      intros.
      unfold impl_eqv.
      repeat (rewrite abs_step).
      repeat (rewrite step_r_step).
      auto.
    Qed.

    Lemma impl_step_consistency :
      step_consistency_r Impl impl_eqv.
    Proof.
      unfold step_consistency_r.
      intros.
      unfold impl_eqv.
      repeat (rewrite abs_step).
      repeat (rewrite step_r_step).
      auto.
    Qed.

    Lemma impl_step_respect :
      step_respect_r Impl impl_dom impl_eqv.
    Proof.
      unfold step_respect_r.
      intros.
      unfold impl_eqv.
      repeat (rewrite abs_step).
      repeat (rewrite step_r_step).
      auto.
    Qed.

    Lemma impl_noninfluence_r :
      noninfluence_r Impl impl_dom impl_eqv.
    Proof.
      apply (noninfluence_unwinding_r Impl impl_dom impl_eqv).
      - unfold impl_eqv; intros; now apply eqv_sym.
      - intros. unfold impl_eqv in *; eapply eqv_trans. eauto. eauto.
      - apply impl_dom_consistency.
      - apply impl_dom_respect.
      - apply impl_output_consistency.
      - apply impl_local_respect.
      - apply impl_weak_step_consistency.
    Qed.

    Lemma impl_noninterference_r :
      noninterference_r Impl impl_dom.
    Proof.
      apply noninfluence_r_noninterference_r with (eqv_r := impl_eqv); auto.
      - unfold impl_eqv; intros; apply eqv_refl.
      - apply impl_noninfluence_r.
    Qed.

    Lemma impl_nonleakage_r :
      nonleakage_r Impl impl_dom impl_eqv.
    Proof.
      apply (nonleakage_unwinding_r Impl impl_dom impl_eqv).
      - apply impl_output_consistency.
      - apply impl_weak_step_consistency.
      - apply impl_step_respect.
    Qed.

    Lemma impl_transitive_nonleakage_r :
      transitive_nonleakage_r Impl impl_eqv.
    Proof.
      apply (transitive_nonleakage_unwinding_r Impl impl_eqv).
      - unfold impl_eqv; intros; now apply eqv_sym.
      - apply impl_step_consistency.
    Qed.

    (***************)

    Theorem impl_noninfluence:
      forall dom eqv,
        (forall ir a,
            dom a (projT1 ir) = impl_dom a ir) ->
        (forall d ir jr,
            eqv d (projT1 ir) (projT1 jr) = impl_eqv d ir jr) ->
        noninfluence Impl dom eqv.
    Proof.
      intros.
      eapply noninfluence_r_noninfluence; auto.
      apply impl_noninfluence_r.
    Qed.

    Theorem impl_nonleakage:
      forall dom eqv,
        (forall ir a,
            dom a (projT1 ir) = impl_dom a ir) ->
        (forall d ir jr,
            eqv d (projT1 ir) (projT1 jr) = impl_eqv d ir jr) ->
        nonleakage Impl dom eqv.
    Proof.
      intros.
      eapply nonleakage_r_nonleakage; auto.
      apply impl_nonleakage_r.
    Qed.

    Theorem impl_transitive_nonleakage :
      forall eqv,
        (forall d ir jr,
            eqv d (projT1 ir) (projT1 jr) = impl_eqv d ir jr) ->
        transitive_nonleakage Impl eqv.
    Proof.
      intros.
      eapply transitive_nonleakage_r_transitive_nonleakage; auto.
      apply impl_transitive_nonleakage_r.
    Qed.

    Theorem impl_noninterference :
      forall dom,
        (forall ir a,
            dom a (projT1 ir) = impl_dom a ir) ->
        noninterference Impl dom.
    Proof.
      intros.
      eapply noninterference_r_noninterference; auto.
      apply impl_noninterference_r.
    Qed.
  End ImplementationNoninterference.
End Refinement.

End Policy.

  Section Monotonicity.

    Variable m: M.
    Variable dom: A -> S -> D.

    Hint Resolve ipurge_nil ipurge_purge ipurge_nopurge.

    Definition restrictive (p q: D -> D -> bool) : Prop :=
      forall u v, (p u v = true) -> (q u v = true).

    Lemma sources_monotonicity :
      forall interferes interferes' alpha u s v,
        restrictive interferes interferes' ->
        sources interferes _ dom alpha u s v ->
        sources interferes' _ dom alpha u s v.
   Proof.
     unfold restrictive.
     induction alpha; intros.
     - inversion H0.
       constructor.
     - inversion H0; subst.
       + apply sources_recurse.
         apply IHalpha; auto.
       + apply sources_contains with (v := v0).
         apply IHalpha; auto.
         apply H; auto.
    Qed.

    Lemma sources_monotonicity_inv :
      forall interferes interferes' alpha u s v,
        restrictive interferes interferes' ->
        ~ sources interferes' _ dom alpha u s v ->
        ~ sources interferes _ dom alpha u s v.
   Proof.
     unfold restrictive.
     induction alpha; intros; intuition; auto.
     - apply H0.
       eapply sources_monotonicity; eauto.
     - apply H0.
       eapply sources_monotonicity with (interferes := interferes); auto.
    Qed.

   Lemma ipurge_monotonicity :
      forall interferes interferes' alpha alpha' u s,
        restrictive interferes interferes' ->
        ipurge interferes' _ dom alpha u s alpha' ->
        ipurge interferes _ dom alpha u s alpha'.
   Proof.
     induction alpha.
     intros.
     - inversion H0; auto.
     - intros.
       inversion H0; subst.
       + apply ipurge_nopurge; eauto.
       + apply sources_monotonicity_inv with (interferes := interferes) in H3; auto.
   Qed.

    Lemma noninterference_monotonicity :
      forall interferes interferes',
        restrictive interferes interferes' ->
        noninterference interferes _ dom ->
        noninterference interferes' _ dom.
    Proof.
      unfold noninterference, restrictive.
      intros.
      eapply H0 with (alpha := alpha) (alpha' := alpha'); auto.
      eapply ipurge_monotonicity in H3; eauto.
    Qed.

  End Monotonicity.

End Metasystem.

Check impl_noninfluence.
Print Assumptions impl_noninfluence.
Check impl_noninterference.
Print Assumptions impl_noninterference.
Check impl_nonleakage.
Print Assumptions impl_nonleakage.
Check impl_transitive_nonleakage.
Print Assumptions impl_transitive_nonleakage.
