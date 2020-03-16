Require Import Nat.
Require Import PeanoNat.
Require Import List.

Record S : Set := { global: nat; current : nat }.
Inductive D : Set := Proc : nat -> D | Sched : D.
Inductive A : Set := Read : nat -> A | Write : nat -> nat -> A | Schedule : nat -> A.
Definition O : Set := nat.

Definition step (s: S) (a: A) : S :=
  match a with
  | Read cur => s
  | Write cur x => if Nat.eq_dec cur (current s)
                  then Build_S x (current s)
                  else s
  | Schedule x => Build_S (global s) x
  end.

Definition output (s: S) (a: A) : O :=
  match a with
  | Read cur => if Nat.eq_dec cur (current s)
           then global s else 0
  | _ => 0
  end.

Definition dom (a: A) : D :=
  match a with
  | Schedule _ => Sched
  | Read cur => Proc cur
  | Write cur _ => Proc cur
  end.

Definition init : S := Build_S 1 1 .

Definition interferes (d1 d2: D) : bool :=
  match d1, d2 with
  | Sched, _ => true
  | _, Sched => true
  | Proc n, Proc m => if Nat.eq_dec n m then true else false
  end.

Inductive tree : Set :=
| Empty : tree
| Node : tree -> tree -> A -> tree.

Fixpoint att (a: A) (u: D) (t: tree) :=
  match t with
  | Empty => if interferes (dom a) u
            then Node Empty Empty a 
            else Empty
  | Node t t' b => Node (att a u t) (att a (dom b) t') b
  end.

Fixpoint ta_reverse (u: D) (a: list A) : tree :=
  match a with
  | nil => Empty
  | x :: xs =>
    if interferes (dom x) u
    then Node (ta_reverse u xs) (ta_reverse (dom x) xs) x
    else ta_reverse u xs
  end.

Definition ta (u: D) (a: list A) : tree := ta_reverse u (rev a).

Fact ta_att : (* This doesn't matter, just kind of fun *)
  forall alpha u a,
    ta u (a :: alpha) = att a u (ta u alpha).
Proof.
  induction alpha; intros; auto.
  rewrite IHalpha.
  unfold ta; simpl.
  clear IHalpha.
  revert u.
  revert a0 a.
  induction alpha using rev_ind; intros.
  - simpl; auto.
    destruct (interferes (dom a) u) eqn:?; simpl; auto.
  - simpl.
    rewrite rev_app_distr.
    simpl.
    destruct (interferes (dom x) u) eqn:?; simpl; auto.
    rewrite IHalpha.
    f_equal.
    rewrite IHalpha; auto.
Qed.

Definition do (l: list A) : S := fold_left step l init.

Definition eqv (d: D) (s t: S) : Prop :=
  match d with
  | Sched => (global s) = (global t) /\ (current s) = (current t)
  | Proc n =>
      (current s) = (current t) /\
      (current s = n -> global s = global t)
  end.

Lemma eqv_refl : forall d u, eqv u d d.
Proof.
  intros; destruct u; simpl; auto.
Qed.


Theorem local_respect :
  forall a s u,
    interferes (dom a) u = false ->
    eqv u s (step s a).
Proof.
  destruct a; intros.
  - simpl; auto.
    apply eqv_refl.
  - simpl in H.
    destruct u.
    + destruct (Nat.eq_dec n n1) eqn:?; try congruence.
      simpl.
      split.
      destruct (Nat.eq_dec n (current s)) eqn:?; try congruence.
      now simpl.
      intros.
      destruct (Nat.eq_dec n (current s)) eqn:?; simpl; try congruence.
      subst; congruence.
    + congruence.
  - simpl in H; congruence.
Qed.

Theorem output_consistency :
  forall a s t,
    eqv (dom a) s t ->
    output s a = output t a.
Proof.
  intros; destruct a; simpl; auto.
  simpl in H.
  destruct H; subst.
  destruct (Nat.eq_dec n (current s)) eqn:?; simpl; auto; subst.
  - rewrite H; simpl.
    rewrite H0; auto.
    destruct (Nat.eq_dec (current t) (current t)); try congruence.
  - destruct (Nat.eq_dec n (current t)); auto.
    congruence.
Qed.

Theorem eqv_trans :
  forall u s t v,
   eqv u s t ->
   eqv u t v ->
   eqv u s v.
Proof.
  destruct u; intros; simpl.
  - simpl in *.
    destruct H, H0.
    split; try congruence.
    intros; try congruence.
    rewrite H1; auto.
    apply H2; auto.
    congruence.
  - simpl in *; split; try congruence; destruct H, H0; congruence.
Qed.

Theorem eqv_sym :
  forall u s t,
    eqv u s t ->
    eqv u t s.
Proof.
  destruct u; intros; simpl in *.
  - split; destruct H; simpl; try congruence.
    rewrite <- H.
    intros.
    rewrite <- H0; auto.
  - split; destruct H; congruence.
Qed.

Theorem weak_step_consistency :
  forall u s t a,
    eqv u s t ->
    eqv (dom a) s t ->
    eqv u (step s a) (step t a).
Proof.
  intros; destruct a.
  - simpl in *; auto.
  - simpl in *.
    destruct H0.
    rewrite H0.
    destruct (Nat.eq_dec n (current t)) eqn:?; auto.
    apply eqv_refl.
  - simpl in *.
    destruct H0 as [a b]; rewrite a.
    apply eqv_refl.
Qed.

