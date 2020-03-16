
Section Reduction.

  (* The state of the system (MonitorState) in state.py *)
  Variable state: Type.

  (* Observable equivalence of states.
     Depends on the observer in the python,
     but is irrelevant here.
   *)
  Variable eq: state -> state -> Prop.

  (* eq is an equivalence relation. *)
  Hypothesis eq_refl: forall x, eq x x.
  Hypothesis eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Hypothesis eq_symm: forall x y, eq x y -> eq y x.

  (* It's sufficient to show that each function on the state
     preserves equivalence to show noninterference.
     This works because when the OS does a hypercall, that hypercall
     cannot change the observable state of a sealed enclave.
     This means that whatever pair of states or pair of hypercalls we use,
     that will preserve equivalence.
     see vmm/verif/noninterference/test.py for where this reduction is used
     to make proof complexity linear in number of hypercalls rather than quadratic.
   *)
  Theorem reduce_proof_to_linear :
    forall f g,
      (forall s, eq s (f s)) ->
      (forall s, eq s (g s)) ->
      (forall s1 s2, (eq s1 s2) -> eq (f s1) (g s2)).
  Proof.
    intros f g H H0 s1 s2 H1.
    eapply eq_trans.
    apply eq_symm.
    apply H.
    eapply eq_trans.
    exact H1.
    apply H0.
  Qed.

End Reduction.
