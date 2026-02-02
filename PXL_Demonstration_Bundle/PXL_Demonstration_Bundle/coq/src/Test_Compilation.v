(** Test file to verify jsCoq compilation works **)

Definition test_identity (A : Type) (x : A) : A := x.

Lemma test_trivial : True.
Proof.
  exact I.
Qed.

Lemma test_reflexivity : forall (x : nat), x = x.
Proof.
  intros x.
  reflexivity.
Qed.
