Set Implicit Arguments.
Generalizable All Variables.

Parameter Box : Prop -> Prop.
Notation "□ p" := (Box p) (at level 75).

Axiom ax_K : forall p q:Prop, □ (p -> q) -> (□ p -> □ q).

Lemma K_sound (p q:Prop) : (□ (p -> q)) -> (□ p -> □ q).
Proof.
  exact (fun (H:□ (p -> q)) (Hp:□ p) => ax_K (p:=p) (q:=q) H Hp).
Qed.
