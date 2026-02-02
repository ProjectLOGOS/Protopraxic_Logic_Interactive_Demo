From PXL Require Import PXLv3 PXL_Foundations PXL_Bridge_Proofs.

Import PXLv3.

Axiom non_equiv_privative_equiv :
  forall (x y : Obj), x ⇎ y <-> ~ (◇ (x ⧟ y)).

Lemma non_equiv_implies_no_possibility :
  forall x y, x ⇎ y -> ~ (◇ (x ⧟ y)).
Proof.
  intros x y Hneq.
  apply (proj1 (non_equiv_privative_equiv x y)).
  exact Hneq.
Qed.

Lemma no_possibility_implies_non_equiv :
  forall x y, ~ (◇ (x ⧟ y)) -> x ⇎ y.
Proof.
  intros x y Hno.
  apply (proj2 (non_equiv_privative_equiv x y)).
  exact Hno.
Qed.

Theorem privative_collapse_sound :
  forall (P : Prop), ~ (◇ (entails 𝕆 P)) -> incoherent P.
Proof.
  intros P H.
  apply privative_collapse; auto.
Qed.
