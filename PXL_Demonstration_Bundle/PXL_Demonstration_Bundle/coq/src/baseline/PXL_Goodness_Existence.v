From PXL Require Import PXL_Foundations PXL_Privative.

Lemma goodness_entails_existence :
  forall P : Prop, Goodness P -> Existence P.
Proof.
  intros P HG.
  apply (proj1 (goodness_existence_equiv P)).
  exact HG.
Qed.

Lemma existence_entails_goodness :
  forall P : Prop, Existence P -> Goodness P.
Proof.
  intros P HE.
  apply (proj2 (goodness_existence_equiv P)).
  exact HE.
Qed.
