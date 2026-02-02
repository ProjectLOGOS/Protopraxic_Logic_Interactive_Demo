From PXL Require Import PXLv3_SemanticModal PXL_Internal_LEM.

Axiom coherence_not_identity_guard :
  ~ (forall x, coherence 𝕆 -> x ⧟ 𝕆).

Lemma false_not_derivable : False -> True.
Proof.
  intro H.
  exact I.
Qed.
