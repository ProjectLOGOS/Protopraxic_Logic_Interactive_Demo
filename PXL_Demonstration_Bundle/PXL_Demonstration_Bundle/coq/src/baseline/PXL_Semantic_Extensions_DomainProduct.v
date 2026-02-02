(*
  PXL_Semantic_Extensions_DomainProduct.v

  Explicit EXTENSIONS layer (not part of Kernel17).
  Any new axioms/parameters beyond the Kernel17 semantic profile must live here.
*)

From PXL Require Import PXL_Foundations_SemanticPort PXLv3_SemanticModal.

Parameter domain_product : Obj -> Obj -> Obj.
Infix " ⊗ " := domain_product (at level 40, left associativity).

Axiom domain_product_coherence_left :
  forall X Y : Obj,
    coherence X ->
    coherence (X ⊗ Y).

Axiom domain_product_coherence_right :
  forall X Y : Obj,
    coherence Y ->
    coherence (X ⊗ Y).

Axiom triune_coherence_hypostases :
  coherence 𝕆 ->
  coherence 𝕀₁ /\ coherence 𝕀₂ /\ coherence 𝕀₃.
