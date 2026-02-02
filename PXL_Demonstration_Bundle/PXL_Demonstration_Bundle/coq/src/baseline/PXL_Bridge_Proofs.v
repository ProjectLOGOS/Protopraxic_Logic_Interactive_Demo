From PXL Require Import PXL_Foundations PXLv3.

Definition Coherent (P : Prop) := Coherence P.
Definition TrueAtRoot (P : Prop) := Truth P.

Parameter domain_product : Obj -> Obj -> Obj.
Infix " ⊗ " := domain_product (at level 40, left associativity).

(* Domain product preserves coherence in its left argument; coherence
   propagates across modal boundaries when the originating domain is
   coherent. *)
Axiom domain_product_coherence_left :
  forall X Y : Obj,
    coherence X ->
    coherence (X ⊗ Y).

(* Symmetric domain-product bridge: coherence inherited from the
   right-hand domain also persists through the tensor. *)
Axiom domain_product_coherence_right :
  forall X Y : Obj,
    coherence Y ->
    coherence (X ⊗ Y).

(* Coherence inherited by each hypostasis when 𝕆 is coherent. *)
Axiom triune_coherence_hypostases :
  coherence 𝕆 ->
  coherence 𝕀₁ /\ coherence 𝕀₂ /\ coherence 𝕀₃.

Lemma coherence_I1 :
  coherence 𝕆 -> coherence 𝕀₁.
Proof.
  intro HcohO.
  destruct (triune_coherence_hypostases HcohO) as [H _].
  exact H.
Qed.

Lemma coherence_I2 :
  coherence 𝕆 -> coherence 𝕀₂.
Proof.
  intro HcohO.
  destruct (triune_coherence_hypostases HcohO) as [_ [H _]].
  exact H.
Qed.

Lemma coherence_I3 :
  coherence 𝕆 -> coherence 𝕀₃.
Proof.
  intro HcohO.
  destruct (triune_coherence_hypostases HcohO) as [_ [_ H]].
  exact H.
Qed.

Lemma coherence_entails_truth :
  forall P : Prop,
    Coherent P -> TrueAtRoot P.
Proof.
  intros P Hcoh.
  apply (proj2 (truth_coherence_equiv P)).
  exact Hcoh.
Qed.

Lemma truth_entails_coherence :
  forall P : Prop,
    TrueAtRoot P -> Coherent P.
Proof.
  intros P Htrue.
  apply (proj1 (truth_coherence_equiv P)).
  exact Htrue.
Qed.

Lemma coherence_O :
  coherence 𝕆.
Proof.
  apply (ax_T (p:=coherence 𝕆)).
  exact A7_triune_necessity.
Qed.

Lemma coherence_I1_global :
  coherence 𝕀₁.
Proof.
  apply coherence_I1.
  exact coherence_O.
Qed.

Lemma coherence_I2_global :
  coherence 𝕀₂.
Proof.
  apply coherence_I2.
  exact coherence_O.
Qed.

Lemma coherence_I3_global :
  coherence 𝕀₃.
Proof.
  apply coherence_I3.
  exact coherence_O.
Qed.

