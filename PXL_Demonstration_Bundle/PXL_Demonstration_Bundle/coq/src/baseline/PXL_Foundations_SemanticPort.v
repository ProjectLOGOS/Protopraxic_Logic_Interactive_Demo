From Stdlib Require Import Classical.
From PXL Require Import PXLv3_SemanticModal.

Section PXL_Foundations.

Axiom identity_axiom : forall (A : Type) (x : A), x = x.
Axiom non_contradiction_axiom : forall P : Prop, ~ (P /\ ~ P).
Axiom excluded_middle_axiom : forall P : Prop, P \/ ~ P.

Parameter Truth : Prop -> Prop.
Parameter Coherence : Prop -> Prop.

(** Canonical object-level representative for each proposition. *)
Parameter anchor_obj : Prop -> Obj.

(** Truth/coherence correspondence at the canonical anchor. *)
Axiom truth_coherence_anchor :
  forall P : Prop,
    coherence (anchor_obj P) <-> Truth P.

(* NOTE:
   Coherence is treated as invariant across the object-level identity
   relation (⧟).  The axiom stated below captures this design choice so
   coherence can be reasoned about on Ident-equivalence classes.
 *)

Axiom truth_coherence_equiv : forall P : Prop, Truth P <-> Coherence P.

Parameter Goodness : Prop -> Prop.
Parameter Existence : Prop -> Prop.

Axiom goodness_existence_equiv : forall P : Prop, Goodness P <-> Existence P.

Lemma excluded_middle :
  forall P : Prop, P \/ ~ P.
Proof.
  apply excluded_middle_axiom.
Qed.

Lemma excluded_middle_implies_trinitarian_decidability :
  forall P : Prop, P \/ ~ P.
Proof.
  apply excluded_middle_axiom.
Qed.

End PXL_Foundations.

(* Kernel axiom: coherence is preserved along Ident equivalence. *)
Axiom coherence_respects_ident :
  forall x y : Obj,
    x ⧟ y ->
    coherence x ->
    coherence y.
