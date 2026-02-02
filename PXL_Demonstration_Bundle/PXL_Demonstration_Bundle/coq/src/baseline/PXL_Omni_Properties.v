(************************************************************************)
(*  PXL_Omni_Properties.v                                               *)
(*  Omni-property foundations (definitions + grounding tags, no proofs) *)
(************************************************************************)

From Stdlib Require Import Unicode.Utf8.
From PXL Require Import PXL_Definitions PXL_Modal_Axioms_Semantic PXL_Kernel_Axioms.

Module PXL_Omni_Properties.

  (*** Uninterpreted primitives introduced by the omni layer ***)
  Parameter Truth  : Prop -> Prop.
  Parameter Wills  : Obj -> Prop -> Prop.
  Parameter Good   : Prop -> Prop.

  (*** Coherence guard used by Omnipotence ***)
  Definition Coherent (φ : Prop) : Prop := ~ incoherent φ.

  (*** Omni property definitions (PXL-typed, Prop-level modal operators) ***)
  Definition Omniscient (x : Obj) : Prop :=
    □ (forall p : Prop, Truth p -> K x p).

  Definition Omnibenevolent (x : Obj) : Prop :=
    □ (forall φ : Prop, Wills x φ -> Good φ).

  Definition Omnipresent (x : Obj) : Prop :=
    □ (forall w : Obj, x ⇌ w).

  Definition Omnipotent (x : Obj) : Prop :=
    □ (forall φ : Prop, Coherent φ -> ◇ (entails x φ)).

  (*** Grounding tags (kept as axioms/placeholders) ***)
  Axiom OP1_ground : grounded_in (Omniscient 𝕆) 𝕀₁.
  Axiom OP2_ground : grounded_in (Omnibenevolent 𝕆) 𝕀₂.
  Axiom OP3_ground : grounded_in (Omnipresent 𝕆) 𝕀₃.
  Axiom OP4_ground : grounded_in (Omnipotent 𝕆) 𝕆.

End PXL_Omni_Properties.
