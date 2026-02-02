(************************************************************************)
(*  PXL_OntoGrid.v                                                      *)
(*  Minimal OntoGrid scaffold (gated)                                   *)
(************************************************************************)

From Stdlib Require Import Unicode.Utf8.
From PXL Require Import
  PXL_Kernel_Axioms
  PXL_Triune_Principles
  PXL_Omni_Properties
  PXL_Omni_Bridges.

Inductive Axis : Type :=
  | Truth
  | Goodness
  | Presence
  | Power.

Definition AxisTarget (a : Axis) : Obj :=
  match a with
  | Truth    => 𝕀₁
  | Goodness => 𝕀₂
  | Presence => 𝕀₃
  | Power    => 𝕆
  end.

Definition AxisPrinciple (a : Axis) : Principle :=
  match a with
  | Truth    => Sign
  | Goodness => Bridge
  | Presence => Mind
  | Power    => Mesh
  end.

Inductive IELDomain : Type :=
  | OntoPraxis
  | TheoPraxis
  | CosmoPraxis
  | MathPraxis
  | AnthroPraxis.

Definition DomainProfile (d : IELDomain) : Axis -> option Obj :=
  match d with
  | OntoPraxis =>
      fun a =>
        match a with
        | Truth => Some 𝕀₁
        | Presence => Some 𝕀₃
        | _ => None
        end
  | TheoPraxis =>
      fun a =>
        match a with
        | Truth => Some 𝕀₁
        | Goodness => Some 𝕀₂
        | _ => None
        end
  | CosmoPraxis =>
      fun a =>
        match a with
        | Presence => Some 𝕀₃
        | Power => Some 𝕆
        | _ => None
        end
  | MathPraxis =>
      fun a =>
        match a with
        | Truth => Some 𝕀₁
        | Goodness => Some 𝕀₂
        | _ => None
        end
  | AnthroPraxis =>
      fun a =>
        match a with
        | Goodness => Some 𝕀₂
        | Presence => Some 𝕀₃
        | _ => None
        end
  end.

Definition DomainAxisGround (d : IELDomain) (a : Axis) (o : Obj) : Prop :=
  DomainProfile d a = Some o.

Lemma DomainProfile_sound :
  forall d a o, DomainProfile d a = Some o -> DomainAxisGround d a o.
Proof.
  intros d a o H; unfold DomainAxisGround; exact H.
Qed.

Definition OntoGrid_Coherent : Prop :=
  forall (d : IELDomain) (a : Axis) (o : Obj),
    DomainAxisGround d a o -> o = AxisTarget a.

Definition OntoGrid_Principled : Prop :=
  forall (d : IELDomain) (a : Axis),
    PrincipleOf (AxisTarget a) (AxisPrinciple a).

Definition OntoGrid_NoDrift : Prop := OntoGrid_Coherent.

Lemma OntoGrid_NoDrift_holds : OntoGrid_Coherent -> OntoGrid_NoDrift.
Proof. easy. Qed.

Lemma AxisTarget_has_Principle :
  forall a : Axis, PrincipleOf (AxisTarget a) (AxisPrinciple a).
Proof.
  intro a; destruct a; simpl;
    try exact I1_is_Sign;
    try exact I2_is_Bridge;
    try exact I3_is_Mind;
    try exact O_is_Mesh.
Qed.
