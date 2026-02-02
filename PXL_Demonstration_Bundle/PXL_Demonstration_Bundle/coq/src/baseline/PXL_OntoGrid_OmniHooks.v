(************************************************************************)
(*  PXL_OntoGrid_OmniHooks.v                                            *)
(*  Thin hooks tying OntoGrid axes to existing omni-layer artifacts.     *)
(************************************************************************)

From Stdlib Require Import Unicode.Utf8.
From PXL Require Import
  PXL_Kernel_Axioms
  PXL_Omni_Properties
  PXL_Omni_Bridges
  PXL_OntoGrid.

Import PXL_Omni_Bridges.

Definition AxisOmniHook (a : Axis) : Prop :=
  match a with
  | Truth    => □ (forall p : Prop, PXL_Omni_Properties.Truth p -> K 𝕀₁ p)
  | Goodness => □ (forall φ : Prop, PXL_Omni_Properties.Wills 𝕀₂ φ -> PXL_Omni_Properties.Good φ)
  | Presence => □ (forall w : Obj, 𝕀₃ ⇌ w)
  | Power    => □ (forall φ : Prop, PXL_Omni_Properties.Coherent φ -> ◇ (entails 𝕆 φ))
  end.

Lemma Truth_axis_hook : AxisOmniHook Truth.
Proof. unfold AxisOmniHook; exact OP1_truth_to_K_box. Qed.

Lemma Goodness_axis_hook : AxisOmniHook Goodness.
Proof. unfold AxisOmniHook; exact OP2_wills_implies_good_box. Qed.

Lemma Presence_axis_hook : AxisOmniHook Presence.
Proof. unfold AxisOmniHook; exact OP3_present_all_worlds. Qed.

Lemma Power_axis_hook : AxisOmniHook Power.
Proof. unfold AxisOmniHook; exact NB_modal_power. Qed.

Lemma DomainAxisGround_implies_AxisOmniHook :
  forall d a o, DomainAxisGround d a o -> AxisOmniHook a.
Proof.
  intros d a o H.
  unfold DomainAxisGround in H.
  destruct d; destruct a; simpl in H; try discriminate; inversion H; subst;
    try apply Truth_axis_hook;
    try apply Goodness_axis_hook;
    try apply Presence_axis_hook;
    try apply Power_axis_hook.
Qed.
