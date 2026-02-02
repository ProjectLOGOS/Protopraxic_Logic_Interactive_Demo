(************************************************************************)
(*  PXL_Omni_Bridges.v                                                 *)
(*  Granular bridge lemmas/axioms for omni properties                  *)
(************************************************************************)

From Stdlib Require Import Unicode.Utf8.
From PXL Require Import PXL_Definitions PXL_Modal_Axioms_Semantic PXL_Kernel_Axioms PXL_Omni_Properties.

Module PXL_Omni_Bridges.

  Import PXL_Omni_Properties.
  Import PXL_Kernel_Axioms.

  (*** OP3: Omnipresence bridges (I₃ world interface) ***)
  (* Presence across all objects/worlds. *)
  Axiom OP3_present_all_worlds : □ (forall w : Obj, 𝕀₃ ⇌ w).

  (*** OP1: Omniscience bridges (I₁ knowledge interface) ***)
  Axiom OP1_truth_grounded_I1 : forall p : Prop, Truth p -> grounded_in p 𝕀₁.
  Lemma OP1_grounded_leads_K_I1 : forall p : Prop, grounded_in p 𝕀₁ -> K 𝕀₁ p.
  Proof.
    intros p Hp.
    apply (Perfect_self_knowledge (x:=𝕀₁) (p:=p)).
    exact Hp.
  Qed.
  Lemma OP1_truth_to_K_box : □ (forall p : Prop, Truth p -> K 𝕀₁ p).
  Proof.
    apply ax_Nec.
    intros p Hp.
    pose proof (OP1_truth_grounded_I1 p Hp) as Hg.
    pose proof (OP1_grounded_leads_K_I1 p Hg) as HK.
    exact HK.
  Qed.

  (*** OP2: Omnibenevolence bridge (I₂ volition interface) ***)
  Axiom OP2_wills_implies_good_box : □ (forall φ : Prop, Wills 𝕀₂ φ -> Good φ).

  (*** OP4: Omnipotence bridge (Necessary Being capability) ***)
  (* OP4 bridge: omnipotence grounded in NB's modal power *)
  Definition OP4_coherent_implies_possible :
    □ (forall φ : Prop, Coherent φ -> ◇ (entails 𝕆 φ)) :=
    NB_modal_power.

End PXL_Omni_Bridges.
