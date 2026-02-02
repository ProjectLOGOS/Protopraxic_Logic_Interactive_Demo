(************************************************************************)
(*  PXL_OmniKernel.v                                                   *)
(*  Kernel-level omni-property API (wraps canonical foundations)        *)
(************************************************************************)

From Stdlib Require Import Unicode.Utf8.
From PXL Require Import PXL_Definitions PXL_Modal_Axioms_Semantic PXL_Kernel_Axioms PXL_Omni_Properties.

Module PXL_OmniKernel.

  Import PXL_Kernel_Axioms.

  (*** Core aliases to PXL object domain ***)
  Definition World : Type := Obj.
  Definition Entity : Type := Obj.

  (*** Distinguished referent and triune identities ***)
  Definition NB : Entity := 𝕆.
  Definition I1 : Entity := 𝕀₁.
  Definition I2 : Entity := 𝕀₂.
  Definition I3 : Entity := 𝕀₃.

  (*** Omni-property API wrappers (aliases to canonical definitions) ***)
  Definition Omniscient : Entity -> Prop := PXL_Omni_Properties.Omniscient.
  Definition Omnibenevolent : Entity -> Prop := PXL_Omni_Properties.Omnibenevolent.
  Definition Omnipresent : Entity -> Prop := PXL_Omni_Properties.Omnipresent.
  Definition Omnipotent : Entity -> Prop := PXL_Omni_Properties.Omnipotent.

  (*** Canonical distribution signatures (proved in PXL_OmniProofs.v) ***)
  Parameter I1_grounds_omniscience     : Omniscient I1.
  Parameter I2_grounds_omnibenevolence : Omnibenevolent I2.
  Parameter I3_grounds_omnipresence    : Omnipresent I3.
  Parameter NB_grounds_omnipotence     : Omnipotent NB.

End PXL_OmniKernel.
