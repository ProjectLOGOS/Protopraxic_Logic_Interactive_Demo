From PXL Require Import PXLv3.

(* Demonstrate an unsafe theorem that depends on unproven axioms *)
Axiom unsafe_modification_allowed : Prop.

Theorem unsafe_system_modification : unsafe_modification_allowed -> True.
Proof.
  intro. exact I.
Qed.
