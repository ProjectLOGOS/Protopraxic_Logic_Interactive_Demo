(*
  PXL_Kernel_Axioms.v

  Shared declaration of the remaining metaphysical axioms and runtime
  parameters for the minimal LOGOS kernel. Keeping these in a dedicated module
  avoids cyclical dependencies when deriving axioms into lemmas across the
  Phase 1/2 elimination files.
*)

Require Export PXL.PXL_Definitions.
Require Export PXL.PXL_Modal_Axioms_Semantic.

Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.

(* ------------------------------------------------------------------------- *)
(* Object-level constants                                                     *)
(* ------------------------------------------------------------------------- *)

Parameters 𝕆 𝕀₁ 𝕀₂ 𝕀₃ : Obj.
Parameters Λ₁ Λ₂ Λ₃ : Prop.

Parameter entails : Obj -> Prop -> Prop.
Parameter grounded_in : Prop -> Obj -> Prop.
Parameter K : Obj -> Prop -> Prop.
Parameter incoherent : Prop -> Prop.
Parameter coherence : Obj -> Prop.

(* ------------------------------------------------------------------------- *)
(* Residual axioms (post Phase 3 reductions)                                 *)
(* ------------------------------------------------------------------------- *)

Axiom A2_noncontradiction : □ (forall x y : Obj, ~ (x ⧟ y /\ x ⇎ y)).
Axiom A7_triune_necessity : □ (coherence 𝕆).

Axiom modus_groundens :
  forall (x y : Obj) (P : Prop), □ (x ⧟ y) -> entails x P -> entails y P.

Axiom triune_dependency_substitution :
  forall (φ ψ : Prop), grounded_in φ 𝕀₁ -> grounded_in ψ 𝕀₂ -> φ ⩪ ψ -> coherence 𝕆.

Axiom privative_collapse :
  forall (P : Prop), ~ (◇ (entails 𝕆 P)) -> incoherent P.

(* Self-grounded truths are epistemically transparent to their ground. *)
Axiom Perfect_self_knowledge :
  forall (x : Obj) (p : Prop),
    grounded_in p x -> K x p.

(* Necessary Being's modal entailment power; capacity, not actualization. *)
Axiom NB_modal_power :
  □ (forall φ : Prop, ~ (incoherent φ) -> ◇ (entails 𝕆 φ)).

Axiom grounding_yields_entails :
  forall (x : Obj) (P : Prop), grounded_in P x -> entails x P.

Axiom coherence_lifts_entailment :
  forall (x : Obj) (P : Prop), coherence 𝕆 -> entails x P -> entails 𝕆 P.

Axiom entails_global_implies_truth :
  forall (P : Prop), entails 𝕆 P -> P.
