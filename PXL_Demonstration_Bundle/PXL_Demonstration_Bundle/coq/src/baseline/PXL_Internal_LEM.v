(* ========================================================= *)
(*  PXL – Protopraxic Logic: Self‑Contained Internal LEM     *)
(* ========================================================= *)

(* --- Context --------------------------------------------------
   This module integrates directly with PXL’s Trinity framework.
   It assumes the following already exist in scope:
     - grounded_in : Prop -> Obj -> Prop
     - modus_groundens : forall (x y:Obj) (P:Prop),
         □ (x ⧟ y) -> entails x P -> entails y P
     - coherence : Obj -> Prop  (typically 𝕆)
     - 𝕀₁ 𝕀₂ 𝕀₃ 𝕆 : Obj
     - ax_T : forall p, □ p -> p
     - ax_Nec : forall p, p -> □ p
   ------------------------------------------------------------- *)

From PXL Require Import PXLv3.

Module PXL_Internal_LEM.

Import PXLv3.

(* Each proposition grounds in either its positive or negative mode. *)
Axiom trinitarian_decidability :
  forall (P : Prop), grounded_in P 𝕀₁ \/ grounded_in (~ P) 𝕀₂.

Lemma grounding_yields_truth :
  forall (P : Prop) (x : Obj),
    grounded_in P x ->
    □ (coherence 𝕆) ->
    P.
Proof.
  intros P x Hgx Hcoh.
  pose proof (grounding_yields_entails (x:=x) (P:=P) Hgx) as Hent.
  pose proof (coherence_lifts_entailment (x:=x) (P:=P) (ax_T (p:=coherence 𝕆) Hcoh) Hent) as HΩ.
  exact (entails_global_implies_truth (P:=P) HΩ).
Qed.

Theorem pxl_excluded_middle :
  forall P : Prop, P \/ ~ P.
Proof.
  intros P.
  destruct (trinitarian_decidability P) as [HP | HnP].
  - left.
    apply (grounding_yields_truth P 𝕀₁); [exact HP|exact A7_triune_necessity].
  - right.
    intro HPtrue.
    pose proof (grounding_yields_truth (~P) 𝕀₂ HnP A7_triune_necessity) as HnotP.
    apply HnotP; exact HPtrue.
Qed.

End PXL_Internal_LEM.
