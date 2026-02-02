(*
  PXL_Modal_Semantic_Kripke.v

  Purpose (Phase 3 / Historical Milestone Track):
  - Introduce semantic S5 (Kripke) as a *derived* modal layer.
  - Do NOT modify the PXL kernel yet.
  - Provide "drop-in" theorems corresponding to ax_K and ax_T
    using Kripke semantics over an equivalence relation.

  Notes:
  - We use "validity at all worlds" as the Prop-level adapter:
      □p  :=  forall w, box (fun _ => p) w
      ◇p  :=  exists w, dia (fun _ => p) w
  - This is a conservative adapter that avoids choosing an "actual world".
*)

(* Import the existing, proven Kripke semantics file. *)
From Stdlib Require Import Logic.Classical_Prop.

(* NOTE: S5_Kripke.v is already compiled as part of the external PXLd project.
  Use the PXLd logical root provided by _CoqProject. *)
From PXL.modal.PXLd Require Import S5_Kripke.

Section PXL_Kripke_Adapter.

  (* Worlds and accessibility *)
  Variable W : Type.
  Variable R : W -> W -> Prop.

  Hypothesis R_refl  : forall w, R w w.
  Hypothesis R_symm  : forall w u, R w u -> R u w.
  Hypothesis R_trans : forall w u v, R w u -> R u v -> R w v.

  (* Define box/dia locally (same as S5_Kripke.v) *)
  Definition box (p:W->Prop) : W->Prop := fun w => forall u, R w u -> p u.
  Definition dia (p:W->Prop) : W->Prop := fun w => exists u, R w u /\ p u.

  (* Prop-level "global" adapter *)
  Definition PXL_Box (p : Prop) : Prop :=
    forall w : W, box (fun _ => p) w.

  Definition PXL_Dia (p : Prop) : Prop :=
    exists w : W, dia (fun _ => p) w.

  (* Semantic K (distribution) at Prop level *)
  Theorem PXL_ax_K_sem :
    forall p q : Prop, PXL_Box (p -> q) -> PXL_Box p -> PXL_Box q.
  Proof.
    intros p q Hpq Hp w.
    unfold PXL_Box in *.
    specialize (Hpq w). specialize (Hp w).
    (* box R (fun _ => p -> q) w  and box R (fun _ => p) w *)
    (* use the K lemma from S5_Kripke, or unfold directly *)
    intros u Hwu.
    specialize (Hpq u Hwu).
    specialize (Hp u Hwu).
    exact (Hpq Hp).
  Qed.

  (* Semantic T (reflexivity) at Prop level *)
  (* Requires W to be inhabited to extract a witness world *)
  Hypothesis W_inhabited : W.

  Theorem PXL_ax_T_sem :
    forall p : Prop, PXL_Box p -> p.
  Proof.
    intros p Hb.
    unfold PXL_Box in Hb.
    (* Use reflexivity with the inhabited witness *)
    specialize (Hb W_inhabited).
    unfold box in Hb.
    apply (Hb W_inhabited).
    apply R_refl.
  Qed.

  (* Semantic Necessitation (Prop-level adapter)
     Under global validity, any proven p lifts to PXL_Box p. *)
  Theorem PXL_ax_Nec_sem :
    forall p : Prop, p -> PXL_Box p.
  Proof.
    intros p Hp w.
    unfold PXL_Box, box.
    intros _ _. exact Hp.
  Qed.

End PXL_Kripke_Adapter.

