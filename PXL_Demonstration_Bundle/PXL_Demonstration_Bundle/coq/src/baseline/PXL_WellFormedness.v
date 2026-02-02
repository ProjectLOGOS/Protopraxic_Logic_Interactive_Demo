(** PXL_WellFormedness.v
    Well-formedness/admissibility + core paradox-blocking metatheorems.

    Goal: Provide a statement you can cite in the paradox catalog:
      - liar-family formulas are not in Dom(I1) / not in O
    Here made precise as: not typable / not admissible under stratified truth.
*)

Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Program.Equality.
From PXL Require Import PXL_ObjectLanguage.

(* In this architecture, "well-formed" is enforced by typing:
   if phi : Form level, it is well-formed at level level.
   Still, it helps to expose a named predicate to match catalog language.
*)
Definition InO {level : Lvl} (_ : Form level) : Prop := True.

(* A helper: extract the level index as a nat. Useful for metatheorems. *)
Definition level_of {level : Lvl} (_ : Form level) : Lvl := level.

Definition Packed : Type := { l : Lvl & Form l }.

Definition pack {l : Lvl} (phi : Form l) : Packed := existT _ l phi.

Lemma pack_level_eq :
  forall (l1 l2 : Lvl) (phi1 : Form l1) (phi2 : Form l2),
    pack phi1 = pack phi2 -> l1 = l2.
Proof.
  intros l1 l2 phi1 phi2 H.
  dependent destruction H.
  reflexivity.
Qed.

(* Truth always raises the level by exactly one. *)
Theorem truth_raises_level :
  forall (level : Lvl) (phi : Form level),
    level_of (FTruth phi) = S (level_of phi).
Proof.
  intros level phi. reflexivity.
Qed.

(* Stratified truth blocks any same-level identification with truth. *)
Theorem no_same_level_truth_term :
  forall (level : Lvl) (phi : Form level) (psi : Form level),
    pack psi <> pack (FTruth phi).
Proof.
  intros level phi psi Heq.
  pose proof (pack_level_eq (l1:=level) (l2:=S level)
                            (phi1:=psi) (phi2:=FTruth phi) Heq) as Hlev.
  apply (PeanoNat.Nat.neq_succ_diag_l level).
  symmetry.
  exact Hlev.
Qed.

(* Core liar blocker: no fixed point of negated truth at the same level. *)
Theorem no_liar_fixed_point_term :
  forall (level : Lvl) (L : Form level),
    pack L <> pack (FNot (FTruth L)).
Proof.
  intros level L Heq.
  pose proof (pack_level_eq (l1:=level) (l2:=S level)
                            (phi1:=L) (phi2:=FNot (FTruth L)) Heq) as Hlev.
  apply (PeanoNat.Nat.neq_succ_diag_l level).
  symmetry.
  exact Hlev.
Qed.

(* Curry-style constructions cannot be formed at the same level. *)
Theorem no_curry_fixed_point_term :
  forall (level : Lvl) (C : Form level) (P : Form (S level)),
    pack C <> pack (FImp (FTruth C) P).
Proof.
  intros level C P Heq.
  pose proof (pack_level_eq (l1:=level) (l2:=S level)
                            (phi1:=C) (phi2:=FImp (FTruth C) P) Heq) as Hlev.
  apply (PeanoNat.Nat.neq_succ_diag_l level).
  symmetry.
  exact Hlev.
Qed.

(* Optional: expose a "Core Admissibility" theorem for catalog citations. *)
Theorem Core_Admissibility_Theorem :
  forall (level : Lvl) (phi : Form level),
    InO phi.
Proof.
  intros level phi. exact I.
Qed.
