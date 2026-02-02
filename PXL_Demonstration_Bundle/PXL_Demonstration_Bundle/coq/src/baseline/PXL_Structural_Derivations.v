(*
  PXL_Structural_Derivations.v

  Purpose:
  - Phase 1 staging ground to eliminate S4 "structural axioms" by proving them as lemmas.
  - Do NOT introduce new axioms here.
  - Workflow: for each structural axiom S in PXLv3.v:
      1) restate as Lemma S_derived : <S>.
      2) prove using existing kernel axioms + previously derived lemmas.
      3) once proved, delete S from PXLv3.v and replace imports to use this lemma module.

  Hard invariants:
  - Must not add assumptions to:
      pxl_excluded_middle
      trinitarian_optimization
*)

From PXL Require Import PXLv3.
From PXL Require Import PXL_Foundations.

(* ===========================================================================
   PHASE 1B: A1_identity reduction
   
   HYPOTHESIS: A1_identity can be proven from ax_ident_refl + ax_Nec
   
   A1_identity: □ (∀x : Obj, x ⧟ x)
   ax_ident_refl: ∀x : Obj, x ⧟ x
   ax_Nec: ∀p : Prop, p → □ p
   
   Proof strategy:
   1. Take ax_ident_refl as witness for (∀x, x ⧟ x)
   2. Apply ax_Nec to wrap in □
   =========================================================================== *)

Lemma A1_from_refl : □ (forall x : Obj, x ⧟ x).
Proof.
  apply ax_Nec.
  intro x.
  apply ax_ident_refl.
Qed.

(* If above compiles successfully, A1_identity can be eliminated from PXLv3.v *)

(* ===========================================================================
   PHASE 1C: Modal redundancy elimination
   
   HYPOTHESIS: ax_4 and ax_5 are derivable from ax_Nec alone
   
   ax_4: ∀p, □p → □(□p)
   ax_5: ∀p, ◇p → □(◇p)
   ax_Nec: ∀p, p → □p
   
   Proof strategy:
   Both axioms just apply ax_Nec to their premise:
   - ax_4: Given □p, apply ax_Nec to get □(□p)
   - ax_5: Given ◇p, apply ax_Nec to get □(◇p)
   =========================================================================== *)

Lemma ax_4_derived : forall p : Prop, □ p -> □ (□ p).
Proof.
  intros p Hp.
  apply ax_Nec.
  exact Hp.
Qed.

Lemma ax_5_derived : forall p : Prop, ◇ p -> □ (◇ p).
Proof.
  intros p Hp.
  apply ax_Nec.
  exact Hp.
Qed.

(* If above compile successfully, ax_4 and ax_5 can be eliminated from PXLv3.v *)

(* ===========================================================================
   PHASE 1D: A4_distinct_instantiation reduction
   
   HYPOTHESIS: A4_distinct_instantiation is derivable from ax_ident_refl + ax_Nec
   
   A4_distinct_instantiation: □ (𝕀₁⧟𝕀₁ ∧ 𝕀₂⧟𝕀₂ ∧ 𝕀₃⧟𝕀₃)
   ax_ident_refl: ∀x, x ⧟ x
   ax_Nec: ∀p, p → □p
   
   NOTE: Universe polymorphism prevents direct application of ax_ident_refl
   to the specific hypostases. We must instantiate ax_ident_refl for each.
   =========================================================================== *)

Lemma A4_derived : □ (𝕀₁ ⧟ 𝕀₁ /\ 𝕀₂ ⧟ 𝕀₂ /\ 𝕀₃ ⧟ 𝕀₃).
Proof.
  apply ax_Nec.
  repeat split.
  - exact (ax_ident_refl 𝕀₁).
  - exact (ax_ident_refl 𝕀₂).
  - exact (ax_ident_refl 𝕀₃).
Qed.

(* If above compiles successfully, A4_distinct_instantiation can be eliminated from PXLv3.v *)

(* ===========================================================================
   PHASE 1E: Identity Equivalence Relation Axioms (STATUS: COMPLETE)
   
   Target: Eliminate ax_ident_refl, ax_ident_symm, ax_ident_trans.
   
   RESOLUTION: PXL_Definitions.v now defines Ident as Leibniz equality and
   PXL_Derivations_Phase2.v proves the three axioms as lemmas
   (ident_refl_derived, ident_symm_derived, ident_trans_derived).
   The compatibility aliases ax_ident_* are therefore provided by those
   lemmas and no longer depend on primitive axioms.
   =========================================================================== *)

(* PHASE1_STATUS: ax_ident_refl eliminated via ident_refl_derived
    (PXL_Derivations_Phase2.v). *)

(* PHASE1_STATUS: ax_ident_symm eliminated via ident_symm_derived
   (PXL_Derivations_Phase2.v). *)

(* PHASE1_STATUS: ax_ident_trans eliminated via ident_trans_derived
   (PXL_Derivations_Phase2.v). *)

(* ===========================================================================
   PHASE 1F: Non-Equivalence Irreflexivity (STATUS: COMPLETE)
   
   HYPOTHESIS: ax_nonequiv_irrefl can be derived from A2_noncontradiction + ax_ident_refl
   
   A2_noncontradiction: □ (∀x y, ¬(x ⧟ y ∧ x ⇎ y))
   ax_ident_refl: ∀x, x ⧟ x
   
   Target: ax_nonequiv_irrefl: ∀x, ¬(x ⇎ x)
   
   Proof strategy:
   1. Use ax_ident_refl to get x ⧟ x
   2. Apply A2_noncontradiction with x, x to get ¬(x ⧟ x ∧ x ⇎ x)
   3. Since we have x ⧟ x, we must have ¬(x ⇎ x)
   =========================================================================== *)

(* PHASE1_STATUS: ax_nonequiv_irrefl eliminated via nonequiv_irrefl_derived
   (PXL_Derivations_Phase2.v). *)

(* ===========================================================================
   PHASE 1G: Interaction Commutativity (STATUS: COMPLETE)
   
   HYPOTHESIS: ax_inter_comm should be derivable if Inter has symmetric structure.
   
   Target: ax_inter_comm: ∀x y, x ⇌ y ↔ y ⇌ x.
   
   RESOLUTION: PXL_Definitions.v defines Inter using a shared witness, and
   PXL_Derivations_Phase2.v proves inter_comm_derived. The alias ax_inter_comm
   now points to that lemma, removing the need for an independent axiom.
   =========================================================================== *)

(* PHASE1_STATUS: ax_inter_comm eliminated via inter_comm_derived
   (PXL_Derivations_Phase2.v). *)

(* ===========================================================================
   Summary of Derivation Status
   
   COMPLETED (ready to eliminate from kernel):
   - ax_ident_refl → ident_refl_derived ✓
   - ax_ident_symm → ident_symm_derived ✓
   - ax_ident_trans → ident_trans_derived ✓
   - ax_nonequiv_irrefl → nonequiv_irrefl_derived ✓
   - ax_inter_comm → inter_comm_derived ✓
   - A1_identity → A1_from_refl ✓
   - ax_4 → ax_4_derived ✓
   - ax_5 → ax_5_derived ✓
   - A4_distinct_instantiation → A4_derived ✓
   
   IN PROGRESS (need proof completion):
   - (none)
   
   BLOCKED (need definitional structure):
   - (none)
   =========================================================================== *)

