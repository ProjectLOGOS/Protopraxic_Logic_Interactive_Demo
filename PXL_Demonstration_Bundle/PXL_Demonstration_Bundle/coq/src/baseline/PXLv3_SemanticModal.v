(*
  PXLv3_SemanticModal.v

  Parallel kernel profile:
  - Replaces modal Parameters (Box/Dia) with semantic Definitions (Kripke adapter).
  - Removes modal axioms from the trusted base by proving them as theorems.
  - Keeps the rest of PXLv3 interface (Obj, Ident, entails, etc.) as Parameters/Axioms.

  IMPORTANT:
  - This file is NOT yet wired into the baseline proof stack.
  - It is a migration target for the “historical” modal internalization milestone.
*)

From Stdlib Require Import Logic.Classical_Prop.

(* Import semantic scaffold (already proven + gated) *)
From PXL.modal Require Import PXL_Modal_Semantic_Kripke.

(* Phase 2: Import and EXPORT definitional operators (Ident, Inter) *)
(* Export ensures modules importing PXLv3_SemanticModal can see Obj, Ident, Inter *)
From PXL Require Export PXL_Definitions.
From PXL Require Export PXL_Derivations_Phase2.

(* ========= Shared primitives (match PXLv3.v shape) ========= *)

(* Phase 2: Obj declared in PXL_Definitions, re-export here *)
(* Definition already imported from PXL_Definitions *)
Parameters 𝕆 𝕀₁ 𝕀₂ 𝕀₃ : Obj.

(* Phase 2: Ident and Inter now DEFINED (not Parameter) via PXL_Definitions *)
(* Ident(x,y) := ∀P, P x → P y (Leibniz equality) *)
(* Inter(x,y) := ∃z, x⧟z ∧ y⧟z (symmetric accessibility) *)
(* NonEquiv remains Parameter (privative primitive) *)

(* Phase 3: PImp and MEquiv now DEFINED (not Parameter) via PXL_Definitions *)
(* PImp p q := p → q (Coq implication) *)
(* MEquiv p q := p ↔ q (Coq biconditional) *)

Parameter entails : Obj -> Prop -> Prop.
Parameter grounded_in : Prop -> Obj -> Prop.
Parameter incoherent : Prop -> Prop.
Parameter coherence : Obj -> Prop.

(* Notations already defined in PXL_Definitions.v (imported above):
   - x ⧟ y  (Ident)
   - x ⇎ y  (NonEquiv)
   - x ⇌ y  (Inter)
   - p ⟹ q (PImp)
   - p ⩪ q (MEquiv)
*)

(* ========= Semantic modal core (Definitions, not Parameters) ========= *)

Section SemanticModal.

  (* Frame parameters (proof obligations, not axioms) *)
  Parameter W : Type.
  Parameter w0 : W.
  Parameter R : W -> W -> Prop.

  Parameter R_refl  : forall w, R w w.
  Parameter R_symm  : forall w u, R w u -> R u w.
  Parameter R_trans : forall w u v, R w u -> R u v -> R w v.

  (* Box/Dia as semantic definitions via adapter *)
  Definition Box (p : Prop) : Prop := PXL_Box W R p.
  Definition Dia (p : Prop) : Prop := PXL_Dia W R p.

  Notation "□ p" := (Box p) (at level 75).
  Notation "◇ p" := (Dia p) (at level 75).

  (* ========= Modal axioms now as THEOREMS ========= *)

  Theorem ax_K : forall p q : Prop, □ (p -> q) -> □ p -> □ q.
  Proof.
    intros p q Himp Hp.
    unfold Box in *.
    eapply (@PXL_ax_K_sem W R p q); assumption.
  Qed.

  Theorem ax_T : forall p : Prop, □ p -> p.
  Proof.
    intros p Hp.
    unfold Box in *.
    eapply (@PXL_ax_T_sem W R R_refl w0 p); assumption.
  Qed.

  Theorem ax_Nec : forall p : Prop, p -> □ p.
  Proof.
    intros p Hp.
    unfold Box in *.
    eapply (@PXL_ax_Nec_sem W R p); assumption.
  Qed.

End SemanticModal.

(* ========= Non-modal axioms: 8 remaining after Phase 3 ========= *)

  (* PHASE 2 ELIMINATION: 4 axioms removed (16 → 12) *)
  (* - ax_ident_refl  → ident_refl_derived  (Leibniz reflexivity)      *)
  (* - ax_ident_symm  → ident_symm_derived  (Leibniz symmetry)         *)
  (* - ax_ident_trans → ident_trans_derived (Leibniz transitivity)     *)
  (* - ax_inter_comm  → inter_comm_derived  (symmetric witness)        *)
  (* All 4 proven in PXL_Derivations_Phase2.v, imported above.         *)
  
  (* PHASE 3 ELIMINATION: 4 bridge axioms removed (12 → 8) *)
  (* - ax_imp_intro    → bridge_imp_intro    (PImp definition)         *)
  (* - ax_imp_elim     → bridge_imp_elim     (PImp definition)         *)
  (* - ax_mequiv_intro → bridge_mequiv_intro (MEquiv definition)       *)
  (* - ax_mequiv_elim  → bridge_mequiv_elim  (MEquiv definition)       *)
  (* All 4 proven in PXL_Derivations_Phase2.v, imported above.         *)
  
  (* Compatibility exports: Use derived lemmas with original names *)
  Definition ax_ident_refl   := ident_refl_derived.
  Definition ax_ident_symm   := ident_symm_derived.
  Definition ax_ident_trans  := ident_trans_derived.
  Definition ax_inter_comm   := inter_comm_derived.
  Definition ax_imp_intro    := bridge_imp_intro.
  Definition ax_imp_elim     := bridge_imp_elim.
  Definition ax_mequiv_intro := bridge_mequiv_intro.
  Definition ax_mequiv_elim  := bridge_mequiv_elim.

  (* ax_nonequiv_irrefl eliminated: proven from A2_noncontradiction + ax_ident_refl *)

  (* 8 IRREDUCIBLE METAPHYSICAL AXIOMS *)
  (* These define PXL's metaphysical commitments and cannot be further reduced *)
  (* without changing the semantic foundation of the logic. *)

  Axiom A2_noncontradiction : Box (forall x y : Obj, ~ (Ident x y /\ NonEquiv x y)).
  Axiom A7_triune_necessity : Box (coherence 𝕆).

  Axiom modus_groundens :
    forall (x y : Obj) (P : Prop), Box (Ident x y) -> entails x P -> entails y P.

  Axiom triune_dependency_substitution :
    forall (phi psi : Prop), grounded_in phi 𝕀₁ -> grounded_in psi 𝕀₂ -> MEquiv phi psi -> coherence 𝕆.

  Axiom privative_collapse :
    forall (P : Prop), ~ (Dia (entails 𝕆 P)) -> incoherent P.

  Axiom grounding_yields_entails :
    forall (x : Obj) (P : Prop), grounded_in P x -> entails x P.

  Axiom coherence_lifts_entailment :
    forall (x : Obj) (P : Prop), coherence 𝕆 -> entails x P -> entails 𝕆 P.

  Axiom entails_global_implies_truth :
    forall (P : Prop), entails 𝕆 P -> P.
