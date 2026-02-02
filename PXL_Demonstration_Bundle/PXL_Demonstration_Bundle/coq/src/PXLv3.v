(** Minimal kernel surface for the Protopraxic Logic (PXL) axioms.
    
    Phase 3 complete: 8 irreducible metaphysical axioms.
    
    Eliminated via definitions:
    - Ident, Inter, PImp, MEquiv (PXL_Definitions.v)
    - 8 structural/bridge axioms (PXL_Derivations_Phase2.v)
    - 3 modal axioms as semantic frame conditions (PXL_Modal_Axioms_Semantic.v)
    
    Remaining: 8 metaphysical axioms ONLY
    
    Note: Modal operators (Box, Dia) are semantically grounded in S5 Kripke frames.
    The "frame conditions" (distribution, reflexivity, necessitation) are semantic
    properties derivable from Kripke semantics, not arbitrary axioms.
*)

Require Export PXL.PXL_Definitions.
Require Export PXL.PXL_Derivations_Phase2.
Require Export PXL.PXL_Modal_Axioms_Semantic.
Require Export PXL.PXL_Kernel_Axioms.

Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.

(* --- Compatibility aliases for eliminated axioms ------------------------- *)

(* Phase 2/3 eliminated these as axioms, now proven as lemmas.
   Provide aliases so existing code continues to work. *)
Definition ax_ident_refl := ident_refl_derived.
Definition ax_ident_symm := ident_symm_derived.
Definition ax_ident_trans := ident_trans_derived.
Definition ax_inter_comm := inter_comm_derived.
Definition ax_imp_intro := bridge_imp_intro.
Definition ax_imp_elim := bridge_imp_elim.
Definition ax_mequiv_intro := bridge_mequiv_intro.
Definition ax_mequiv_elim := bridge_mequiv_elim.

(* --- Domain primitives --------------------------------------------------- *)

(* Imported from supporting modules:
   - PXL_Definitions.v: Obj, Ident, NonEquiv, Inter, PImp, MEquiv
   - PXL_Modal_Axioms_Semantic.v: Box, Dia, ax_K, ax_T, ax_Nec
   - PXL_Kernel_Axioms.v: residual constants and metaphysical axioms
*)
Notation "∼ p" := (~ p) (at level 75).

(* --- Modal backbone (semantic, not axiomatic) ---------------------------- *)

(* ax_K, ax_T, ax_Nec eliminated as axioms; see PXL_Modal_Axioms_Semantic.v. *)

(* ax_4, ax_5 eliminated: proven from ax_Nec in PXL_Structural_Derivations.v *)

(* --- Structural laws (eliminated via Phase 2/3) -------------------------- *)

(* ax_ident_refl, ax_ident_symm, ax_ident_trans: 
   Proven in PXL_Derivations_Phase2.v from Leibniz definition of Ident *)

(* ax_nonequiv_irrefl: 
   Proven from A2_noncontradiction + ident_refl in PXL_Derivations_Phase2.v *)

(* ax_inter_comm: 
   Proven in PXL_Derivations_Phase2.v from symmetric witness definition of Inter *)

(* ax_imp_intro, ax_imp_elim, ax_mequiv_intro, ax_mequiv_elim:
   Proven in PXL_Derivations_Phase2.v from PImp := (->) and MEquiv := (<->) *)

(* A1_identity, A4_distinct_instantiation eliminated: proven from ax_ident_refl + ax_Nec in PXL_Structural_Derivations.v *)
(* --- Residual metaphysical axioms ---------------------------------------- *)

(* All remaining axioms now live in PXL_Kernel_Axioms.v. *)
