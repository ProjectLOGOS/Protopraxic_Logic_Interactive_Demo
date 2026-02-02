(*
  Privation_Detector_Skeleton.v

  Goal: a sound privative boundary detector over a representable syntax class.
  We do not claim completeness; Unknown is allowed.
*)

From PXL Require Import PXLv3_SemanticModal.

Inductive PStmt : Type :=
| PAtom : nat -> PStmt
| PAnd  : PStmt -> PStmt -> PStmt
| PNot  : PStmt -> PStmt.

Inductive DetectResult : Type :=
| Detect_Incoherent
| Detect_Coherent
| Detect_Unknown.

Parameter eval_stmt : PStmt -> Prop.

(* A conservative detector: implement later. *)
Parameter detect : PStmt -> DetectResult.

(* Soundness-only contract. *)
Axiom detect_sound_incoherent :
  forall s, detect s = Detect_Incoherent -> incoherent (eval_stmt s).

(*
  When integrated into runtime:
    - if Detect_Incoherent => block or collapse (provably safe)
    - else => allow or defer (no false safety claims)
*)
