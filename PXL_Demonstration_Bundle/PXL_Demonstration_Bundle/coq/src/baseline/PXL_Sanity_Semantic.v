(*
  PXL_Sanity_Semantic.v
  Pilot compile target to validate the semantic kernel can support baseline-style modules.
  Non-invasive: does not replace existing PXL_Sanity.v.
*)

From PXL Require Import PXLv3_SemanticModal.

(* Lightweight existence checks only. *)
Check ax_K.
Check ax_T.
Check ax_Nec.
