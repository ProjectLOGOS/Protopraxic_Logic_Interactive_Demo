# TXT Section Audit Template

Use this template to audit each section of legacy TXT documentation.

---

## Section Metadata

**Document ID**: `_________________`  
**Section ID**: `_________________`  
**Section Title**: `_________________`  
**Page/Line Range**: `_________________`

---

## Step 1: Claim Classification

**What type of content is this?** (check one)

- [ ] Axiom (primitive assumption)
- [ ] Theorem (proven result)
- [ ] Definition (formal term definition)
- [ ] Lemma (supporting result)
- [ ] Motivation (conceptual explanation)
- [ ] Example (illustrative application)
- [ ] Notation (symbolic conventions)
- [ ] Abstract (system overview)
- [ ] Meta-claim (verification/completeness statement)
- [ ] Other: `_________________`

---

## Step 2: Formal Claim Check

**Does this section assert a formal claim?**

- [ ] YES — Makes verifiable mathematical/logical assertion
- [ ] NO — Narrative/explanatory content only

**If YES, extract the claim:**

```
TXT Claim (as written):
_______________________________________________
_______________________________________________
_______________________________________________
```

---

## Step 3: Proof ID Mapping

**Search proof_index.json for relevant proof IDs:**

**Proof IDs that might cover this**: `_________________`

**Selected proof ID(s)**: `_________________`

**If no mapping found:**
- [ ] Content is explanatory (no formal claim intended)
- [ ] Content is future work (no proof exists yet)
- [ ] Content is deprecated (contradicts current code)

---

## Step 4: Source Verification

**If mapped to proof ID, fetch Coq source:**

**File path**: `_________________`

**Formal anchor (theorem/axiom/definition name)**: `_________________`

```coq
Coq Definition/Theorem (copy from .v file):
_______________________________________________
_______________________________________________
_______________________________________________
```

---

## Step 5: Match Quality Assessment

**Compare TXT claim to Coq definition:**

- [ ] **Exact** — Symbols and structure identical
- [ ] **Equivalent** — Logically equivalent, different notation
- [ ] **Approximate** — General idea matches, details differ
- [ ] **Drift** — Significant divergence, requires correction
- [ ] **N/A** — No formal claim (explanatory content)

**Specific discrepancies noted:**
```
_______________________________________________
_______________________________________________
```

---

## Step 6: Authority Classification

**Based on mapping and match quality:**

- [ ] **formal** — Proven by listed .v files, maps to status='proven'
- [ ] **explanatory_only** — Narrative only, no formal claim
- [ ] **deprecated** — Conflicts with or superseded by code
- [ ] **to_formalize** — Future work, no proof exists yet

---

## Step 7: Status Assignment

- [ ] **covered** — Formal anchor exists, claim matches proof
- [ ] **eliminated** — Presented as axiom but actually proven lemma
- [ ] **partial** — Formal work incomplete (admits > 0)
- [ ] **unsupported** — No formal anchor, cannot assert as proven
- [ ] **non-formal** — No formal claim intended

---

## Step 8: Normalization Rule Checks

### R1: Unsupported Formal Claims
**Does section assert necessity/completeness/consistency without proven anchor?**
- [ ] PASS — No unsupported claims
- [ ] FAIL — Makes unsupported formal assertion

**If FAIL, action**: `_________________`

---

### R2: Symbol/Terminology Parity
**Do symbols/terms match .v files exactly?**
- [ ] PASS — Parity maintained
- [ ] FAIL — Mismatch detected

**If FAIL, discrepancies**: `_________________`

**If FAIL, action**: `_________________`

---

### R3: Future Work Discipline
**If claiming future work, maps to skeleton/empty proof IDs only?**
- [ ] N/A — Not future work
- [ ] PASS — Correctly labeled and mapped
- [ ] FAIL — Claims completion without proof

**If FAIL, action**: `_________________`

---

### R4: Authority Classification
**Is authority enum unambiguous?**
- [ ] PASS — Clear classification
- [ ] FAIL — Ambiguous or unclear

**If FAIL, action**: `_________________`

---

### R5: Eliminated Axiom Labeling
**If axiom in TXT, is it actually a proven lemma in code?**
- [ ] N/A — Not an axiom
- [ ] PASS — Correctly labeled
- [ ] FAIL — Mislabeled as axiom

**If FAIL, actual status**: `_________________`

**If FAIL, action**: `_________________`

---

### R6: Verification Claims
**If claiming zero admits or full verification, anchored to proof_index.json?**
- [ ] N/A — No verification claim
- [ ] PASS — Anchored and verifiable
- [ ] FAIL — Unsupported verification claim

**If FAIL, action**: `_________________`

---

## Step 9: Action Decision

**Final action for this section:**

- [ ] **KEEP** — No changes needed
- [ ] **REVISE** — Correct symbols/terminology/status
- [ ] **DEMOTE** — Change from formal to explanatory
- [ ] **REMOVE** — Delete section entirely

**If REVISE, specific changes needed:**
```
_______________________________________________
_______________________________________________
_______________________________________________
```

**If DEMOTE, disclaimer to add:**
```
_______________________________________________
_______________________________________________
```

---

## Step 10: JSON Entry

**Complete JSON entry for txt_normalization_schema.json:**

```json
{
  "section_id": "_________________",
  "title": "_________________",
  "claim_type": "_________________",
  "maps_to": ["_________________"],
  "formal_anchor": "_________________",
  "authority": "_________________",
  "status": "_________________",
  "txt_claim": "_________________",
  "coq_definition": "_________________",
  "match_quality": "_________________",
  "notes": "_________________"
}
```

---

## Auditor Notes

**Additional observations or edge cases:**
```
_______________________________________________
_______________________________________________
_______________________________________________
```

**Questions or concerns flagged for review:**
```
_______________________________________________
_______________________________________________
_______________________________________________
```

---

## Approval

**Audited by**: `_________________`  
**Date**: `_________________`  
**Reviewed by**: `_________________`  
**Date**: `_________________`

---

## Quick Reference: Decision Tree

```
Does section assert formal claim?
├─ NO → authority: explanatory_only, status: non-formal, KEEP
└─ YES → Does proof ID exist?
    ├─ NO → authority: to_formalize OR deprecated
    │   └─ Future work? → authority: to_formalize, DEMOTE or KEEP with caveat
    │   └─ Conflicts with code? → authority: deprecated, REMOVE
    └─ YES → Proof status?
        ├─ proven (admits: 0) → authority: formal, VERIFY match quality
        │   ├─ Match quality: exact/equivalent → status: covered, KEEP
        │   └─ Match quality: drift → status: covered, REVISE
        ├─ partial (admits > 0) → authority: formal, status: partial, REVISE with caveat
        └─ skeleton/empty → authority: to_formalize, DEMOTE
```
