# TXT Normalization Schema — Operator Manual

## Purpose

This document defines the authoritative process for mapping legacy TXT documentation to formal Coq proofs. The goal is to preserve useful narrative content while preventing overclaim, ensuring every formal assertion is traceable to verified code.

**Non-negotiable principle**: `.v files > TXT files` at all times.

---

## Authority Hierarchy

```
[TRUTH SOURCE]
├── Coq source files (.v)           — Canonical definitions and proofs
├── proof_index.json                — Authoritative registry
└── TXT files                       — Supportive annotations ONLY
```

**Consequences:**
- TXT files cannot assert formal claims without anchoring to proven proof IDs
- Symbol mismatches must be corrected in TXT, never in code
- Unsupported claims must be demoted or removed

---

## Authority Enum (Strict Classification)

### `formal`
**Definition**: Claims proven by listed .v files. Must map to `status='proven'` proof IDs.

**Display**: ✓ Formal Proof (green)

**Requirements**:
- Must have non-empty `maps_to` array
- Must reference proof ID with `status: "proven"` and `admits: 0`
- TXT claim must match Coq definition (exact or equivalent)

**Example**:
```json
{
  "section_id": "axiom_a2_noncontradiction",
  "authority": "formal",
  "maps_to": ["pxl_kernel_axioms"],
  "formal_anchor": "A2_noncontradiction",
  "status": "covered"
}
```

---

### `explanatory_only`
**Definition**: Narrative, motivation, examples. No formal claims asserted.

**Display**: ℹ Explanatory Only (gray)

**Requirements**:
- `maps_to` array MUST be empty
- `formal_anchor` MUST be null
- Cannot use language like "proven", "verified", "complete"

**Example**:
```json
{
  "section_id": "motivation_triune_structure",
  "authority": "explanatory_only",
  "maps_to": [],
  "formal_anchor": null,
  "status": "non-formal"
}
```

---

### `deprecated`
**Definition**: Conflicts with or superseded by code. Must be removed or corrected.

**Display**: ⚠ Deprecated (red)

**Action Required**: Immediate correction or deletion.

**Common Causes**:
- TXT asserts axiom that's actually a proven lemma
- TXT uses outdated notation or terminology
- TXT contradicts current kernel structure

**Example**:
```json
{
  "section_id": "old_axiom_scheme",
  "authority": "deprecated",
  "status": "eliminated",
  "notes": "This axiom scheme was eliminated in Phase 2 reduction. Remove from TXT."
}
```

---

### `to_formalize`
**Definition**: Explicitly future work. Must map to `skeleton` or `empty` proof IDs.

**Display**: ⧖ Future Work (gold)

**Requirements**:
- Can only map to proof IDs with `status: "skeleton"` or `status: "empty"`
- Must use conditional language ("would", "could", "target")
- Cannot claim resolution or completion

**Example**:
```json
{
  "section_id": "paradox_liar",
  "authority": "to_formalize",
  "maps_to": [],
  "status": "unsupported",
  "notes": "No formal proof exists. Label as conceptual approach or future work."
}
```

---

## Status Enum

### `covered`
Formal anchor exists, claim matches proof exactly or equivalently.

### `eliminated`
TXT presents as axiom but actually proven as lemma. Must correct TXT to reflect derivation.

### `partial`
Formal work exists but incomplete (admits > 0) or experimental. Can reference but must caveat.

### `unsupported`
No formal anchor exists. Cannot assert as proven. Demote to explanatory or future work.

### `non-formal`
No formal claim intended. Safe as prose.

---

## Match Quality Enum

### `exact`
Symbols and structure identical between TXT and Coq. No normalization needed.

### `equivalent`
Logically equivalent but different notation (e.g., 𝕆 vs NB). Acceptable with note.

### `approximate`
General idea matches but details differ. Requires TXT revision.

### `drift`
Significant divergence. Requires full normalization or removal.

### `n/a`
Not applicable (explanatory content with no formal claim).

---

## Normalization Rules (Mandatory)

### R1: No Unsupported Formal Claims
**Rule**: No TXT section may assert necessity, completeness, or consistency unless anchored to a proven proof ID with `status='proven'`.

**Enforcement**: Mandatory

**Violation Action**: Demote to explanatory or remove

**Example Violations**:
- "PXL resolves the liar paradox" → No proof exists
- "The system is complete" → No completeness theorem proven
- "This proves consistency" → No consistency proof anchored

---

### R2: Symbol/Terminology Parity
**Rule**: Any mismatch in symbols, terminology, or structure must be corrected to match .v files exactly.

**Enforcement**: Mandatory

**Violation Action**: Normalize TXT to match Coq

**Example Violations**:
- TXT uses `⧟` but Coq uses `Ident` → Both are acceptable if documented
- TXT uses `Modal_P` but Coq uses `Box P` → TXT must be corrected
- TXT calls it "axiom" but Coq proves it as lemma → TXT must say "proven lemma"

---

### R3: Future Work Discipline
**Rule**: Future work language must map to skeleton or empty proof IDs only. Cannot assert claims as 'resolved' or 'proven' without formal anchor.

**Enforcement**: Mandatory

**Violation Action**: Label as future work or remove

**Example Violations**:
- "PXL proves X" when no theorem exists
- "This resolves Y" when no resolution proof exists
- "The system handles Z" when no Z-related proof exists

---

### R4: Strict Authority Classification
**Rule**: Authority enum strictly enforced: formal / explanatory_only / deprecated / to_formalize. No ambiguous status allowed.

**Enforcement**: Mandatory

**Violation Action**: Classify or remove

---

### R5: Eliminated Axiom Labeling
**Rule**: Axioms presented as postulates in TXT that are actually proven lemmas must be relabeled as 'eliminated via derivation'.

**Enforcement**: Mandatory

**Violation Action**: Correct status in TXT

**Example**: Identity reflexivity was axiom in PXLv1, proven lemma in PXLv3. TXT must reflect current status.

---

### R6: Verification Claims
**Rule**: All claims of 'zero admits' or 'fully verified' must anchor to proof_index.json compilation_notes with `admits=0`.

**Enforcement**: Mandatory

**Violation Action**: Verify or remove claim

---

## Audit Workflow (Step-by-Step)

### Step 1: Extract All TXT Sections
**Action**: Parse each TXT file and identify distinct sections (by header, topic, or claim type).

**Output**: Section inventory with:
- Section ID (unique identifier)
- Title
- Claim type (axiom / theorem / definition / motivation / example / etc.)

**Tools**: Manual parsing or semi-automated extraction script

---

### Step 2: Map Each Section to Proof IDs
**Action**: For each section, determine:
- Does this assert a formal claim?
- If yes, which proof ID(s) prove it?
- If no, mark as explanatory

**Output**: 
- `maps_to` array (proof IDs or empty)
- `formal_anchor` (specific theorem/axiom name or null)

**Reference**: Use proof_index.json to find proof IDs and their status

---

### Step 3: Compare TXT Claims to Coq Definitions
**Action**: For sections with formal anchors:
- Fetch Coq source from .v file
- Extract formal definition/theorem statement
- Compare to TXT claim character-by-character

**Output**: Match quality assessment (exact / equivalent / approximate / drift)

**Red Flags**:
- TXT uses symbols not in Coq
- TXT asserts stronger claim than Coq proves
- TXT terminology outdated

---

### Step 4: Assign Authority Enum
**Action**: Based on mapping and match quality:
- Has proven anchor? → `formal`
- No anchor, no claim? → `explanatory_only`
- Contradicts code? → `deprecated`
- Claims future work? → `to_formalize`

**Output**: Authority classification for each section

---

### Step 5: Enforce Normalization Rules
**Action**: Apply rules R1-R6 to each section:
- Check for unsupported formal claims (R1)
- Verify symbol parity (R2)
- Validate future work language (R3)
- Confirm authority classification (R4)
- Correct eliminated axiom status (R5)
- Verify verification claims (R6)

**Output**: Action items:
- **Keep**: No changes needed
- **Revise**: Correct symbols, terminology, or status
- **Demote**: Change from formal to explanatory
- **Remove**: Delete section entirely

---

### Step 6: Generate Normalized TXT or Annotations
**Action**: 
- For `keep`: No action
- For `revise`: Edit TXT to match Coq
- For `demote`: Add disclaimer ("Conceptual only — not formally proven")
- For `remove`: Delete section or move to separate "future work" document

**Output**: Clean, normalized TXT files or JSON annotation layer

---

## Critical Violations (Immediate Action Required)

The schema has identified these violations in preliminary audit:

### Violation 1: Eliminated Axiom Mislabeling
**Location**: `pxl_axioms_txt` → `axiom_ident_refl`

**Issue**: TXT presents `ax_ident_refl` as axiom, but it's proven as lemma in PXL_Derivations_Phase2.v.

**Action**: Relabel section as "Identity Reflexivity (proven lemma)" and reference derivation file.

---

### Violation 2: Unsupported Paradox Resolution
**Location**: `pxl_paradox_resolution_txt` → `paradox_liar`

**Issue**: TXT asserts "PXL resolves the liar paradox" but no formal proof exists.

**Action**: Demote to "Conceptual Approach to Liar Paradox" or remove entirely. Cannot claim resolution without proof.

**Severity**: Critical (reviewers will check this)

---

### Violation 3: Unsupported Omnipotence Resolution
**Location**: `pxl_paradox_resolution_txt` → `paradox_omnipotence`

**Issue**: TXT asserts resolution of omnipotence paradox but no formal proof exists.

**Action**: Demote to conceptual approach or remove.

**Severity**: Critical

---

## UI Integration (Minimal)

### Conceptual Panel Toggle
**Location**: Workbench UI (right panel or collapsible section)

**Default State**: Hidden

**Toggle Label**: "Show Conceptual Notes"

**Display Rules**:
- Only show TXT excerpts with `authority='formal'` or `authority='explanatory_only'`
- Never show `authority='deprecated'`
- For `authority='to_formalize'`, show with clear "Future Work" badge

**Badges**:
- Formal: "✓ Proven in [proof_id]" (green, clickable link to proof)
- Explanatory: "ℹ Explanatory Only — No Formal Anchor" (gray)
- Future Work: "⧖ Future Work — Not Yet Formalized" (gold)

**No Mapping Fallback**: If section has no formal anchor, display "Explanatory Only" badge.

---

## Next Steps After Normalization

### 1. Editorial Policy Document
Once normalization is complete, write a 1-page policy stating:
- `.v > TXT` hierarchy
- How to interpret authority badges
- How to verify claims (trace to proof_index.json)

This goes in arXiv submission and website footer.

### 2. Regenerate TXT Files (Optional)
If TXT files have many violations, consider:
- Option A: Edit TXT files directly to comply
- Option B: Generate clean TXT from JSON annotations
- Option C: Deprecate TXT entirely, use JSON + UI rendering

### 3. Reviewer Confidence
Normalized schema allows you to say:
- "Every formal claim is traceable to line X in file Y.v"
- "All speculative content is explicitly labeled"
- "No drift between documentation and code"

This is publication-grade defensibility.

---

## Authority Declaration (For Footer/Policy)

**Recommended Text**:

> **Documentation Authority Hierarchy**
> 
> This system enforces a strict documentation hierarchy:
> 
> 1. **Coq Source Files (.v)** — Canonical truth source. Machine-verified.
> 2. **Proof Registry (proof_index.json)** — Authoritative metadata extracted from build system.
> 3. **Text Documentation (.txt / .md)** — Supportive annotations only. Subordinate to proofs.
> 
> All formal claims in text documentation are anchored to specific proof IDs in the registry. Claims without anchors are explicitly labeled as explanatory or future work.
> 
> To verify any assertion: (1) Check proof_index.json for proof ID, (2) View source in coq/v/, (3) Compile via Coq Makefile.
> 
> **No documentation can override formal verification results.**

---

## Glossary

**Formal Anchor**: Specific theorem, axiom, or definition name in a .v file that proves a TXT claim.

**Proof ID**: Unique identifier in proof_index.json (e.g., `pxl_internal_lem`).

**Authority**: Classification determining whether TXT content makes formal claims or not.

**Normalization**: Process of aligning TXT content with .v files, correcting drift, and enforcing rules.

**Baseline**: Core proven files with zero admits (baseline_admits: 0 in proof_index.json).

**Eliminated Axiom**: Axiom that was proven as lemma, reducing axiom count (16 → 8 in PXL).

---

## Contact / Questions

For normalization questions or edge cases, consult:
1. This operator manual (normalization rules)
2. proof_index.json (proof status and dependencies)
3. .v source files (ground truth)

**Remember**: When in doubt, demote to explanatory rather than assert unsupported claims.
