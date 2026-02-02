# PXL Editorial Policy

## Documentation Authority Hierarchy

This system enforces a strict, non-negotiable documentation hierarchy:

### 1. Coq Source Files (.v) — Canonical Truth
- Machine-verified formal proofs
- Compiled via Coq 8.19+ with zero admits in baseline
- Located in `coq/v/` directory
- **Authority**: Absolute

### 2. Proof Registry (proof_index.json) — Authoritative Metadata
- Extracted directly from build system and `.Makefile.d` dependency tracking
- Contains: proof status, dependencies, admit counts, file paths
- Single source of truth for system state
- **Authority**: Derived from .v files

### 3. Text Documentation — Supportive Annotations Only
- Conceptual explanations, motivation, examples
- **Subordinate to formal proofs at all times**
- May not assert formal claims without anchoring to proven proof IDs
- **Authority**: Explanatory only, unless explicitly anchored

---

## Verification Principle

**All formal claims in text documentation are traceable to specific proof IDs in the registry.**

To verify any assertion:
1. Check `proof_index.json` for proof ID
2. View source in `coq/v/[filename]`
3. Compile via Coq Makefile to confirm zero admits

**No documentation can override formal verification results.**

---

## Authority Classifications

### ✓ Formal Proof
- **Definition**: Claims proven by listed .v files with `status='proven'` and `admits=0`
- **Display**: Green badge with clickable link to source
- **Trust Level**: Verified by Coq compiler
- **Usage**: May be cited as proven results

### ℹ Explanatory Only
- **Definition**: Narrative, motivation, or examples with no formal claims
- **Display**: Gray badge, clearly labeled as non-formal
- **Trust Level**: Conceptual only, not verified
- **Usage**: Read as context, not as proven assertions

### ⧖ Future Work
- **Definition**: Planned formalization, not yet proven
- **Display**: Gold badge with "Future Work" label
- **Trust Level**: Speculative, pending formal proof
- **Usage**: Treat as research directions, not completed results

### ⚠ Deprecated (Hidden)
- **Definition**: Conflicts with or superseded by current code
- **Display**: Never shown in UI
- **Trust Level**: None — do not use
- **Usage**: Excluded from all displays

---

## Normalization Rules

### R1: No Unsupported Formal Claims
Text may not assert necessity, completeness, consistency, or resolution without anchoring to a proven proof ID.

**Violation Example**: "PXL resolves the liar paradox" (no proof exists)  
**Compliant Example**: "PXL offers a conceptual approach to the liar paradox (future work)"

### R2: Symbol and Terminology Parity
All symbols and terms must match .v files exactly, or explicitly document mapping.

**Violation Example**: Text uses `⊢` while code uses `entails` (undocumented)  
**Compliant Example**: Both use `entails`, or text states "⊢ represents entails in code"

### R3: Future Work Discipline
Content claiming future results must map to `status='skeleton'` or `status='empty'` proof IDs only.

**Violation Example**: Presenting speculative result as if completed  
**Compliant Example**: Clearly labeling as future work or conceptual approach

### R4: Eliminated Axiom Transparency
Axioms that are now proven lemmas must be labeled as eliminated/derived, not primitive.

**Violation Example**: "Axiom: Identity is reflexive" (when proven as lemma)  
**Compliant Example**: "Theorem (proven lemma): Identity is reflexive"

### R5: Verification Claim Accountability
All claims about compilation, admits, or verification status must anchor to `proof_index.json`.

**Violation Example**: "All proofs verified" (unsourced)  
**Compliant Example**: "All baseline proofs compile with zero admits (per proof_index.json: baseline_admits = 0)"

### R6: Status Discipline
Authority classification must be unambiguous: formal / explanatory_only / to_formalize / deprecated.

**Violation Example**: Ambiguous status between formal and explanatory  
**Compliant Example**: Clear badge with explicit authority enum

---

## For Authors

**Adding text content:**
1. Write section with clear claim type (definition / theorem / motivation / example)
2. If asserting formal claim, ensure proof exists first with `status='proven'`
3. If explanatory only, set `authority='explanatory_only'` in normalization schema
4. Add entry to appropriate normalization JSON file (e.g., `pxl_theorems_normalized.json`)
5. Verify badge displays correctly in UI

**Modifying existing content:**
1. Find section in normalization schema
2. Maintain symbol/terminology parity with .v files
3. Update schema if formal anchor changes
4. Re-verify in UI

---

## For Reviewers

**To verify a text claim:**
1. Locate section in normalization JSON (e.g., `docs/pxl_axioms_normalized.json`)
2. Check `authority` field — must be `formal` for formal claims
3. Verify `maps_to` array contains valid proof ID
4. Look up proof ID in `proof_index.json`
5. Confirm `status: "proven"` and `admits: 0`
6. View source in `coq/v/[filename]` to verify claim matches code
7. If skeptical, compile via Coq Makefile

**Red flags:**
- `authority: to_formalize` but claims completion
- `authority: formal` but no proof ID mapping
- `status: unsupported` but asserts necessity
- `match_quality: drift` without correction plan

---

## Critical Violations (Immediate Rejection)

The following constitute immediate grounds for rejection or correction:

1. **Unsupported Formal Claims**: Asserting theorems, completeness, consistency, or resolution without proven proof ID
2. **Status Misrepresentation**: Presenting eliminated axioms as primitive, or speculative work as completed
3. **Verification Fabrication**: Claiming zero admits or full verification without proof_index.json anchor
4. **Authority Ambiguity**: Failing to clearly label content as formal vs. explanatory

---

## UI Enforcement

The PXL workbench enforces this policy programmatically:

- **Conceptual Panel** displays text content only when user requests it
- **Authority Badges** clearly distinguish formal from explanatory content
- **Deprecated Content** never displayed under any circumstances
- **Proof Links** allow direct verification of formal claims
- **No Mapping Fallback** displays "Explanatory Only" when no formal anchor exists

---

## Modification Protocol

This policy may only be modified by:
1. Updating the authority hierarchy (requires formal justification)
2. Adding normalization rules (must maintain .v > TXT principle)
3. Clarifying existing rules (no substantive changes)

**The core principle `.v files > TXT files` is non-negotiable.**

---

## Version History

**v1.0** (2026-02-01): Initial policy  
**Status**: Active  
**Authority**: Derived from PXL normalization schema and proof registry

---

## Contact

For policy questions:
- Normalization rules → `TXT_Normalization_Manual.md`
- Authority definitions → `TXT_Normalization_Quick_Reference.md`
- Proof status → `proof_index.json`
- Source verification → `coq/v/*.v`

**When uncertain**: Demote to explanatory rather than assert unsupported claims.
