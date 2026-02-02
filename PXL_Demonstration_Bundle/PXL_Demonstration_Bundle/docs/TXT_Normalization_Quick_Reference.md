# TXT Normalization — Quick Reference Card

## Authority Badges (What Can This Claim?)

### ✓ Formal Proof
**Color**: Green (#4a9e6e)  
**Meaning**: Proven by .v files, zero admits  
**Requirements**: Maps to `status='proven'` proof ID  
**Action**: Clickable link to proof source  
**Trust**: Verified by Coq compiler  

### ℹ Explanatory Only
**Color**: Gray (#8a8880)  
**Meaning**: Narrative/motivation, no formal claims  
**Requirements**: Empty `maps_to`, null anchor  
**Action**: Read as context only  
**Trust**: Not verified, conceptual only  

### ⚠ Deprecated
**Color**: Red (#b55a6a)  
**Meaning**: Conflicts with code, outdated  
**Requirements**: Contradicts current system  
**Action**: HIDDEN (never shown in UI)  
**Trust**: Do not use  

### ⧖ Future Work
**Color**: Gold (#c9a84c)  
**Meaning**: Not yet formalized, planned  
**Requirements**: Maps to `skeleton` or `empty` only  
**Action**: Treat as conceptual approach  
**Trust**: Speculative, not proven  

---

## Status Indicators (What's the Proof State?)

### Covered
**Meaning**: Formal anchor exists, claim matches  
**Reliability**: High  
**Action**: Verify via proof ID  

### Eliminated
**Meaning**: Was axiom, now proven lemma  
**Reliability**: High (better than original)  
**Action**: Check derivation file  

### Partial
**Meaning**: Proof incomplete (admits > 0)  
**Reliability**: Medium  
**Action**: Check admit count, review carefully  

### Unsupported
**Meaning**: No formal anchor, cannot verify  
**Reliability**: None  
**Action**: Demote to explanatory or remove  

### Non-Formal
**Meaning**: No formal claim intended  
**Reliability**: N/A  
**Action**: Treat as prose only  

---

## Match Quality (How Close is TXT to Code?)

### Exact
**Symbol parity**: ✓  
**Structure parity**: ✓  
**Action**: None needed  

### Equivalent
**Symbol parity**: Minor differences (e.g., 𝕆 vs NB)  
**Structure parity**: ✓  
**Action**: Document symbol mapping  

### Approximate
**Symbol parity**: ✗  
**Structure parity**: Partial  
**Action**: Revise TXT to match code  

### Drift
**Symbol parity**: ✗  
**Structure parity**: ✗  
**Action**: Full normalization required  

### N/A
**Meaning**: Explanatory content, no formal claim  
**Action**: None needed  

---

## Decision Flowchart

```
Does TXT assert formal claim?
├─ NO
│  └─ authority: explanatory_only
│     └─ Display: ℹ Explanatory Only
│
└─ YES
   └─ Does proof ID exist?
      ├─ NO
      │  ├─ Future work? → authority: to_formalize → Display: ⧖ Future Work
      │  └─ Conflicts? → authority: deprecated → Display: HIDDEN
      │
      └─ YES
         └─ Proof status?
            ├─ proven (admits: 0)
            │  └─ authority: formal → Display: ✓ Formal Proof
            │
            ├─ partial (admits > 0)
            │  └─ authority: formal, status: partial → Display with caveat
            │
            └─ skeleton/empty
               └─ authority: to_formalize → Display: ⧖ Future Work
```

---

## Critical Rules (Never Violate)

### R1: No Unsupported Claims
❌ "PXL proves completeness"  
✓ "PXL provides a framework for investigating completeness (future work)"

### R2: Symbol Parity
❌ TXT uses `⊢` but code uses `entails`  
✓ Both use `entails` or TXT explains symbol mapping

### R3: Future Work Discipline
❌ "PXL resolves the liar paradox"  
✓ "PXL offers a conceptual approach to the liar paradox (to be formalized)"

### R4: Authority Classification
❌ Ambiguous status between formal and explanatory  
✓ Clear badge with explicit authority enum

### R5: Eliminated Axiom Labeling
❌ "Axiom: Identity is reflexive"  
✓ "Theorem (proven lemma): Identity is reflexive"

### R6: Verification Claims
❌ "All proofs compile with zero admits" (unsourced)  
✓ "All proofs compile with zero admits (per proof_index.json: baseline_admits = 0)"

---

## Common Audit Questions

**Q**: TXT says "proven" but I can't find the proof ID?  
**A**: FAIL — Demote to explanatory or find proof

**Q**: TXT uses different symbols than code?  
**A**: Document mapping or normalize TXT to match code

**Q**: TXT claims future result as if completed?  
**A**: FAIL — Relabel as future work or remove

**Q**: Proof has admits > 0 but TXT says "proven"?  
**A**: FAIL — Add caveat or change status to partial

**Q**: TXT is conceptual narrative with no claims?  
**A**: PASS — Authority: explanatory_only

---

## For Reviewers

**To verify a TXT claim:**

1. Find section in `txt_normalization_schema.json`
2. Check `authority` field
3. If `formal`, check `maps_to` array
4. Look up proof ID in `proof_index.json`
5. Verify `status: "proven"` and `admits: 0`
6. View source in `coq/v/[filename]`
7. Compile via Coq Makefile if skeptical

**Red flags:**
- `authority: to_formalize` but claims completion
- `authority: formal` but no proof ID
- `match_quality: drift` without revision plan
- `status: unsupported` but asserts necessity

---

## For Authors

**Adding new TXT content:**

1. Write section
2. Complete `Section_Audit_Template.md`
3. Add entry to `txt_normalization_schema.json`
4. If formal claim, ensure proof exists first
5. If explanatory, set `authority: explanatory_only`
6. Test in UI, verify badge displays correctly

**Modifying existing TXT:**

1. Find section in schema
2. Check current authority/status
3. Make edits maintaining parity
4. Update schema if formal anchor changes
5. Re-verify badge in UI

---

## Contact

**Questions**: See `TXT_Normalization_Manual.md`  
**Edge cases**: Consult schema, then proof source  
**When uncertain**: Demote to explanatory  

**Remember**: `.v files > TXT files` (always)
