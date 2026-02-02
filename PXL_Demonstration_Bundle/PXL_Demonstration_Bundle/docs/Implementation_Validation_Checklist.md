# TXT Normalization Implementation — Validation Checklist

## Pre-Flight Check

### Files Present
- [ ] `docs/pxl_axioms_normalized.json`
- [ ] `docs/pxl_theorems_normalized.json`
- [ ] `docs/pxl_foundations_normalized.json`
- [ ] `docs/pxl_domain_mappings_normalized.json`
- [ ] `docs/pxl_paradox_resolutions_normalized.json`
- [ ] `docs/EDITORIAL_POLICY.md`
- [ ] `docs/normalization_template.json`
- [ ] `js/conceptual_panel.js`

### File Structure
- [ ] Each normalized JSON has `doc_id`, `source`, `sections` fields
- [ ] Each section has `section_id`, `title`, `claim_type`, `maps_to`, `authority`, `status` fields
- [ ] Authority enum values are one of: `formal`, `explanatory_only`, `deprecated`, `to_formalize`
- [ ] Status enum values are one of: `covered`, `eliminated`, `partial`, `unsupported`, `non-formal`

---

## UI Integration Tests

### Conceptual Panel Visibility
- [ ] Panel is hidden by default when workbench loads
- [ ] "Show Conceptual Notes" button appears in file actions toolbar
- [ ] Clicking button opens conceptual panel
- [ ] Clicking button again (or close button) hides panel
- [ ] Panel label updates: "Show" ↔ "Hide"

### Content Loading
- [ ] Selecting a proof with mapped TXT content displays sections in panel
- [ ] Selecting a proof with no mapped content shows "No Conceptual Notes" message
- [ ] Failed file loads show error message with instructions
- [ ] Multiple sections from different documents can appear for single proof

### Authority Badges
- [ ] `authority: formal` → Green "✓ Proven in [proof_id]" badge
- [ ] `authority: explanatory_only` → Gray "ℹ Explanatory Only" badge
- [ ] `authority: to_formalize` → Gold "⧖ Future Work" badge
- [ ] `authority: deprecated` → Content NEVER displayed (hidden by filter)
- [ ] Badge colors match CSS variables (formal=#4a9e6e, explanatory=#8a8880, future=#c9a84c)

### Status Badges
- [ ] Each section displays status badge alongside authority badge
- [ ] Status values render correctly: covered, eliminated, partial, unsupported, non-formal
- [ ] Status colors are distinct from authority colors

### Content Sections
- [ ] Section title displays correctly
- [ ] TXT claim box appears when `txt_claim` is present
- [ ] Coq definition box appears when `coq_definition` is present
- [ ] Notes box appears when `notes` is present
- [ ] Source reference displays at bottom of section
- [ ] Match quality displays at bottom of section

### Deprecated Content Filtering
- [ ] Sections with `authority: deprecated` never appear in UI
- [ ] No toggle or setting can reveal deprecated content
- [ ] Console confirms deprecated sections are filtered during load

---

## Editorial Policy Tests

### Policy Access
- [ ] Footer contains link to "Editorial Policy"
- [ ] Clicking link opens EDITORIAL_POLICY.md in new tab
- [ ] Policy document is readable and well-formatted
- [ ] Policy clearly states `.v files > TXT files` hierarchy

### Policy Enforcement
- [ ] UI only displays formal claims when mapped to `status='proven'` proofs
- [ ] Explanatory content is visually secondary (gray badge, smaller text)
- [ ] Future work content clearly labeled with conditional language
- [ ] No content appears without explicit proof mapping or explanatory label

---

## Data Integrity Tests

### Proof ID Mapping
- [ ] `maps_to` array in normalized JSON matches `id` field in proof_index.json
- [ ] Clicking proof in navigation shows all sections that map to it
- [ ] Sections only appear for proofs they explicitly map to
- [ ] Empty `maps_to` array results in "No Mapping" display

### Authority Hierarchy
- [ ] proof_index.json drives primary navigation (left panel)
- [ ] Normalized JSON drives secondary content (conceptual panel)
- [ ] .v files remain source of truth (referenced, not replaced)
- [ ] No TXT content appears in main content panel (only in conceptual panel)

### Cross-File Consistency
- [ ] Proof IDs in normalized JSON exist in proof_index.json
- [ ] Formal anchors in normalized JSON match theorem/axiom names in .v files
- [ ] Status claims match compilation results (zero admits where claimed)

---

## Error Handling Tests

### Missing Files
- [ ] Missing normalization JSON logs warning but doesn't crash
- [ ] Missing EDITORIAL_POLICY.md shows "Policy not found" message
- [ ] Missing proof_index.json shows error in navigation panel

### Malformed Data
- [ ] JSON parse errors caught and logged
- [ ] Missing required fields handled gracefully
- [ ] Invalid authority/status values default to safe fallback

### Network Failures
- [ ] Fetch failures show error message in conceptual panel
- [ ] Retry mechanism or manual refresh available
- [ ] Main workbench remains functional even if normalization fails

---

## Performance Tests

### Load Time
- [ ] All normalization files load in <1 second
- [ ] Panel opens/closes instantly (<100ms)
- [ ] Switching between proofs updates panel in <200ms

### Memory
- [ ] No memory leaks after opening/closing panel 50+ times
- [ ] No duplicate event listeners accumulating
- [ ] Console clear of repeated warnings or errors

---

## Accessibility Tests

### Keyboard Navigation
- [ ] Toggle button reachable via Tab key
- [ ] Panel closable via Escape key
- [ ] Proof links in badges navigable via Tab

### Screen Readers
- [ ] Authority badges have accessible labels
- [ ] Status badges have accessible labels
- [ ] Panel state changes announced (opened/closed)

### Visual Clarity
- [ ] Badge colors distinguishable for colorblind users
- [ ] Text contrast meets WCAG AA standards
- [ ] Font sizes readable at default zoom

---

## Regression Tests

### Existing Features
- [ ] Navigation panel still functions correctly
- [ ] Main content panel still displays proof summaries
- [ ] Source view toggle still works
- [ ] Status filters still function
- [ ] Compile button still present (even if stub)

### Layout
- [ ] Three-panel layout maintained (nav / content / compiler)
- [ ] Panels resize correctly
- [ ] Conceptual panel doesn't break layout when opened
- [ ] Footer remains fixed at bottom

---

## Documentation Tests

### README
- [ ] Updated with TXT normalization section
- [ ] Lists all new files in directory structure
- [ ] Explains how to populate normalized JSON files
- [ ] Points to EDITORIAL_POLICY.md for authority rules

### Inline Comments
- [ ] conceptual_panel.js has clear comments
- [ ] File loading logic documented
- [ ] Badge rendering logic documented

---

## Critical Validation (Must Pass)

### Authority Hierarchy Enforced
- [ ] **CRITICAL**: .v files are never replaced or modified
- [ ] **CRITICAL**: proof_index.json remains sole driver of navigation
- [ ] **CRITICAL**: TXT content only appears in optional conceptual panel
- [ ] **CRITICAL**: Deprecated content never displayed under any circumstances

### No Scope Creep
- [ ] **CRITICAL**: No redesign of layout
- [ ] **CRITICAL**: No new features beyond normalization integration
- [ ] **CRITICAL**: No modification of proof_index.json structure
- [ ] **CRITICAL**: No changes to core navigation or content display logic

### Mechanical Implementation
- [ ] **CRITICAL**: Normalization JSON consumed exactly as provided
- [ ] **CRITICAL**: No reinterpretation or "improvement" of text content
- [ ] **CRITICAL**: No merging or simplification of normalization artifacts
- [ ] **CRITICAL**: Filenames and IDs match exactly as specified

---

## Sign-Off

**Implementation Validated By**: `_______________`  
**Date**: `_______________`  
**All Critical Tests Passed**: [ ] YES / [ ] NO  
**Ready for Production**: [ ] YES / [ ] NO  

**Notes**:
```
_______________________________________________
_______________________________________________
_______________________________________________
```

---

## Failure Resolution

If any critical test fails:
1. Identify which component violated constraints
2. Revert to last known good state
3. Re-implement mechanically per spec
4. Re-run full validation checklist
5. Do not proceed until all critical tests pass

**Remember**: This is a verification workbench, not a presentation layer.
