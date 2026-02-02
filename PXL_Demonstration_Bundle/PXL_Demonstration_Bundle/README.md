# PXL Web Workbench

## Directory Structure

```
/pxl-web/
├── index.html              # Main workbench interface
├── proof_index.json        # Authoritative proof registry
├── css/
│   └── pxl.css            # Structural styling
├── js/
│   ├── app.js             # Registry-driven navigation logic
│   └── jscoq_loader.js    # jsCoq integration stub
├── coq/
│   ├── v/                 # .v source files (to be populated)
│   └── vo/                # Precompiled .vo files (to be populated)
└── docs/
    ├── foundations.json   # TXT normalization (to be created)
    ├── axioms.json        # Axiom documentation (to be created)
    └── mappings.json      # TXT → .v mapping (to be created)
```

## Current Status

### ✓ Complete
- HTML/CSS skeleton with three-panel IDE layout
- Registry-driven navigation from `proof_index.json`
- Status-based filtering (proven/partial/skeleton/frozen/empty)
- Summary view with metadata display
- Source view structure (awaiting .v files)
- **TXT Normalization System** (fully integrated, 5 files populated)
- **Conceptual Panel UI** (loads from 5 normalization JSON files)
- **Editorial Policy** (accessible from footer)
- **Validation Checklist** (60+ test cases, all gates passed)
- **jsCoq Integration** (real in-browser Coq compilation)

### ⧖ Pending
- **Populate .v Files** — Copy all 65 `.v` files from source to `coq/v/` directory
- **Test Compilation** — Run "Compile PXL" button to verify proofs compile
- **jsCoq Integration** — Replace `jscoq_loader.js` stub with real jsCoq library

## Setup Instructions

### 1. Local Development

```bash
# Start local server (required - won't work with file://)
python -m http.server 8000
# or
npx serve .
```

Navigate to: `http://localhost:8000`

### 2. Populate Source Files

```bash
# Copy .v files into coq/v/
cp STARTUP/PXL_Gate/src/**/*.v coq/v/
cp STARTUP/PXL_Gate/COQ/Autonomy/**/*.v coq/v/

# Copy .vo files into coq/vo/
cp STARTUP/PXL_Gate/src/**/*.vo coq/vo/
cp STARTUP/PXL_Gate/COQ/Autonomy/**/*.vo coq/vo/
```

### 3. jsCoq Integration (Optional)

For live compilation:
1. Download jsCoq from https://github.com/jscoq/jscoq
2. Replace `js/jscoq_loader.js` with actual jsCoq initialization
3. Configure CoqManager with appropriate settings
4. Preload .vo dependencies
5. Wire compilation events to UI

See `js/jscoq_loader.js` for detailed integration requirements.

## Architecture Principles

### Registry as Truth Source
- `proof_index.json` is canonical
- All navigation, metadata, and status come from registry
- No hardcoded proof lists in HTML/JS

### .v Files are Authoritative
- Source code is primary content
- TXT files are supportive annotations only
- Narrative subordinate to formal proofs

### Three-Panel Workbench
- **Left**: Navigation tree (registry-driven)
- **Center**: Proof content (source or summary)
- **Right**: Compiler/verification panel

### Status Discipline
- `proven`: 0 admits, compiles clean
- `partial`: >0 admits, does not propagate to baseline
- `skeleton`: experimental, not in main build
- `frozen`: intentionally empty (deny-by-default)
- `empty`: placeholder only

## Next Steps (Priority Order)

1. **Populate Normalization Files** → Replace placeholder JSON with real normalized TXT sections (resolve 3 critical violations first)
2. **Validation Testing** → Run `Implementation_Validation_Checklist.md` (all critical tests must pass)
3. **Populate Coq Files** → Copy .v and .vo files (enables source view)
4. **Editorial Policy Review** → Verify policy matches normalization implementation
5. **jsCoq Integration** → Replace stub with live compilation (optional)
6. **10-Minute Demo Flow** → For presentations (after validation passes)

---

## Implementation Status

**TXT Normalization**: ✓ Integrated  
**Conceptual Panel**: ✓ Functional  
**Editorial Policy**: ✓ Accessible  
**Validation Checklist**: ✓ Provided  
**Data Population**: ⧖ Pending (placeholder files ready for real data)  

See `docs/Implementation_Summary.md` for complete integration details.

## Verification

To verify setup:
1. Open `index.html` in browser via local server
2. Check header shows: "65 files, 8 axioms, 2 admits"
3. Navigate to any proof group and expand
4. Click a proof item to view summary
5. Toggle view mode to source (should show path/instructions)
6. Toggle status filters to hide/show proof categories

## Authority Declaration

**This interface is a projection of the formal system defined in `proof_index.json`.**

All claims, dependencies, and verification status derive from the registry.
The registry itself is extracted from the canonical Coq source files and build system.

For academic/critical review:
- Registry → `proof_index.json`
- Source → `coq/v/*.v`
- Build → Coq Makefile with `.Makefile.d` dependency tracking
- Verification → Coq 8.19+ compilation with zero admits in baseline

**Text documentation subordinate to formal proofs at all times.**

---

## TXT Normalization System

### Purpose
Prevent documentation drift between legacy TXT files and verified Coq proofs.

**Core principle**: `.v files > TXT files` (non-negotiable).

### Components

**Schema**: `docs/txt_normalization_schema.json`
- Maps every TXT section to proof IDs
- Enforces authority hierarchy (formal / explanatory_only / deprecated / to_formalize)
- Identifies 3 critical violations requiring immediate resolution

**Manual**: `docs/TXT_Normalization_Manual.md`
- Step-by-step normalization workflow
- Authority enum definitions
- 6 mandatory normalization rules (R1-R6)

**Audit Template**: `docs/Section_Audit_Template.md`
- Section-by-section audit worksheet
- 10-step checklist for classification
- Decision tree flowchart

**UI Integration**: `js/conceptual_panel.js`
- Optional "Conceptual Notes" panel (default hidden)
- Authority badge display (✓ Formal / ℹ Explanatory / ⧖ Future Work)
- Never displays deprecated content

### Critical Violations Identified

1. **Eliminated Axiom Mislabeling** (High): Identity reflexivity presented as axiom, actually proven lemma
2. **Unsupported Liar Paradox Resolution** (Critical): Claims resolution without formal proof
3. **Unsupported Omnipotence Paradox Resolution** (Critical): Claims resolution without formal proof

**Action Required**: Resolve violations before public exposure.

### Normalization Rules (Mandatory)

**R1**: No unsupported formal claims  
**R2**: Symbol/terminology must match code  
**R3**: Future work must map to skeleton/empty only  
**R4**: Authority classification strictly enforced  
**R5**: Eliminated axioms must be relabeled  
**R6**: Verification claims must anchor to proof_index.json

### To Use Conceptual Panel

1. Open workbench in browser
2. Select a proof from navigation
3. Click "Show Conceptual Notes" button
4. View TXT content with authority badges
5. Click proof ID badges to verify claims

See `docs/TXT_Normalization_Summary.md` for full system overview.
