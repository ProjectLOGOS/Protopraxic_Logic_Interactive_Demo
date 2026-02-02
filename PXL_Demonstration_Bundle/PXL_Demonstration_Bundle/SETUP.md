# PXL Demonstration Bundle - Setup Instructions

## Quick Test (Immediate)

To verify the system works:

1. Rename files:
   ```bash
   mv proof_index.json proof_index_full.json
   mv proof_index_working.json proof_index.json
   ```

2. Open `index.html` in browser

3. Click "Compile PXL"

4. Expected: Test_Compilation.v compiles successfully

**This proves jsCoq integration is working.**

---

## Full System (Requires .v Files)

The full system requires 65 .v files. Currently missing:

To populate:

1. Copy all .v files from source repository to paths specified in `proof_index_full.json`

2. Structure:
   ```
   coq/src/
   ├── PXL_Definitions.v
   ├── PXL_Kernel_Axioms.v
   ├── PXLv3.v
   ├── baseline/
   │   ├── PXL_Internal_LEM.v
   │   ├── PXL_Global_Bijection.v
   │   └── ...
   └── ...
   ```

3. Restore full registry:
   ```bash
   mv proof_index.json proof_index_working.json
   mv proof_index_full.json proof_index.json
   ```

4. Open `index.html` and compile

---

## Files Included

**Working (Test)**:
- `coq/src/Test_Compilation.v` - Minimal test file
- `proof_index_working.json` - Single file registry

**Full System (Needs .v files)**:
- `proof_index_full.json` - Complete 65-file registry
- `coq/src/` - Empty, awaiting .v files

**UI & Integration**:
- `index.html` - Main interface
- `css/pxl.css` - Styling
- `js/` - jsCoq integration + navigation + conceptual panel

**Documentation**:
- `docs/` - Normalization files + editorial policy + technical docs

---

## Missing .v Files

The following 65 .v files are referenced in `proof_index_full.json` but not present:

1. PXL_Definitions.v
2. PXL_Derivations_Phase2.v
3. PXL_Structural_Derivations.v
4. S5_Kripke.v
5. PXL_Modal_Semantic_Kripke.v
6. PXL_Modal_Axioms_Semantic.v
7. PXL_Kernel_Axioms.v
8. PXLv3.v
9. PXLv3_shadow.v
10. PXL_Axiom_Minimality_Check.v
11. PXL_Internal_LEM.v
12. Godelian_Theorem_Satisfaction.v
13. PXL_Global_Bijection.v
... (62 more)

Copy these from source repository to complete the full demonstration.

---

## Verification

**Test works**: jsCoq integration operational  
**Full system**: Requires .v file population
