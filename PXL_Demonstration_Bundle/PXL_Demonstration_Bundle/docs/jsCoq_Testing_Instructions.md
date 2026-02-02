# jsCoq Integration — Testing Instructions

## Quick Verification Test

To verify the jsCoq integration is working before populating all 65 .v files:

### Step 1: Use Test Configuration

Temporarily rename files:
```bash
mv proof_index.json proof_index_full.json
mv proof_index_test.json proof_index.json
```

### Step 2: Open in Browser

Open `index.html` in a modern browser (Chrome, Firefox, Edge)

### Step 3: Expected Behavior

**On Page Load (2-3 seconds):**
- Console shows: "Loading jsCoq..."
- Console shows: "Starting jsCoq..."
- Console shows: "jsCoq started successfully"
- Compiler panel shows: "jsCoq ready. Click 'Compile PXL' to verify proofs."

**Click "Compile PXL" Button:**
- Button changes to "Compiling..." and disables
- See messages:
  ```
  Building compilation queue...
  Compiling 1 proven modules...
  [1/1] Loading Test Compilation...
  [1/1] Compiling Test Compilation...
  [1/1] ✓ Test Compilation
  All 1 modules compiled successfully
  ```

**If This Works:**
- jsCoq integration is operational
- Real Coq compilation is executing
- Ready to populate full .v files

**If This Fails:**

Common errors and solutions:

1. **"File not found: coq/v/test/Test_Compilation.v"**
   - Ensure Test_Compilation.v exists in coq/v/test/
   - Check file path matches exactly

2. **"jsCoq not initialized"**
   - Check browser console for errors
   - Verify jsCoq loaded from CDN (check Network tab)
   - Try refreshing page

3. **"Coq error: ..."**
   - Check browser console for detailed Coq error
   - Verify Test_Compilation.v syntax is valid
   - This indicates jsCoq IS working but Coq code has issue

---

## Full System Test

After test works, restore full configuration:

### Step 1: Restore Configuration
```bash
mv proof_index.json proof_index_test.json
mv proof_index_full.json proof_index.json
```

### Step 2: Populate .v Files

Copy all 65 .v files from source repository to paths specified in proof_index.json

Example structure:
```
coq/v/
├── src/
│   ├── PXL_Definitions.v
│   ├── PXL_Kernel_Axioms.v
│   ├── PXLv3.v
│   ├── baseline/
│   │   ├── PXL_Internal_LEM.v
│   │   ├── PXL_Global_Bijection.v
│   │   └── ...
│   └── ...
```

### Step 3: Run Full Compilation

Open index.html, click "Compile PXL"

**Expected:**
- All 65 proven modules compile in dependency order
- Takes 10-30 seconds depending on browser/machine
- Green checkmarks for each successful module
- Final success message

**If compilation fails:**
- Error shows which module failed
- Error shows specific Coq error message
- Check that module and its dependencies exist
- Verify module syntax is valid

---

## Debugging

### Browser Console

Open browser DevTools (F12) and check Console tab for:
- jsCoq initialization messages
- Proof registry loading
- Compilation order
- Detailed error messages

### Network Tab

Check Network tab to verify:
- jsCoq library loads from CDN (jscoq.js)
- proof_index.json loads successfully
- .v files load successfully (status 200)

### Common Issues

**jsCoq not loading:**
- Check internet connection (jsCoq loads from CDN)
- Try different CDN: unpkg.com vs cdn.jsdelivr.net
- Check browser compatibility (needs ES6 and WebAssembly)

**Files not found:**
- Verify file paths in proof_index.json match actual filesystem
- Check case sensitivity (Linux/Mac are case-sensitive)
- Use browser DevTools Network tab to see failed requests

**Compilation errors:**
- Read Coq error message carefully
- Check if dependencies are missing
- Verify module compiles standalone in desktop Coq
- Check for syntax errors or admits

---

## Performance Notes

**First Run:**
- jsCoq initializes (~2-3 seconds)
- Coq standard library loads
- Then compilation begins

**Subsequent Runs:**
- Still recompiles everything (no caching yet)
- Each run is independent
- WebAssembly runtime is fast (~500ms per module)

**Large Codebase:**
- 65 modules = ~10-30 seconds total
- Browser may become briefly unresponsive
- This is normal for client-side compilation

---

## Success Criteria

Integration is working correctly if:

✓ Page loads without errors  
✓ jsCoq ready message appears  
✓ Compile button is clickable  
✓ Test file compiles successfully  
✓ Real Coq errors appear if syntax is invalid  
✓ Compilation halts on first error  
✓ Success message shows when all modules compile  

---

## Next Steps After Verification

1. **Populate Full .v Files**: Copy all 65 modules to correct paths
2. **Run Full Compilation**: Verify all proofs compile
3. **Fix Any Errors**: Address compilation failures
4. **Deploy**: System ready for use

---

## Technical Verification

To verify real Coq execution (not simulation):

1. **Break Test File**: Add invalid Coq syntax to Test_Compilation.v
   ```coq
   Lemma broken : forall x, x = x + 1.  (* This is false *)
   Proof. reflexivity. Qed.  (* This will fail *)
   ```

2. **Compile**: Click "Compile PXL"

3. **Expect Real Error**: Should see actual Coq error like:
   ```
   Error: Unable to unify "x" with "x + 1"
   ```

4. **This Confirms**: jsCoq is really compiling, not simulating

---

## File Checklist

Required files for integration to work:

- [x] index.html (with jsCoq CDN links)
- [x] js/jscoq_loader.js (real implementation)
- [x] css/pxl.css (compilation feedback styles)
- [x] proof_index.json (or proof_index_test.json for testing)
- [x] coq/v/test/Test_Compilation.v (for testing)
- [ ] coq/v/src/*.v (65 files for full system)

---

**Status**: Integration complete and ready for testing
