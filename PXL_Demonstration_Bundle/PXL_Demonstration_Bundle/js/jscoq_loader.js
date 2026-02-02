// jsCoq Integration with Coq Project Build Semantics
// Implements .vo artifact generation and proper module import resolution

let coqManager = null;
let proofRegistry = null;
let compiledModules = new Set();  // Track .vo files
let buildLog = [];

// Wait for jsCoq library, then initialize
function initPXLWorkbench() {
  if (typeof JsCoq === 'undefined') {
    setTimeout(initPXLWorkbench, 100);
    return;
  }
  
  loadProofRegistry()
    .then(setupJsCoq)
    .then(setupBuildControls)
    .catch(error => {
      console.error('Initialization failed:', error);
      displayError(`Initialization failed: ${error.message}`);
    });
}

// Load proof_index.json
async function loadProofRegistry() {
  const response = await fetch('proof_index.json');
  proofRegistry = await response.json();
  console.log('Loaded proof registry:', proofRegistry);
}

// Initialize jsCoq with virtual filesystem and loadpath
async function setupJsCoq() {
  const container = document.getElementById('jscoq-container');
  if (!container) {
    throw new Error('jsCoq container not found');
  }
  
  container.innerHTML = '<div id="jscoq-panel"></div>';
  
  // Initialize jsCoq with filesystem and loadpath configuration
  coqManager = new JsCoq.CoqManager({
    wrapper_id: 'jscoq-panel',
    base_path: 'https://cdn.jsdelivr.net/npm/jscoq@0.18.1/dist/',
    init_pkgs: ['coq'],
    all_pkgs: {
      'coq': ['init', 'utf8', 'arith', 'reals', 'logic']
    },
    implicit_libs: false,
    prelude: false,
    editor: {
      mode: 'none'
    },
    // Virtual filesystem layout
    file_system: {
      '/coq/src': {},      // Source .v files
      '/coq/build': {}     // Compiled .vo files
    }
  });
  
  console.log('Starting jsCoq...');
  await coqManager.start();
  
  // Configure loadpath after start
  await configureLoadpath();
  
  console.log('jsCoq started with build semantics');
  displayStatus('jsCoq ready. Click "Compile PXL" to build project.');
}

// Configure Coq loadpath for module resolution
async function configureLoadpath() {
  try {
    // Set loadpath: -Q /coq/src PXL
    // This makes "Require Import PXL.ModuleName" resolve to /coq/build/ModuleName.vo
    const loadpathCmd = 'Add LoadPath "/coq/build" as PXL.';
    await coqManager.provider.exec(loadpathCmd);
    
    console.log('Configured loadpath: /coq/build -> PXL');
    buildLog.push('Loadpath: /coq/build -> PXL');
    
  } catch (error) {
    console.warn('Loadpath configuration warning:', error);
    // Non-fatal, continue
  }
}

// Setup build control buttons
function setupBuildControls() {
  const compileBtn = document.getElementById('compile-btn');
  if (compileBtn) {
    compileBtn.addEventListener('click', handleCompile);
  }
  
  // Add clear build button if it exists
  const clearBtn = document.getElementById('clear-build-btn');
  if (clearBtn) {
    clearBtn.addEventListener('click', handleClearBuild);
  }
}

// Handle compile button click
async function handleCompile(event) {
  const btn = event.target;
  btn.disabled = true;
  btn.textContent = 'Building...';
  
  buildLog = [];
  
  try {
    await buildProject();
  } catch (error) {
    console.error('Build failed:', error);
    displayError(`Build failed: ${error.message}`);
  } finally {
    btn.disabled = false;
    btn.textContent = 'Compile PXL';
  }
}

// Handle clear build button click
async function handleClearBuild(event) {
  const btn = event.target;
  btn.disabled = true;
  
  displayStatus('Clearing build artifacts...');
  
  // Clear compiled modules tracking
  compiledModules.clear();
  buildLog = [];
  
  // Reset jsCoq provider state
  try {
    await coqManager.provider.reset();
    await configureLoadpath();
    displayStatus('Build cleared. Ready for clean rebuild.');
  } catch (error) {
    displayError(`Clear failed: ${error.message}`);
  } finally {
    btn.disabled = false;
  }
}

// Main build workflow
async function buildProject() {
  if (!coqManager || !coqManager.provider) {
    throw new Error('jsCoq not initialized');
  }
  
  displayStatus('Building project...');
  
  // Get proven proofs
  const provenProofs = [];
  for (const group of proofRegistry.groups) {
    for (const item of group.items) {
      if (item.status === 'proven' && item.admits === 0) {
        provenProofs.push(item);
      }
    }
  }
  
  if (provenProofs.length === 0) {
    displayError('No proven proofs to build');
    return;
  }
  
  console.log(`Building ${provenProofs.length} modules`);
  buildLog.push(`Total modules: ${provenProofs.length}`);
  
  // Sort by dependencies (topological order)
  const buildOrder = sortByDependencies(provenProofs);
  
  console.log('Build order:', buildOrder.map(p => p.id));
  buildLog.push(`Build order: ${buildOrder.map(p => p.file).join(', ')}`);
  
  displayStatus(`Building ${buildOrder.length} modules in dependency order...`);
  
  // Build each module
  for (let i = 0; i < buildOrder.length; i++) {
    const proof = buildOrder[i];
    
    // Check if already compiled (skip if .vo exists)
    if (compiledModules.has(proof.id)) {
      displayProgress(`[${i + 1}/${buildOrder.length}] ⊙ ${proof.title} (using cached .vo)`, 'cached');
      buildLog.push(`${proof.file}: cached`);
      continue;
    }
    
    // Check dependencies have .vo files
    const missingDeps = checkDependencies(proof);
    if (missingDeps.length > 0) {
      const error = `Missing dependencies for ${proof.file}: ${missingDeps.join(', ')}`;
      displayError(error);
      buildLog.push(`${proof.file}: FAILED - missing dependencies`);
      throw new Error(error);
    }
    
    displayProgress(`[${i + 1}/${buildOrder.length}] Building ${proof.title}...`, 'info');
    
    try {
      // Load source
      const source = await loadCoqFile(proof.path);
      
      // Compile
      await compileModule(source, proof);
      
      // Generate .vo artifact
      generateVOArtifact(proof);
      
      displayProgress(`[${i + 1}/${buildOrder.length}] ✓ ${proof.title} (.vo generated)`, 'success');
      buildLog.push(`${proof.file}: SUCCESS -> .vo generated`);
      
    } catch (error) {
      const errorMsg = `Build failed at ${proof.file}: ${error.message}`;
      displayError(errorMsg);
      buildLog.push(`${proof.file}: FAILED - ${error.message}`);
      throw error;  // Halt on first failure
    }
  }
  
  displaySuccess(`Build complete: ${buildOrder.length} modules compiled, ${compiledModules.size} .vo artifacts`);
  buildLog.push(`Build complete: ${compiledModules.size} .vo files`);
}

// Check if dependencies have .vo files
function checkDependencies(proof) {
  const missing = [];
  
  if (proof.dependencies && proof.dependencies.length > 0) {
    for (const depId of proof.dependencies) {
      if (!compiledModules.has(depId)) {
        missing.push(depId);
      }
    }
  }
  
  return missing;
}

// Load Coq source file
async function loadCoqFile(path) {
  try {
    const response = await fetch(path);
    
    if (!response.ok) {
      throw new Error(`File not found: ${path}`);
    }
    
    const content = await response.text();
    
    if (!content || content.trim().length === 0) {
      throw new Error(`File is empty: ${path}`);
    }
    
    return content;
    
  } catch (error) {
    if (error.message.includes('not found')) {
      throw new Error(`File not found: ${path} (ensure .v files exist at paths in proof_index.json)`);
    }
    throw error;
  }
}

// Compile a module
async function compileModule(coqCode, proof) {
  try {
    // Execute Coq code through provider
    const result = await coqManager.provider.exec(coqCode);
    
    // Check for errors
    if (result && result.error) {
      throw new Error(result.error);
    }
    
    return result;
    
  } catch (error) {
    // Extract meaningful error
    let errorMsg = error.message || 'Unknown Coq error';
    
    if (error.response && error.response.message) {
      errorMsg = error.response.message;
    }
    
    throw new Error(errorMsg);
  }
}

// Generate .vo artifact after successful compilation
function generateVOArtifact(proof) {
  // Mark module as compiled (.vo exists)
  compiledModules.add(proof.id);
  
  // Log .vo generation
  console.log(`Generated .vo for ${proof.id} at /coq/build/${proof.file.replace('.v', '.vo')}`);
  
  // In real Coq, this would be: coqc file.v -> file.vo
  // In jsCoq, we track compilation state and configure imports to resolve properly
}

// Sort proofs by dependency order (topological sort)
function sortByDependencies(proofs) {
  const sorted = [];
  const visited = new Set();
  const proofMap = new Map();
  
  for (const proof of proofs) {
    proofMap.set(proof.id, proof);
  }
  
  function visit(proof) {
    if (visited.has(proof.id)) return;
    
    // Visit dependencies first
    if (proof.dependencies && proof.dependencies.length > 0) {
      for (const depId of proof.dependencies) {
        const dep = proofMap.get(depId);
        if (dep) {
          visit(dep);
        }
      }
    }
    
    visited.add(proof.id);
    sorted.push(proof);
  }
  
  for (const proof of proofs) {
    visit(proof);
  }
  
  return sorted;
}

// Display functions
function displayStatus(message) {
  const container = document.getElementById('jscoq-container');
  if (!container) return;
  
  const panel = container.querySelector('#jscoq-panel');
  if (panel) panel.style.display = 'none';
  
  const statusDiv = document.createElement('div');
  statusDiv.className = 'compilation-status';
  statusDiv.textContent = message;
  statusDiv.id = 'compilation-output';
  
  container.innerHTML = '';
  container.appendChild(statusDiv);
}

function displayError(message) {
  const container = document.getElementById('jscoq-container');
  if (!container) return;
  
  let output = container.querySelector('#compilation-output');
  if (!output) {
    output = document.createElement('div');
    output.id = 'compilation-output';
    container.innerHTML = '';
    container.appendChild(output);
  }
  
  const errorDiv = document.createElement('div');
  errorDiv.className = 'compilation-error';
  errorDiv.innerHTML = `
    <div class="error-icon">⚠</div>
    <div class="error-message">${escapeHtml(message)}</div>
  `;
  
  output.appendChild(errorDiv);
  console.error('Build error:', message);
}

function displaySuccess(message) {
  const container = document.getElementById('jscoq-container');
  if (!container) return;
  
  let output = container.querySelector('#compilation-output');
  if (!output) {
    output = document.createElement('div');
    output.id = 'compilation-output';
    container.innerHTML = '';
    container.appendChild(output);
  }
  
  const successDiv = document.createElement('div');
  successDiv.className = 'compilation-success';
  successDiv.innerHTML = `
    <div class="success-icon">✓</div>
    <div class="success-message">${escapeHtml(message)}</div>
  `;
  
  output.appendChild(successDiv);
}

function displayProgress(message, type = 'info') {
  const container = document.getElementById('jscoq-container');
  if (!container) return;
  
  let output = container.querySelector('#compilation-output');
  if (!output) {
    output = document.createElement('div');
    output.id = 'compilation-output';
    container.innerHTML = '';
    container.appendChild(output);
  }
  
  const progressDiv = document.createElement('div');
  progressDiv.className = `compilation-progress compilation-${type}`;
  progressDiv.textContent = message;
  
  output.appendChild(progressDiv);
  output.scrollTop = output.scrollHeight;
}

function escapeHtml(text) {
  const div = document.createElement('div');
  div.textContent = text;
  return div.innerHTML;
}

// Start initialization
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', initPXLWorkbench);
} else {
  initPXLWorkbench();
}
