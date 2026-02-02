// PXL Workbench - Registry-Driven Interface

let registry = null;
let currentProof = null;
let activeFilters = new Set(['proven', 'partial', 'skeleton', 'frozen', 'empty']);
let viewMode = 'summary'; // 'summary' or 'source'

// DOM Elements
const proofTree = document.getElementById('proof-tree');
const contentView = document.getElementById('content-view');
const currentFileName = document.getElementById('current-file-name');
const currentFileStatus = document.getElementById('current-file-status');
const compileStatusText = document.getElementById('compile-status-text');
const fileCountBadge = document.getElementById('file-count');
const axiomCountBadge = document.getElementById('axiom-count');
const admitCountBadge = document.getElementById('admit-count');
const lastVerifiedSpan = document.getElementById('last-verified');
const versionBadge = document.getElementById('version-badge');
const viewSourceBtn = document.getElementById('view-source-btn');
const viewSummaryBtn = document.getElementById('view-summary-btn');
const compileBtn = document.getElementById('compile-btn');

// Initialize
document.addEventListener('DOMContentLoaded', async () => {
  await loadRegistry();
  renderNavigation();
  setupEventListeners();
  updateMetadata();
});

// Load Registry
async function loadRegistry() {
  try {
    const response = await fetch('proof_index.json');
    registry = await response.json();
    console.log('Registry loaded:', registry);
  } catch (error) {
    console.error('Failed to load registry:', error);
    proofTree.innerHTML = '<div style="padding: 16px; color: #b55a6a;">Failed to load proof registry</div>';
  }
}

// Render Navigation Tree
function renderNavigation() {
  if (!registry) return;
  
  proofTree.innerHTML = '';
  
  registry.groups.forEach(group => {
    const groupEl = document.createElement('div');
    groupEl.className = 'proof-group';
    
    const headerEl = document.createElement('div');
    headerEl.className = 'proof-group-header';
    headerEl.textContent = `${group.name} (${group.items.length})`;
    headerEl.onclick = () => toggleGroup(groupEl);
    
    const itemsEl = document.createElement('div');
    itemsEl.className = 'proof-items';
    
    group.items.forEach(proof => {
      if (!activeFilters.has(proof.status)) return;
      
      const itemEl = document.createElement('div');
      itemEl.className = 'proof-item';
      itemEl.dataset.proofId = proof.id;
      
      const titleEl = document.createElement('span');
      titleEl.className = 'proof-item-title';
      titleEl.textContent = proof.title;
      
      const badgeEl = document.createElement('span');
      badgeEl.className = `status-badge ${proof.status}`;
      badgeEl.textContent = proof.status;
      
      itemEl.appendChild(titleEl);
      itemEl.appendChild(badgeEl);
      itemEl.onclick = () => selectProof(proof);
      
      itemsEl.appendChild(itemEl);
    });
    
    groupEl.appendChild(headerEl);
    groupEl.appendChild(itemsEl);
    proofTree.appendChild(groupEl);
  });
}

// Toggle Group Expand/Collapse
function toggleGroup(groupEl) {
  const items = groupEl.querySelector('.proof-items');
  items.style.display = items.style.display === 'none' ? 'block' : 'none';
}

// Select Proof
function selectProof(proof) {
  currentProof = proof;
  
  // Update active state in nav
  document.querySelectorAll('.proof-item').forEach(el => {
    el.classList.remove('active');
  });
  document.querySelector(`[data-proof-id="${proof.id}"]`)?.classList.add('active');
  
  // Update header
  currentFileName.textContent = proof.file;
  currentFileStatus.textContent = proof.status;
  currentFileStatus.className = `status-badge ${proof.status}`;
  
  // Render content based on view mode
  if (viewMode === 'summary') {
    renderSummary(proof);
  } else {
    renderSource(proof);
  }
}

// Render Summary View
function renderSummary(proof) {
  contentView.innerHTML = `
    <div class="content-summary">
      <div class="summary-section">
        <h3>File Path</h3>
        <p style="font-family: var(--font-mono); font-size: 11px; color: var(--text-secondary);">${proof.path}</p>
      </div>
      
      <div class="summary-section">
        <h3>Status</h3>
        <p>
          <span class="status-badge ${proof.status}">${proof.status}</span>
          ${proof.admits > 0 ? `<span style="color: var(--status-partial); font-family: var(--font-mono); font-size: 11px; margin-left: 12px;">${proof.admits} admit${proof.admits > 1 ? 's' : ''}</span>` : ''}
        </p>
      </div>
      
      <div class="summary-section">
        <h3>Summary</h3>
        <p>${proof.summary}</p>
      </div>
      
      ${proof.dependencies.length > 0 ? `
        <div class="summary-section">
          <h3>Dependencies</h3>
          <ul class="dependency-list">
            ${proof.dependencies.map(dep => `<li>→ ${dep}</li>`).join('')}
          </ul>
        </div>
      ` : ''}
      
      ${proof.hot_button ? `
        <div class="summary-section" style="background: rgba(201, 168, 76, 0.05); padding: 12px; border-left: 3px solid var(--status-partial); border-radius: 4px;">
          <h3 style="color: var(--status-partial);">⚡ Hot Button Proof</h3>
          <p>This proof contains contested or architecturally critical claims.</p>
        </div>
      ` : ''}
    </div>
  `;
}

// Render Source View
async function renderSource(proof) {
  contentView.innerHTML = '<div style="padding: 16px; color: var(--text-muted);">Loading source...</div>';
  
  try {
    const response = await fetch(`coq/v/${proof.file}`);
    if (!response.ok) throw new Error('File not found');
    
    const source = await response.text();
    contentView.innerHTML = `<pre class="content-source">${escapeHtml(source)}</pre>`;
  } catch (error) {
    contentView.innerHTML = `
      <div style="padding: 16px; color: var(--status-partial);">
        <p>Source file not available in web interface.</p>
        <p style="font-family: var(--font-mono); font-size: 11px; margin-top: 8px; color: var(--text-muted);">Path: ${proof.path}</p>
        <p style="font-size: 12px; margin-top: 12px; color: var(--text-secondary);">
          .v files must be placed in <code style="background: rgba(255,255,255,0.05); padding: 2px 6px; border-radius: 2px;">coq/v/</code> directory for source viewing.
        </p>
      </div>
    `;
  }
}

// Setup Event Listeners
function setupEventListeners() {
  // Filter buttons
  document.querySelectorAll('.filter-btn').forEach(btn => {
    btn.addEventListener('click', () => {
      const status = btn.dataset.status;
      if (activeFilters.has(status)) {
        activeFilters.delete(status);
        btn.classList.remove('active');
      } else {
        activeFilters.add(status);
        btn.classList.add('active');
      }
      renderNavigation();
    });
  });
  
  // View mode buttons
  viewSourceBtn.addEventListener('click', () => {
    viewMode = 'source';
    viewSourceBtn.classList.add('active');
    viewSummaryBtn.classList.remove('active');
    if (currentProof) renderSource(currentProof);
  });
  
  viewSummaryBtn.addEventListener('click', () => {
    viewMode = 'summary';
    viewSummaryBtn.classList.add('active');
    viewSourceBtn.classList.remove('active');
    if (currentProof) renderSummary(currentProof);
  });
  
  // Compile button
  compileBtn.addEventListener('click', () => {
    compileStatusText.textContent = 'jsCoq integration pending';
    console.log('Compile requested - jsCoq integration not yet implemented');
  });
}

// Update Metadata
function updateMetadata() {
  if (!registry) return;
  
  const totalFiles = registry.groups.reduce((sum, g) => sum + g.items.length, 0);
  const totalAdmits = registry.groups.reduce((sum, g) => 
    sum + g.items.reduce((itemSum, item) => itemSum + (item.admits || 0), 0), 0
  );
  
  fileCountBadge.textContent = `${totalFiles} files`;
  axiomCountBadge.textContent = `${registry.axiom_count} axioms`;
  admitCountBadge.textContent = `${totalAdmits} admits`;
  lastVerifiedSpan.textContent = registry.last_verified;
  versionBadge.textContent = registry.version;
}

// Utility
function escapeHtml(text) {
  const div = document.createElement('div');
  div.textContent = text;
  return div.innerHTML;
}
