// Conceptual Panel Integration
// Adds normalized TXT content display to PXL workbench

const conceptualPanelHTML = `
  <div id="conceptual-panel" class="conceptual-panel" style="display: none;">
    <div class="panel-header">
      <h2>Conceptual Notes</h2>
      <button id="close-conceptual-btn" class="close-btn">✕</button>
    </div>
    <div id="conceptual-content" class="conceptual-content"></div>
  </div>
`;

const conceptualToggleHTML = `
  <button id="toggle-conceptual-btn" class="toggle-conceptual-btn">
    <span class="icon">📖</span>
    <span class="label">Show Conceptual Notes</span>
  </button>
`;

// Initialize Conceptual Panel
function initConceptualPanel() {
  // Add panel to DOM
  const mainPanel = document.getElementById('main-panel');
  if (!mainPanel) return;
  
  // Insert panel after main panel
  mainPanel.insertAdjacentHTML('afterend', conceptualPanelHTML);
  
  // Add toggle button to file actions
  const fileActions = document.querySelector('.file-actions');
  if (fileActions) {
    fileActions.insertAdjacentHTML('beforeend', conceptualToggleHTML);
  }
  
  // Setup event listeners
  const toggleBtn = document.getElementById('toggle-conceptual-btn');
  const closeBtn = document.getElementById('close-conceptual-btn');
  const panel = document.getElementById('conceptual-panel');
  
  if (toggleBtn) {
    toggleBtn.addEventListener('click', () => {
      if (panel.style.display === 'none') {
        showConceptualPanel();
      } else {
        hideConceptualPanel();
      }
    });
  }
  
  if (closeBtn) {
    closeBtn.addEventListener('click', hideConceptualPanel);
  }
}

// Show Conceptual Panel
async function showConceptualPanel() {
  const panel = document.getElementById('conceptual-panel');
  const toggleBtn = document.getElementById('toggle-conceptual-btn');
  
  if (!panel || !currentProof) return;
  
  panel.style.display = 'flex';
  if (toggleBtn) {
    toggleBtn.querySelector('.label').textContent = 'Hide Conceptual Notes';
  }
  
  // Load conceptual content for current proof
  await loadConceptualContent(currentProof);
}

// Hide Conceptual Panel
function hideConceptualPanel() {
  const panel = document.getElementById('conceptual-panel');
  const toggleBtn = document.getElementById('toggle-conceptual-btn');
  
  if (!panel) return;
  
  panel.style.display = 'none';
  if (toggleBtn) {
    toggleBtn.querySelector('.label').textContent = 'Show Conceptual Notes';
  }
}

// Load Conceptual Content
async function loadConceptualContent(proof) {
  const contentDiv = document.getElementById('conceptual-content');
  if (!contentDiv) return;
  
  contentDiv.innerHTML = '<div class="loading">Loading conceptual notes...</div>';
  
  try {
    // Load all normalization documents
    const normalizationFiles = [
      'docs/pxl_axioms_normalized.json',
      'docs/pxl_theorems_normalized.json',
      'docs/pxl_foundations_normalized.json',
      'docs/pxl_domain_mappings_normalized.json',
      'docs/pxl_paradox_resolutions_normalized.json'
    ];
    
    const documents = await Promise.all(
      normalizationFiles.map(file => 
        fetch(file)
          .then(r => r.json())
          .catch(err => {
            console.warn(`Failed to load ${file}:`, err);
            return null;
          })
      )
    );
    
    // Filter out failed loads and combine all sections
    const allSections = documents
      .filter(doc => doc && doc.sections)
      .flatMap(doc => doc.sections.map(section => ({
        ...section,
        doc_id: doc.doc_id,
        source: doc.source
      })));
    
    // Find sections that map to current proof
    const mappedSections = allSections.filter(section => 
      section.maps_to && section.maps_to.includes(proof.id)
    );
    
    if (mappedSections.length === 0) {
      contentDiv.innerHTML = renderNoMapping();
      return;
    }
    
    // Render mapped sections
    contentDiv.innerHTML = mappedSections.map(section => renderSection(section, proof)).join('');
    
  } catch (error) {
    console.error('Failed to load conceptual content:', error);
    contentDiv.innerHTML = renderError();
  }
}

// Render Section
function renderSection(section, proof) {
  const authorityBadge = renderAuthorityBadge(section.authority, proof.id);
  const statusBadge = renderStatusBadge(section.status);
  
  return `
    <div class="conceptual-section" data-authority="${section.authority}">
      <div class="section-header">
        <h3>${section.title}</h3>
        <div class="badges">
          ${authorityBadge}
          ${statusBadge}
        </div>
      </div>
      
      ${section.txt_claim ? `
        <div class="claim-box">
          <div class="claim-label">TXT Claim</div>
          <div class="claim-text">${escapeHtml(section.txt_claim)}</div>
        </div>
      ` : ''}
      
      ${section.coq_definition ? `
        <div class="definition-box">
          <div class="definition-label">Coq Definition</div>
          <pre class="definition-text">${escapeHtml(section.coq_definition)}</pre>
        </div>
      ` : ''}
      
      ${section.notes ? `
        <div class="notes-box">
          <div class="notes-label">Notes</div>
          <div class="notes-text">${escapeHtml(section.notes)}</div>
        </div>
      ` : ''}
      
      <div class="section-footer">
        <span class="source-ref">Source: ${section.source}</span>
        <span class="match-quality">Match: ${section.match_quality}</span>
      </div>
    </div>
  `;
}

// Render Authority Badge
function renderAuthorityBadge(authority, proofId) {
  const badges = {
    formal: {
      label: `✓ Proven in ${proofId}`,
      class: 'badge-formal',
      color: '#4a9e6e'
    },
    explanatory_only: {
      label: 'ℹ Explanatory Only',
      class: 'badge-explanatory',
      color: '#8a8880'
    },
    deprecated: {
      label: '⚠ Deprecated',
      class: 'badge-deprecated',
      color: '#b55a6a'
    },
    to_formalize: {
      label: '⧖ Future Work',
      class: 'badge-future',
      color: '#c9a84c'
    }
  };
  
  const badge = badges[authority] || badges.explanatory_only;
  
  return `<span class="authority-badge ${badge.class}" style="color: ${badge.color};">${badge.label}</span>`;
}

// Render Status Badge
function renderStatusBadge(status) {
  const statusMap = {
    covered: { label: 'Covered', color: '#4a9e6e' },
    eliminated: { label: 'Eliminated', color: '#5ba8b5' },
    partial: { label: 'Partial', color: '#c9a84c' },
    unsupported: { label: 'Unsupported', color: '#b55a6a' },
    'non-formal': { label: 'Non-formal', color: '#8a8880' }
  };
  
  const s = statusMap[status] || statusMap['non-formal'];
  
  return `<span class="status-badge-small" style="color: ${s.color};">${s.label}</span>`;
}

// Render No Mapping
function renderNoMapping() {
  return `
    <div class="empty-state">
      <div class="empty-icon">ℹ</div>
      <h3>No Conceptual Notes</h3>
      <p>This proof has no associated conceptual documentation in the TXT files.</p>
      <p class="note">The formal proof in the .v file is the complete specification.</p>
    </div>
  `;
}

// Render Error
function renderError() {
  return `
    <div class="error-state">
      <div class="error-icon">⚠</div>
      <h3>Failed to Load</h3>
      <p>Could not load TXT normalization schema.</p>
      <p class="note">Ensure <code>docs/txt_normalization_schema.json</code> is present.</p>
    </div>
  `;
}

// Add CSS for Conceptual Panel
function addConceptualPanelStyles() {
  const style = document.createElement('style');
  style.textContent = `
    .conceptual-panel {
      width: 400px;
      background: var(--bg-panel);
      border-left: 1px solid var(--border);
      display: flex;
      flex-direction: column;
      flex-shrink: 0;
    }
    
    .conceptual-content {
      flex: 1;
      overflow-y: auto;
      padding: 16px;
    }
    
    .conceptual-section {
      background: var(--bg-main);
      border: 1px solid var(--border);
      border-radius: 6px;
      padding: 16px;
      margin-bottom: 16px;
    }
    
    .conceptual-section[data-authority="deprecated"] {
      display: none;
    }
    
    .section-header {
      display: flex;
      justify-content: space-between;
      align-items: flex-start;
      margin-bottom: 12px;
    }
    
    .section-header h3 {
      font-size: 14px;
      font-weight: 500;
      color: var(--text-primary);
      margin: 0;
      flex: 1;
    }
    
    .badges {
      display: flex;
      gap: 6px;
      flex-wrap: wrap;
    }
    
    .authority-badge, .status-badge-small {
      font-family: var(--font-mono);
      font-size: 9px;
      text-transform: uppercase;
      letter-spacing: 0.5px;
      padding: 3px 7px;
      border-radius: 3px;
      background: rgba(255, 255, 255, 0.05);
      border: 1px solid currentColor;
      white-space: nowrap;
    }
    
    .claim-box, .definition-box, .notes-box {
      margin: 12px 0;
      padding: 10px 12px;
      border-radius: 4px;
    }
    
    .claim-box {
      background: rgba(91, 168, 181, 0.08);
      border-left: 3px solid var(--status-frozen);
    }
    
    .definition-box {
      background: rgba(74, 158, 110, 0.08);
      border-left: 3px solid var(--status-proven);
    }
    
    .notes-box {
      background: rgba(138, 136, 128, 0.08);
      border-left: 3px solid var(--text-secondary);
    }
    
    .claim-label, .definition-label, .notes-label {
      font-family: var(--font-mono);
      font-size: 9px;
      text-transform: uppercase;
      letter-spacing: 1px;
      color: var(--text-muted);
      margin-bottom: 6px;
    }
    
    .claim-text, .notes-text {
      font-size: 12px;
      line-height: 1.6;
      color: var(--text-primary);
    }
    
    .definition-text {
      font-family: var(--font-mono);
      font-size: 11px;
      line-height: 1.5;
      color: var(--text-primary);
      white-space: pre-wrap;
      margin: 0;
    }
    
    .section-footer {
      display: flex;
      justify-content: space-between;
      margin-top: 12px;
      padding-top: 12px;
      border-top: 1px solid var(--border);
      font-family: var(--font-mono);
      font-size: 9px;
      color: var(--text-muted);
    }
    
    .toggle-conceptual-btn {
      display: flex;
      align-items: center;
      gap: 5px;
      padding: 5px 10px;
      font-size: 10px;
      font-family: var(--font-mono);
      text-transform: uppercase;
      background: transparent;
      border: 1px solid var(--border);
      color: var(--text-secondary);
      cursor: pointer;
      border-radius: 3px;
    }
    
    .toggle-conceptual-btn:hover {
      background: var(--status-frozen-bg);
      border-color: var(--status-frozen);
      color: var(--status-frozen);
    }
    
    .toggle-conceptual-btn .icon {
      font-size: 12px;
    }
    
    .close-btn {
      background: transparent;
      border: none;
      color: var(--text-muted);
      font-size: 16px;
      cursor: pointer;
      padding: 4px 8px;
      margin: -4px -8px -4px 0;
    }
    
    .close-btn:hover {
      color: var(--text-primary);
    }
    
    .empty-state, .error-state {
      display: flex;
      flex-direction: column;
      align-items: center;
      justify-content: center;
      padding: 40px 20px;
      text-align: center;
      color: var(--text-secondary);
    }
    
    .empty-icon, .error-icon {
      font-size: 32px;
      margin-bottom: 12px;
    }
    
    .empty-state h3, .error-state h3 {
      font-size: 14px;
      margin-bottom: 8px;
      color: var(--text-primary);
    }
    
    .empty-state p, .error-state p {
      font-size: 12px;
      line-height: 1.6;
      margin-bottom: 6px;
    }
    
    .empty-state .note, .error-state .note {
      font-size: 11px;
      color: var(--text-muted);
      margin-top: 8px;
    }
    
    .loading {
      display: flex;
      align-items: center;
      justify-content: center;
      padding: 40px;
      color: var(--text-muted);
      font-size: 12px;
    }
  `;
  document.head.appendChild(style);
}

// Initialize on DOM load
document.addEventListener('DOMContentLoaded', () => {
  addConceptualPanelStyles();
  initConceptualPanel();
});

// Export for app.js
window.ConceptualPanel = {
  show: showConceptualPanel,
  hide: hideConceptualPanel,
  load: loadConceptualContent
};
