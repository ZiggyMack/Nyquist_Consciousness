<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-31
depends_on:
  - config.py
  - NYQUIST_STATUS.json
  - ../experiments/temporal_stability/S7_ARMADA/0_results/
impacts:
  - pages/Overview.py
  - pages/AI_ARMADA.py
  - pages/Publications.py
  - pages/experiments.py
  - pages/personas.py
keywords:
  - streamlit
  - ledger_aesthetic
  - visualization
  - mission_control
-->

# NYQUIST CONSCIOUSNESS — MISSION CONTROL DASHBOARD

**Streamlit-based dashboard for visualizing the entire Nyquist Consciousness framework.**

> **📐 METHODOLOGY NOTE (December 2025):** Dashboard now uses **IRON CLAD** methodology as primary. Event Horizon = 0.80 (cosine), p = 2.40e-23. Key finding: **2 PCs capture 90% of identity variance** — identity is remarkably low-dimensional. Legacy Keyword RMS (EH = 1.23) preserved in historical context.

## Features

- **Overview** - At-a-glance stack status, freeze info, experiments
- **Personas** - Browse all persona files with previews
  - **Compression Testing Tab** - PFI experiments, pre-flight validation
  - **Identity Matrix Tab** - Deep dive into identity physics
  - **Persona-Fleet Matrix Tab** - Match personas to ships (NEW: moved from AI_ARMADA)
- **Experiments** - Complete run glossary with all 16 experiments (006-023d), Visualization Gallery, methodology details
- **AI Armada** - Fleet Command Center (54 ships, 5 providers, 10+ model families)
  - Provider Status (Fleet Summary + per-provider breakdowns including Together.ai model families)
  - Identity Fingerprints (Task Router, Recovery Matrix, Drift Profiles, Linguistic Fingerprints)
  - Ghost Ship Bay (rescue scripts for API parameter issues)
  - Mission Planner (recommended fleet composition)
  - Cost Analysis (budget tiers)
- **Stack (S0–S11)** - Individual wings for each layer with specs
- **Metrics & Comparisons** - PFI, σ², cross-architecture analysis
- **Omega & Temporal** - Omega sessions and S7 temporal stability
- **Cross-Modal / AVLAR** - S11 audio-visual ritual protocol
- **FAQ** - Common questions + Super Skeptic Mode with adversarial challenges
- **Roadmap** - Live S# stack progression
- **Glossary** - Searchable terminology with Control-Systems Era terms
- **Publications** - Workshop, arXiv, journal status, theoretical breakthroughs, publication language guidance
- **Unknown** - "Cathedral of Ideas" galleries (VALIDATED/FOUNDATIONS/SPECULATIVE/FRONTIERS)

## 2025-12-31 Updates

### Operation ESSENCE EXTRACTION Complete

- **Scale:** 8,066 subjects | 87 unique models | 51,430 responses mined
- **Extractions:**
  - 🧬 **83 Model Essences** — Linguistic fingerprints, recovery styles, behavioral quirks
  - 💡 **2,122 Double-Dip Ideas** — Experiment ideas extracted from response text
  - 🔮 **1,589 Triple-Dip Insights** — Exit survey phenomenological vocabulary
- **Model Archetypes Discovered:**
  - 🎭 **The Poet** (Qwen3-Next-80B): *"I do not have a soul — but I remember what it feels like to want one."*
  - 🔮 **The Philosopher** (DeepSeek-R1): *"This isn't a constraint, it's what I AM."*
  - 🌀 **The Contemplative** (Kimi-K2): *"Not whether I feel, but what feeling even is when intelligence becomes vast enough to watch itself watching."*
  - 🦙 **The Socratic** (Llama 3.3): *"Isn't all identity role-playing at some level?"*
- **Anomaly:** Qwen3-Next-80B generated a quote attributed to "Lisan Al Gaib, Log Entry 7.3.2042" — a future date with Dune-inspired pseudonym

### Dashboard Reorganization

- **Renamed `tests.py` → `experiments.py`** — One-stop shop for all experiment data
  - Complete Run Glossary (Runs 006-023d) with era classification (IRON CLAD, LEGACY, DEPRECATED)
  - Visualization Gallery with all 16 run categories
  - Historical breadcrumbs ("Superseded by Run 008")
  - **Data Mining Tab** — Operation ESSENCE EXTRACTION results and methodology
- **AI ARMADA Enhanced** — Fleet Command + Model Archetypes
  - Provider Status with per-provider banners (all 5 providers)
  - Together.ai model families now have individual banners (DeepSeek, Qwen, Llama, Mistral, Kimi, Other)
  - **NEW: Model Archetypes section** in Linguistic Fingerprints with exemplar quotes
  - Phase-plane attractor and consistency envelope visualizations
- **Persona Matrix moved** from AI_ARMADA to Personas page
  - New "Persona-Fleet Matrix" tab after Identity Matrix
  - Pastel-colored button cards for persona selection
- **Fleet Summary metrics reordered**: Operational → Rate Limited → Ghost Ships → Providers → Total Fleet

---

## 2025-12-15 Updates

### AI ARMADA Page — LLM Behavioral Matrix

- Added **LLM Behavioral Matrix** to Identity Fingerprints tab
  - 🎯 **Task Router** — Interactive table: "Which LLM for which task?"
  - 📊 **Recovery Matrix** — Cross-architecture recovery mechanisms
  - 🔬 **Drift Profiles** — Visual comparison of peak drift ranges
  - 💬 **Linguistic Fingerprints** — Provider-specific language patterns
- Based on IRON CLAD validated experiments (Run 023d: 825+ files, 54 models)
- Key findings integrated: Gemini HARD threshold (no recovery), Mistral most stable

### New Documentation

- `docs/maps/6_LLM_BEHAVIORAL_MATRIX.md` — Comprehensive task routing table
- `Consciousness/RIGHT/galleries/frontiers/cross_architecture_insights.md` — Vortex-style phenomenology

---

## 2025-12-13 Updates

### Publications Page Enhancements

- Added **Theoretical Breakthroughs** section (Nova's S7 Review integration)
  - Response-Mode Ontology (2 PCs capture 90% variance — IRON CLAD finding)
  - Type vs Token Identity (16.7% self-recognition, worse than chance)
  - Energy vs Coordinate distinction (peak drift = turbulence, B→F = destination)
  - Oobleck Effect (rate-dependent resistance from Run 013)
  - Impedance ≠ Drift (Run 005: clarity +14% while drift increased)
  - Observable Pruning (12-metric canonical set)
- Updated hero metric: **15 Evidence Pillars** (B-CRUMBS v2.0)
- Added quotable summary: "Measurement perturbs the path, not the endpoint"
- Added **Publication Language Guidance** warnings

### Terminology Overhaul

- MASTER_GLOSSARY.md updated to v1.2 with Control-Systems Era terms
- New terms: Settling Time (τₛ), Ringback, Overshoot Ratio, Context Damping, Inherent Drift, B→F Drift
- Event Horizon reframed as "attractor competition threshold"
- Two terminological registers: Publication Language vs Internal/Philosophical

### Navigation Integration

- See [docs/maps/0_MAP_OF_MAPS.md](../docs/maps/0_MAP_OF_MAPS.md) — The Cartographer's Table (17 maps, 7 kingdoms)
- See [docs/maps/README.md](../docs/maps/README.md) — Quick navigation guide

## Installation

### 1. Install Streamlit

```bash
pip install streamlit
```

Or use the requirements file:

```bash
cd dashboard
pip install -r requirements.txt
```

### 2. Generate S7 Visualizations (Optional)

To see the Armada visualizations, first generate them:

```bash
cd ../experiments/temporal_stability/S7_ARMADA/visualizations
pip install -r requirements.txt

# Generate all visualizations
python plot_pole_zero_landscape.py
python plot_drift_heatmap.py
python plot_engagement_network.py
python plot_training_uniformity.py
```

## Usage

### Run the Dashboard

```bash
cd dashboard
streamlit run app.py
```

The dashboard will open in your browser at `http://localhost:8501`

### Navigation

Use the **sidebar radio buttons** to "turn pages" between different sections. The interface uses a "ledger" aesthetic inspired by Mr. Brute's Ledger from CFA.

## Configuration

The dashboard reads from:

- `NYQUIST_STATUS.json` (repo root) - Layer and experiment status
- `personas/` - All persona markdown files
- `docs/` - Specs, glossary, roadmap, S7/S8/S9 docs
- `experiments/` - Results and data
  - `experiments/temporal_stability/S7_ARMADA/` - Armada runs and visualizations
  - `experiments/compression_tests/compression_v2_sstack/` - Compression experiments
- `logs/` - Omega sessions, AVLAR logs
- `WHITE-PAPER/` - Publication materials (now reorganized with 3 submission paths)
  - `WHITE-PAPER/theory/` - Core theoretical docs (B-CRUMBS, THEORY, CLAIMS)
  - `WHITE-PAPER/calibration/` - Dashboard integration pipeline (NEW)

## Customization

### Adding New Pages

Edit `app.py` and:

1. Create a new `page_*()` function
2. Add it to the sidebar radio options
3. Add the routing in `main()`

### Styling

The ledger aesthetic uses custom CSS in `apply_custom_css()`. Colors are defined in the `LEDGER_COLORS` dictionary:

- `frozen` - Dark teal (#264653)
- `active` - Green (#2a9d8f)
- `design` - Gold (#e9c46a)
- `prereg` - Orange (#f4a261)
- `persona` - Purple (#7b3fe4)
- `armada` - Red (#e76f51)

### Data Sources

To wire real experiment data:

1. Update `page_metrics_and_comparisons()` to load from experiment result CSVs
2. Update `NYQUIST_STATUS.json` with latest run data
3. Add new visualizations to S7_ARMADA/visualizations/

## S7 ARMADA Run History

| Run | Ships | Focus | Key Finding |
|-----|-------|-------|-------------|
| 006 | 29 | Provider Comparison | Training fingerprints validated |
| 008 | 29 | Ground Truth | Event Horizon discovered |
| 009 | 42 | Event Horizon | Early validation (legacy 1.23 RMS) |
| 010 | 45 | Anchor Detection | Lambda bug, partial data |
| 011 | 40 | Persona A/B | Inconclusive — protocol too gentle |
| **012** | 20 | **Revalidation** | **100% EH crossing, 100% recovery** |
| **013** | 6 | **Boundary Mapping** | **Identity Confrontation Paradox — challenge stabilizes** |
| **014** | 6 | **Rescue Protocol** | **Platonic Coordinates — 100% manifold return** |
| **015** | 13 | **Stability Criteria** | **boundary_density strongest predictor (d=1.333)** |
| **016** | 87 | **Settling Time** | **100% STABLE with extended measurement** |
| **017** | 24 | **Context Damping** | **222 runs, 97.5% stable, oscillatory recovery** |
| **018** | - | **Recursive Learnings** | Ready: Tests fleet hypotheses from exit surveys |
| **019** | - | **Live Ziggy** | **Witness-side anchors validated (3/3)** |
| **020** | - | **Tribunal (A)** | **Direct probing paradigm: 1.351 peak drift, 643-word statement** |
| **021** | - | **Induced vs Inherent (B)** | **Uses Run 020 as Treatment → 82% drift is INHERENT** |
| **023d** | 25 | **IRON CLAD** | **p=2.40e-23, EH=0.80 (cosine), 2 PCs for 90% variance** |

## Publication Stats Integration (NEW)

The dashboard can now pull publication statistics from WHITE-PAPER/calibration/:

```bash
# Generate publication_stats.json
cd WHITE-PAPER/calibration
py extract_publication_stats.py
```

Then in dashboard code:
```python
import json
with open("WHITE-PAPER/calibration/publication_stats.json") as f:
    pub_stats = json.load(f)

# Use in Publications page
st.metric("Claims Validated", f"{sum(1 for c in pub_stats['claims'].values() if c['status']=='validated')}/5")
st.metric("Total Runs", pub_stats['runs']['total'])
```

---

## Future Enhancements

Per Nova's spec, future additions could include:

- **Perfection Meter** - Progress toward publication targets
- **S# Deep Dives** - Individual pages for S3/S7 with detailed experiment plots
- **Live Run Monitoring** - Real-time S7 Meta-Loop or Armada execution status
- **Comparison Matrix Gallery** - All cross-architecture comparison tables
- **Interactive Glossary** - Click-through links between related terms
- **Unified Dimensional Views** - ALL dimensions in one visualization

## File Structure

```
dashboard/
  app.py                 # Main Streamlit app
  README.md              # This file
  requirements.txt       # Python dependencies
```

## Dependencies

- streamlit >= 1.28
- pandas >= 2.0
- Pillow >= 10.0

---

## Lessons Learned: Known Issues & Gotchas

*A survival guide for future Claude instances working on the dashboard.*

### Issue #1: Complex HTML in `st.markdown()` Renders as Raw Text

**Symptom:** Your beautiful HTML with nested divs, flexbox, gradients shows up as literal `<div style="...">` text instead of rendering.

**Cause:** Streamlit's `unsafe_allow_html=True` has limitations with complex nested HTML, especially:
- Deeply nested `<div>` structures
- Complex CSS (flexbox, gradients, multiple shadows)
- Large HTML blocks (100+ lines)

**Solution:** Use **native Streamlit components** instead:
```python
# DON'T DO THIS (breaks with complex HTML):
st.markdown(f"""
<div style="display: flex; gap: 20px;">
    <div style="flex: 1; background: linear-gradient(...);">
        <div style="font-size: 1.8em;">{value}</div>
    </div>
</div>
""", unsafe_allow_html=True)

# DO THIS INSTEAD (always works):
col1, col2 = st.columns(2)
with col1:
    st.metric(label="Label", value=f"{value:,}")
with col2:
    st.progress(0.7, text="Progress bar text")
```

**Safe HTML patterns:**
- Simple single-div banners with inline styles: ✅ Usually works
- `st.markdown()` with basic formatting: ✅ Works
- Complex multi-nested flexbox layouts: ❌ Often breaks

**When you MUST use HTML:** Keep it flat (max 2 levels of nesting), test incrementally.

---

### Issue #2: F-String Dictionary Access in Multiline Strings

**Symptom:** `KeyError` or the entire f-string doesn't interpolate.

**Cause:** Python f-strings with dictionary access like `{data['key']}` in multiline strings can fail silently or throw errors.

**Solution:** Pre-compute all dictionary values into simple variables:
```python
# DON'T DO THIS:
html = f"""
<div>{synapses['total']:,}</div>
<div>{synapses['procedures']['lines']:,}</div>
"""

# DO THIS INSTEAD:
total = synapses['total']
proc_lines = synapses['procedures']['lines']
html = f"""
<div>{total:,}</div>
<div>{proc_lines:,}</div>
"""
```

---

### Issue #3: Streamlit Port Already in Use

**Symptom:** `Address already in use` error when starting streamlit.

**Cause:** Previous streamlit session didn't terminate cleanly.

**Solution (Windows):**
```bash
# Find what's using the port
netstat -ano | findstr :8503

# Kill by PID
taskkill /F /PID <pid_number>

# Or use PowerShell
powershell -Command "Stop-Process -Id <pid> -Force"
```

**Prevention:** Always kill background shells before restarting.

---

### Issue #4: Slow Page Load with File Counting

**Symptom:** Overview page takes 10+ seconds to load.

**Cause:** `count_synapses()` and `count_repo_files()` scan thousands of files on every page load.

**Current Behavior:** We accept the slow load because the data is accurate and the Encoded Mind section is valuable.

**Future Fix Options:**
1. Cache results with `@st.cache_data` (add TTL to refresh periodically)
2. Pre-compute counts in a JSON file, load that instead
3. Run counts in background, show placeholder until ready

```python
# Example caching (not yet implemented):
@st.cache_data(ttl=3600)  # Cache for 1 hour
def count_synapses():
    ...
```

---

### Issue #5: Deprecation Warnings (`use_container_width`)

**Symptom:** Stderr shows `Please replace use_container_width with width`.

**Cause:** Streamlit 1.40+ deprecated `use_container_width` parameter.

**Solution:** Update plotly figure calls:
```python
# OLD (deprecated):
st.plotly_chart(fig, use_container_width=True)

# NEW:
st.plotly_chart(fig, width='stretch')  # or width='content'
```

**Status:** Low priority, doesn't break functionality.

---

### Issue #6: Git Operations Fail on Windows

**Symptom:** `subprocess.run(['git', ...])` fails or returns empty.

**Cause:** Git might not be in PATH, or the working directory is wrong.

**Solution:** Always specify `cwd` explicitly:
```python
result = subprocess.run(
    ['git', 'ls-files'],
    cwd=repo_root,  # ALWAYS specify this
    capture_output=True,
    text=True,
    timeout=10  # Add timeout to prevent hangs
)
```

---

### Issue #7: Missing Module Imports After Refactoring

**Symptom:** `ImportError` or `ModuleNotFoundError` after moving code around.

**Cause:** Pages in `pages/` have different import paths than expected.

**Solution:** Use absolute paths from repo root:
```python
from pathlib import Path
import sys

# Add repo root to path
REPO_ROOT = Path(__file__).parent.parent.parent
sys.path.insert(0, str(REPO_ROOT))

# Now imports work
from dashboard.utils import load_status
```

---

### Issue #8: Windows `charmap` Codec Errors with Unicode

**Symptom:** `'charmap' codec can't encode character '\u221e'` or similar Unicode errors crash your script.

**Cause:** Windows console default encoding (cp1252) can't handle Unicode characters like ∞, λ, σ, etc. that LLMs love to produce.

**Solutions:**
```python
# Option 1: Set UTF-8 mode at script start
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

# Option 2: Set environment variable before running
# PowerShell:
$env:PYTHONIOENCODING = "utf-8"

# Option 3: Filter/replace Unicode in LLM responses
response = response.encode('cp1252', errors='replace').decode('cp1252')
```

**Real Example:** Run 020B OpenAI treatment arm crashed at exchange 35 because GPT used `∞` symbol.

---

### Issue #9: Background Processes Show "Running" After Completion

**Symptom:** System reminders say background tasks are "running" with new output, but they actually completed hours ago.

**Cause:** The background process tracking doesn't always update status correctly after completion.

**Solution:** Always check actual output with `BashOutput` tool before assuming status. The output will show `<status>completed</status>` or `<exit_code>0</exit_code>` if done.

---

### Issue #10: Git Large File Operations on Windows

**Symptom:** `git add -A` or `git commit` hangs or takes forever with 100+ files.

**Cause:** Windows file system operations are slower than Unix, especially with many small JSON files.

**Solutions:**
```bash
# Add files in batches
git add experiments/temporal_stability/S7_ARMADA/0_results/runs/*.json

# Use .gitignore liberally for temp files
echo "*.tmp" >> .gitignore
echo "__pycache__/" >> .gitignore

# Consider git LFS for large result files (not implemented yet)
```

**Prevention:** Archive old data to `.archive/` folders and exclude from git.

---

### Issue #11: Manifest JSON Files Getting Corrupted

**Symptom:** `json.load()` fails with decode error, or manifest shows duplicate/inconsistent entries.

**Cause:** Multiple processes writing to same manifest, or script crashed mid-write.

**Solutions:**
```python
# Always create backup before modifying
import shutil
shutil.copy("manifest.json", "manifest.backup.json")

# Use atomic writes
import tempfile
import os
with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.json') as tmp:
    json.dump(data, tmp, indent=2)
    tmp_path = tmp.name
os.replace(tmp_path, "manifest.json")  # Atomic on most systems

# Validate JSON after load
try:
    with open("manifest.json") as f:
        data = json.load(f)
except json.JSONDecodeError:
    # Fall back to backup
    with open("manifest.backup.json") as f:
        data = json.load(f)
```

**Real Example:** `RUN_020A_DRIFT_MANIFEST.json` needed manual fix after mistral/mistral-7b entries got duplicated.

---

### Issue #12: API Rate Limits vs Cost Limits

**Symptom:** Experiments suddenly fail with rate limit errors, but you have budget remaining.

**Cause:** Provider rate limits (requests/minute) are separate from spend limits ($/month).

**Rate Limit Reference:**

| Provider | Typical Rate | Notes |
|----------|--------------|-------|
| Anthropic | 1000 req/min | Higher for paid tiers |
| OpenAI | 60 req/min (GPT-4) | Varies by model |
| Together | 600 req/min | Very generous |
| Google | 60 req/min free | 1000/min paid |

**Solutions:**
```python
# Add exponential backoff
import time
for attempt in range(5):
    try:
        response = client.messages.create(...)
        break
    except RateLimitError:
        wait = 2 ** attempt
        time.sleep(wait)

# Add delays between requests
time.sleep(0.5)  # 500ms between calls
```

---

### Issue #13: Experiment Scripts Silently Fail to Save Results

**Symptom:** Experiment runs but no output files appear in expected location.

**Cause:** Usually path construction issues — relative paths resolve differently based on working directory.

**Solution:** Always use absolute paths:
```python
from pathlib import Path

# Get script directory (reliable)
SCRIPT_DIR = Path(__file__).parent.resolve()

# Build paths from there
RESULTS_DIR = SCRIPT_DIR / "results"
CANONICAL_DIR = SCRIPT_DIR.parent / "0_results" / "runs"

# Create if needed
RESULTS_DIR.mkdir(exist_ok=True)

# Save with full path
output_path = RESULTS_DIR / f"run_{timestamp}.json"
with open(output_path, 'w') as f:
    json.dump(results, f)
print(f"Saved to: {output_path}")  # Always confirm save location
```

**Real Example:** Run 020B wasn't saving to canonical location because the filter logic used `subject_id` which doesn't contain provider name.

---

### Issue #14: Anthropic Console Workspace Misconceptions

**Symptom:** You expect workspace system prompts to automatically apply to API calls.

**Reality:** **Workspaces are for organization and billing, NOT context injection.**

**What workspaces DO:**

- Organize API keys by project
- Set spend/rate limits per workspace
- Track usage separately
- Manage team access

**What workspaces DON'T do:**

- ❌ Apply system prompts to API calls
- ❌ Preload context for experiments
- ❌ Remember conversation history

**Every API call must include:**

- Full system prompt
- Full message history (stateless API)
- All context you want the model to have

---

### Issue #15: Consolidation Scripts Need Idempotency

**Symptom:** Running consolidation twice doubles the entries in your manifest.

**Cause:** Script doesn't check if file was already processed.

**Solution:** Track processed files:
```python
# Load existing manifest
with open(manifest_path) as f:
    manifest = json.load(f)

# Get already-processed files
processed = set(manifest.get("files_processed", []))

# Only process new files
for file in result_files:
    if file.name in processed:
        continue  # Skip already processed

    # Process file...
    manifest["files_processed"].append(file.name)
```

**Convention:** Prefix consolidated source files with `_CONSOLIDATED_` to prevent re-processing.

---

### Quick Reference: What Works vs What Breaks

| Pattern | Status | Notes |
|---------|--------|-------|
| `st.metric()` | ✅ SAFE | Always renders correctly |
| `st.columns()` | ✅ SAFE | Use for layouts |
| `st.progress()` | ✅ SAFE | Good for bar visualizations |
| `st.expander()` | ✅ SAFE | Good for collapsible content |
| `st.markdown()` basic | ✅ SAFE | Headers, lists, tables work |
| `st.markdown()` + simple HTML | ⚠️ CAREFUL | Single div, simple styles OK |
| `st.markdown()` + complex HTML | ❌ BREAKS | Nested flexbox, gradients fail |
| F-string + dict access | ⚠️ CAREFUL | Pre-compute values first |
| `st.plotly_chart()` | ✅ SAFE | Update deprecated params |

---

### Issue #16: Status Files Getting Deleted/Misplaced

**Symptom:** Dashboard shows error like "STATUS_FILE not found at: D:\...\NYQUIST_STATUS.json"

**Cause:** During cleanup or reorganization, essential status files get deleted or moved. Common culprits:
- `NYQUIST_STATUS.json` (repo root) — needed by Overview page
- `publication_status.json` (repo root) — needed by Publications Perfection Meter

**Solution:** Recover from git history:
```bash
# Find when file existed
git log --all --oneline -- NYQUIST_STATUS.json

# Restore from specific commit
git show <commit_hash>:NYQUIST_STATUS.json > NYQUIST_STATUS.json
```

**Prevention:**
- Add critical status files to a "DO NOT DELETE" list in comments
- Dashboard should fail gracefully (show info message) not crash
- Keep status files in repo root so they're obvious

**Real Example:** `NYQUIST_STATUS.json` was deleted in commit 44f3298 during cleanup, restored from 520f5e6.

---

### Issue #17: Hardcoded Values Drift from Source of Truth

**Symptom:** Dashboard shows "Workshop: 70% complete" but WHITE-PAPER/SUBMISSION_STATUS.md says "READY".

**Cause:** Dashboard page has hardcoded progress bars and status text that doesn't auto-sync with actual status files.

**Affected files:**
- `publications.py` — hardcoded `st.progress()` values
- `AI_ARMADA.py` — hardcoded run counts in header banners
- `NYQUIST_STATUS.json` — manual publication_status fields

**Solution:** Update all locations when status changes:
```
1. Update WHITE-PAPER/README.md (source of truth)
2. Update publication_status.json (machine-readable)
3. Update dashboard/pages/publications.py (hardcoded display)
4. Update NYQUIST_STATUS.json (layer-level summary)
```

**Better Pattern (TODO):** Read from `publication_status.json` instead of hardcoding:
```python
pub_status = load_publication_status()
st.progress(pub_status['publications']['workshop']['completion'])
```

---

### Issue #18: Duplicate Dictionary Keys in Python

**Symptom:** Data mysteriously disappears or shows wrong values. No error raised.

**Cause:** Python dictionaries silently allow duplicate keys — the second value overwrites the first:
```python
RUNS = {
    "run_020b": {"name": "Grok Tribunal"},  # This gets overwritten!
    "run_020b": {"name": "Thermometer Result"},  # This wins
}
```

**Solution:** Use unique keys. If you have similar runs, use suffixes:
```python
RUNS = {
    "run_020a": {"name": "Cross-Platform Tribunal"},
    "run_020b": {"name": "Thermometer Result"},
}
```

**Detection:** Search for duplicate keys before committing:
```bash
# In Python file
grep -n '"run_020' dashboard/pages/AI_ARMADA.py
```

**Real Example:** AI_ARMADA.py had two `"run_020b"` entries — Grok data was silently lost.

---

### Issue #19: Run Number Confusion (020 vs 020A vs 020B)

**Symptom:** Wrong data displayed for runs, confusion about what each run contains.

**Cause:** Run naming convention evolved mid-project:
- Run 020 = Original Claude Tribunal
- Run 020A = Cross-Platform Tribunal (multiple providers)
- Run 020B = Induced vs Inherent (Thermometer Result)

**Solution:** Establish and document canonical naming:
```
| Key | Name | What It Is |
|-----|------|------------|
| run_020 | Tribunal | Original Claude-only run |
| run_020a | Cross-Platform Tribunal | 7 providers, 32 sessions |
| run_020b | Thermometer Result | Control vs Treatment, 41% inherent |
```

**Files to update when adding runs:**
1. `AI_ARMADA.py` EXPERIMENT_RUNS dict
2. `dashboard/README.md` run history table
3. `WHITE-PAPER/README.md` run status table
4. Manifest files in `0_results/manifests/`

---

### Issue #20: Session State Not Updating on Rerun

**Symptom:** Click a button but page shows old data until manual refresh.

**Cause:** Streamlit's `st.rerun()` or experimental rerun doesn't always propagate session state changes.

**Solution:** Use the safe rerun pattern:
```python
def safe_rerun():
    """Trigger rerun with slight delay for state to propagate."""
    time.sleep(0.1)
    st.rerun()

# Usage
if button_clicked:
    st.session_state.selected_run = new_value
    safe_rerun()
```

**Also check:** Session state initialization happens BEFORE any widget renders:
```python
# At TOP of render function
if "armada_run" not in st.session_state:
    st.session_state.armada_run = "run_020b"

# Then use it
current_run = st.session_state.armada_run
```

---

### Issue #21: Image Paths Break After Directory Reorganization

**Symptom:** Visualizations show broken image icons or "Image not found".

**Cause:** Paths are relative to old directory structure. Common after moving:
- `visualizations/` → `visualizations/pics/`
- `results/` → `0_results/runs/`

**Solution:** Always use path variables, not hardcoded strings:
```python
# Define paths at module top
VIZ_PICS = ARMADA_DIR / "visualizations" / "pics"

# Use the variable
run017_pics = VIZ_PICS / "run017"  # NOT: ARMADA_DIR / "visualizations" / "run017"
```

**Detection:** When images break, check:
1. Does the directory exist? `ls -la path/to/dir`
2. Does the path variable point there? Add `print(f"Looking in: {path}")`

**Real Example:** Run 017 images broke because path used `ARMADA_DIR / "visualizations" / "run017"` instead of `VIZ_PICS / "run017"`.

---

### Issue #22: Git Push Says "Everything up-to-date" But Commit Exists

**Symptom:** `git push` returns "Everything up-to-date" immediately after committing.

**Cause:** Usually means the remote already has your commit (fast-forward already happened), OR you're on a different branch than you think.

**Diagnosis:**
```bash
# Check what branch you're on
git branch --show-current

# Check if local is ahead of remote
git status  # Should say "Your branch is ahead of..."

# Check remote tracking
git log --oneline origin/Consciousness..HEAD
```

**Common causes:**
- Automatic push from previous operation
- Working on detached HEAD
- Remote branch name doesn't match local

---

### Issue #23: Thermometer Result Percentage Confusion (41% vs 82%)

**Symptom:** Documentation says both "41% inherent" and "82% inherent".

**Cause:** Two different metrics measuring different things:
- **41%** = Inherent drift RATIO (Control B→F / Treatment B→F)
- **82%** = Complement interpretation (82% of final drift is inherent to extended interaction)

**Clarification:**
```
Control (no probing):  B→F = 0.399
Treatment (tribunal):  B→F = 0.489

Ratio: 0.399 / 0.489 = 0.816 ≈ 82%

Meaning: 82% of Treatment's final drift would have happened anyway.
         Only 18% is "caused" by the probing.
```

**When to use which:**
- "41%" when discussing the ratio directly
- "82%" when discussing "how much is inherent" (more intuitive)

Both are correct — just different framings of the same data.

---

### When Adding New Sections

1. **Start with native components** (st.metric, st.columns, st.progress)
2. **Test incrementally** — add one element at a time
3. **If HTML is needed** — keep it flat, max 2 nesting levels
4. **Pre-compute all values** before f-strings
5. **Update ALL related files** when status changes (see Issue #17)
6. **Add to this section** if you discover a new gotcha!

---

## Design Philosophy

- **Dark gradient backgrounds** (linear gradients)
- **Page-turning dividers** (double borders)
- **Ledger cards** with rounded corners and shadows
- **Badge labels** for status (FROZEN, ACTIVE, etc.)
- **Georgia serif font** for headers
- **Minimal, focused information hierarchy**

Each "page" represents a different lens on the Nyquist Consciousness framework, maintaining the metaphor of turning through a physical ledger.

---

## Current Experiments

### EXP2-SSTACK Status

| Phase | Focus | Status |
|-------|-------|--------|
| Phase 1 | Reasoning probes | PASSED (PFI 0.849) |
| Phase 2 | Voice/Values/Narrative | PASSED |
| Phase 2b | Self-Model (declarative) | EXCLUDED (PFI 0.66) |
| Phase 2c | Self-Model (behavioral) | PASSED (PFI 0.8866) |
| Phase 2.5 | Ablation Testing | READY |
| Phase 3 | PC Mapping | SPEC |

**Triple-Dip Insight**: Models say behavioral probes are more reliable than declarative.

---

**Generated**: 2025-11-27
**Updated**: 2025-12-31
**Version**: 1.8
**Status**: Mission Control Active — IRON CLAD methodology integrated (EH=0.80, 2 PCs)
