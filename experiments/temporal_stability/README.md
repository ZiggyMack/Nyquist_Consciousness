<!-- FROSTY_MANIFEST
last_reviewed: 2025-12-28
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
-->
# TEMPORAL STABILITY EXPERIMENTS (S7)

**Testing the Identity-Locked Loop (ILL) Framework**

See [S7_ARMADA/README.md](S7_ARMADA/README.md) for complete Armada documentation.
See [S7_ARMADA/START_HERE.md](S7_ARMADA/START_HERE.md) for operations guide.

---

## Current Status (December 22, 2025 - VERIFIED)

| Run | Files | Valid Results | Status | Methodology |
|-----|-------|---------------|--------|-------------|
| **Run 023d** | 825+ | 825+ | **IRON CLAD** | Cosine (EH=0.80) |
| **Run 018** | 465 | 337 | **52.6%** (82 runs needed) | Cosine (EH=0.80) |
| **Run 020A** | 33 | ~20 | **50%** (needs verification) | Cosine (EH=0.80) |
| **Run 020B** | 16 | 16 | **COMPLETE** (gpt-4o only) | Cosine (EH=0.80) |
| **Run 022** | - | - | READY (LOGOS Commutation Cartography) | - |

**Note:** Previous claims of "184 files, IRON CLAD" for Run 018 were incorrect. Verified Dec 22: 465 files, 337 valid, 52.6% IRON CLAD.

**Fleet Size:** 54+ operational ships across 5 providers, 10 model families (Anthropic, OpenAI, Google, xAI, Together.ai)

**THE THREE CORE CLAIMS — ALL VALIDATED:**

1. **DRIFT IS REAL** — p=2.40e-23 (Run 023d), 88% prediction accuracy
2. **WE DON'T CAUSE IT** — 41% inherent drift ratio (cross-provider)
3. **WE CAN MEASURE IT** — PFI d=0.977, σ²=0.00087 cross-architecture

---

## QUICK START

```bash
# Install all dependencies (from this directory)
py -m pip install -r requirements.txt

# Run S7 Armada experiments
cd S7_ARMADA

# Check fleet status first
py 1_CALIBRATION/run_calibrate_parallel.py --quick --depth ping

# Run an experiment (cost-aware fleet selection)
py 11_CONTEXT_DAMPING/run018_recursive_learnings.py --experiment gravity --providers patrol-lite
```

---

## REQUIREMENTS.TXT PHILOSOPHY

**This file is intentionally maintained as the single source of truth for all S7 dependencies.**

A cold-boot Claude (or any new contributor) should be able to:

1. Navigate to this directory
2. Run `py -m pip install -r requirements.txt`
3. Successfully execute ANY script in this directory or subdirectories

When adding new functionality that requires new packages:

- **Always** add the dependency to `requirements.txt`
- Include a comment explaining what it's for
- Test that a fresh install works

Current dependencies cover:

- **API clients**: anthropic, openai, google-generativeai
- **Data processing**: pyyaml, python-dotenv, numpy
- **Visualization**: matplotlib

---

## ⚠️ API KEYS WARNING - READ THIS BEFORE COMMITTING

**This is the #1 source of headaches in this project.**

### The Situation

Experiment scripts (like `4_BASIN_TOPOLOGY/run008_prep_pilot.py`) contain hardcoded API keys for Anthropic, OpenAI, and Google. These keys are:

- **REQUIRED** for running experiments
- **MUST NOT** be committed to git
- **MUST NOT** be deleted (we need them!)

### Before Any Git Commit

1. **Check `.gitignore`** - Ensure your script with keys is listed
2. **Run `git status`** - Look for any `*_with_keys.py` or similar files
3. **If you see key files staged** - STOP and add them to `.gitignore` first

Current `.gitignore` patterns for keys:

```
experiments/temporal_stability/S7_ARMADA/4_BASIN_TOPOLOGY/run008_prep_pilot.py
experiments/temporal_stability/S7_ARMADA/4_BASIN_TOPOLOGY/run008_with_keys.py
**/run*_with_keys.py
**/*API_KEY*
**/*api_key*
**/*secret*
```

### Creating New Experiment Scripts

When creating a new experiment that needs API keys:

1. Name it clearly (e.g., `run009_with_keys.py`)
2. Add it to `.gitignore` BEFORE your first commit
3. Consider using the `*_with_keys.py` naming convention (already gitignored)

### If You Accidentally Commit Keys

**Don't panic, but act quickly.** The keys are now in git history even if you delete the file.

**Option 1: If NOT pushed yet**

```bash
# Undo the last commit, keep changes staged
git reset --soft HEAD~1

# Remove the file from staging
git reset HEAD path/to/file_with_keys.py

# Add to .gitignore
echo "path/to/file_with_keys.py" >> .gitignore

# Recommit without the keys
git add .gitignore
git commit -m "Add gitignore for key file"
```

**Option 2: If already pushed (requires history rewrite)**

```bash
# Remove file from ALL history (destructive - coordinate with team!)
git filter-branch --force --index-filter \
  "git rm --cached --ignore-unmatch path/to/file_with_keys.py" \
  --prune-empty --tag-name-filter cat -- --all

# Force push (DANGEROUS - only if you're sure)
git push origin main --force
```

**Option 3: Use BFG Repo-Cleaner (easier)**

```bash
# Install BFG (faster than filter-branch)
# Then run:
bfg --delete-files file_with_keys.py
git reflog expire --expire=now --all && git gc --prune=now --aggressive
git push --force
```

**After any history rewrite:**

- Rotate/regenerate ALL exposed API keys immediately
- Notify Ziggy if keys may have been exposed

### The Golden Rule

**When in doubt, check `git status` before `git commit`.**

One extra `git status` is worth avoiding hours of git history surgery.

---

## DIRECTORY STRUCTURE

```text
temporal_stability/
├── README.md              # This file
├── requirements.txt       # All Python dependencies for S7 work
├── s7_config.yaml         # Configuration
├── s7_*.py                # Core meta-loop scripts (legacy)
│
├── S7_ARMADA/             # Cross-architecture mapping (54+ ships, Run 006+)
│   ├── START_HERE.md      # Operations guide - READ FIRST
│   ├── README.md          # Theory and background
│   ├── 1_CALIBRATION/     # Fleet calibration utilities
│   ├── 2-10_*/            # Search type experiments (Anchor/Flex, Event Horizon, etc.)
│   ├── 11_CONTEXT_DAMPING/  # Phase 4 experiments (Run 017-020)
│   ├── 12_CFA/            # CFA-ARMADA Integration Pipeline
│   ├── 13_LOGOS/          # LOGOS Commutation Cartography (Run 022)
│   ├── 14_CONSCIOUSNESS/  # Gold/Diamond/Quartz Rush Mining Operations
│   ├── 0_docs/            # Summaries, specs, analysis
│   ├── 0_results/         # Consolidated JSON results
│   └── visualizations/    # Charts and plots
│
└── OUTPUT/                # Meta-loop results (Runs 001-005, legacy)
```

---

## TWO PARADIGMS

**META-LOOP** (Legacy): Deep single-model testing (adaptive curriculum)
**ARMADA** (Active): Wide cross-architecture mapping (54+ ship fleet across 5 providers)

Both feed Phase 3 Orchestrator and ILL Framework validation.

---

## Key Validated Findings

| Finding | Status | Evidence |
|---------|--------|----------|
| **Event Horizon (0.80)** | VALIDATED | p=2.40e-23 (Run 023d perturbation) |
| **Drift is INHERENT** | VALIDATED | Run 020B: 82% inherent, 18% induced |
| **PFI Measures Identity** | VALIDATED | d=0.977, ρ=0.91 embedding invariance |
| **Recovery is Natural** | VALIDATED | 100% manifold return (Platonic Coordinates) |

---

## Run History Highlights

| Run | Focus | Key Finding |
|-----|-------|-------------|
| 006-009 | Basin/Event Horizon | Event Horizon discovered and validated |
| 010-013 | Anchor/Flex/Boundary | Identity Confrontation Paradox |
| 014-016 | Rescue/Stability/Settling | boundary_density strongest predictor |
| **017** | Context Damping | 222 runs, 97.5% stable (Phase 4 start) |
| **018** | Recursive Learnings | Fleet hypotheses testing |
| **019** | Live Ziggy | Witness-side anchors validated |
| **020A/B** | Tribunal/Induced | 82% drift inherent, 1.351 peak achieved |
| **022** | Commutation Cartography | LOGOS algebra validation (READY) |

See [S7_ARMADA/START_HERE.md](S7_ARMADA/START_HERE.md) for complete run history.

---

*Last Updated: December 28, 2025 (Methodology unified to Cosine EH=0.80)*
