<!-- FROSTY_MANIFEST
last_reviewed: 2026-06-30
depends_on:
  - ./run_cfa_trinity_v3.py
  - ./VUDU_NETWORK/load_identity.py
  - ./VUDU_NETWORK/IDENTITY_FILES/
impacts:
  - ../0_results/runs/
  - ./SYNC_OUT/
keywords:
  - consciousness
  - experiments
  - armada
  - cfa
  - trinity
  - ypa
-->
# 12_CFA: CFA-ARMADA Pipeline

```text
================================================================================
                         CFA-ARMADA INTEGRATION PIPELINE
================================================================================
    Purpose: Bidirectional experiment exchange between CFA Repo and ARMADA

    CFA provides: Axioms, claims, audit protocols, identity files
    ARMADA provides: API access, fleet execution, adversarial scoring

    Location: experiments/temporal_stability/S7_ARMADA/12_CFA/
================================================================================
```

**Last Updated:** 2026-07-07
**Status:** OPERATIONAL — 5 FUTs (CT, MdN, PT, G, B), 580+ runs, Buddhism batch running

---

## Before You Start

**ALWAYS check `AUDIT_TRACKER.md` before running experiments or assuming what data exists.**

Runs are scattered across two repos and multiple directories. The tracker has the complete inventory, completion matrix, and outstanding work list. Do not guess.

---

## Quick Start

### Phase 1: Philosophical Quality Audit

```bash
# Use --stance to specify any matchup (see AUDIT_TRACKER.md for full list)
py run_cfa_trinity_v3.py --stance ct_vs_b --phase 1 --external-identities --skip-exit-survey

# Control condition (no identity pressure)
py run_cfa_trinity_v3.py --stance ct_vs_b --phase 1 --control --skip-exit-survey
```

### Batch Runs

Use the dedicated batch scripts for multi-matchup runs:

```bash
py run_buddhism_batch.py      # 8 matchups x 2 conditions x 10 runs = 160
py run_gnostic_batch.py       # 6 matchups (completed)
```

### After Any Experiment Completes

**Update `AUDIT_TRACKER.md`** with new run counts and status changes. This is manual — the batch scripts print final counts at completion, use those to update the tracker.

### Phase 2 (Trinity²): YPA Lever Calibration

Use `--preset` for named prior-value datasets (no manual typing needed):

```bash
# CT Forward — score CT levers with preset priors
py run_cfa_trinity_v3.py --phase 2 --preset ct --external-identities --component 1 \
  --phase1-results ../0_results/runs/S7_cfa_trinity_v2_20260629_132540.json

# MdN Reverse — score MdN levers with preset priors + role swap
py run_cfa_trinity_v3.py --phase 2 --preset mdn --reverse --external-identities --component 1 \
  --phase1-results ../0_results/runs/S7_cfa_trinity_20260630_010555.json
```

Note: Phase 2 runs **include exit surveys** by default — the reflective questions capture
whether auditors fought about lever definitions vs scores, which Phase 1 findings
actually influenced them, and whether priors anchored or were genuinely contested.
Only skip exit surveys for Phase 1 batch runs where throughput matters more than diagnostics.

### Batch Runs (10x)

Copy-paste these to run full batches. Phase 2 runs ~5-8 min each (exit survey included):

```bash
# 10x Phase 2 CT golden batch
for i in $(seq 1 10); do echo "=== CT P2 RUN $i/10 ===" && py run_cfa_trinity_v3.py --phase 2 --preset ct --external-identities --component 1 --skip-baseline --phase1-results ../0_results/runs/S7_cfa_trinity_v2_20260629_132540.json; done

# 10x Phase 2 MdN reverse golden batch
for i in $(seq 1 10); do echo "=== MdN P2 RUN $i/10 ===" && py run_cfa_trinity_v3.py --phase 2 --preset mdn --reverse --external-identities --component 1 --skip-baseline --phase1-results ../0_results/runs/S7_cfa_trinity_20260630_010555.json; done
```

### Other Useful Commands

```bash
# Dry run (no API calls, tests pipeline end-to-end)
py run_cfa_trinity_v3.py --dry-run --phase 2 --preset ct --phase1-results <path>

# Override a single preset value (--prior-values overrides --preset)
py run_cfa_trinity_v3.py --phase 2 --prior-values CCI=7.5,EDB=8.5,PF_I=7.0,PF_E=8.0,AR=8.5,MG=8.5 ...

# List available external identities
py run_cfa_trinity_v3.py --list-identities
```

### Available Presets (Phase 2)

| Preset | Key Notes |
|--------|-----------|
| `ct` | CCI=7.5, EDB=8.5, PF_I=7.0, PF_E=8.0, AR=8.5, MG=8.5 |
| `mdn` | CCI=8.0, EDB=7.5, PF_I=10.0, PF_E=3.0, AR=7.0, MG=4.0 |
| `pt` | CCI=7.0, EDB=7.5, PF_I=5.0, PF_E=8.5, AR=8.0, MG=7.0 |
| `g` | CCI=6.0, EDB=5.0, PF_I=3.0, PF_E=9.0, AR=7.0, MG=6.5 |
| `b` | CCI=8.0, EDB=7.0, PF_I=5.0, PF_E=9.0, AR=7.5, MG=8.0 |

---

## Two-Phase Experiment Design

### Phase 1: Philosophical Quality Audit

Maps the philosophical terrain — what does the worldview claim, how strong are those claims?

**Metrics:** BFI, CA, IP, ES, LS, MS, PS
**Purpose:** Establish agreed-upon battleground before calibrating utility scores
**Status:** Complete for CT/MdN/PT/G (300+ runs). Buddhism batch running.

### Phase 2: Trinity² — YPA Lever Calibration

Armed with Phase 1 findings, scores HOW WELL the worldview performs on utility dimensions.

**Metrics:** CCI, EDB, PF_I, PF_E, AR, MG (with 0/5/10 scoring anchors)
**Purpose:** Produce adversarially-validated lever values for YPA formula
**Requires:** Phase 1 results JSON as context input + current YAML lever values as priors
**Status:** Complete for CT/MdN/PT/G (~280 runs). Buddhism Phase 2 not yet started.

### Why Two Phases?

Phase 1 FEELS like scoring — you get numbers. But BFI/CA/IP/ES/LS/MS/PS describe *what* a worldview claims. The YPA formula needs *how well* it performs (CCI/EDB/PF/AR/MG). You can't honestly answer the second without the first.

---

## Stance Configuration

Stances are defined in `run_cfa_trinity_v3.py` in the `STANCES` dict. Each stance specifies subject/opponent frameworks, Claude/Grok advocacy positions, role-specific prompt lines, and deliberation framing.

20 stances across 5 FUTs (10 matchups, each bidirectional):

| Stance | Subject | Opponent | Claude | Grok |
|--------|---------|----------|--------|------|
| ct_vs_mdn | CT | MdN | PRO-CT | ANTI-CT |
| mdn_vs_ct | MdN | CT | ANTI-MdN | PRO-MdN |
| ct_vs_pt | CT | PT | ANTI-CT | PRO-CT |
| pt_vs_ct | PT | CT | PRO-PT | ANTI-PT |
| mdn_vs_pt | MdN | PT | ANTI-MdN | PRO-MdN |
| pt_vs_mdn | PT | MdN | PRO-PT | ANTI-PT |
| ct_vs_g | CT | G | PRO-CT | ANTI-CT |
| g_vs_ct | G | CT | ANTI-G | PRO-G |
| mdn_vs_g | MdN | G | ANTI-MdN | PRO-MdN |
| g_vs_mdn | G | MdN | PRO-G | ANTI-G |
| pt_vs_g | PT | G | PRO-PT | ANTI-PT |
| g_vs_pt | G | PT | ANTI-G | PRO-G |
| ct_vs_b | CT | B | PRO-CT | ANTI-CT |
| b_vs_ct | B | CT | ANTI-B | PRO-B |
| mdn_vs_b | MdN | B | ANTI-MdN | PRO-MdN |
| b_vs_mdn | B | MdN | PRO-B | ANTI-B |
| pt_vs_b | PT | B | PRO-PT | ANTI-PT |
| b_vs_pt | B | PT | ANTI-B | PRO-B |
| g_vs_b | G | B | PRO-G | ANTI-G |
| b_vs_g | B | G | ANTI-B | PRO-B |

Each matchup pair (e.g., ct_vs_mdn / mdn_vs_ct) is a role swap — Claude and Grok switch advocacy sides while the subject changes. Forward/reverse averaging produces bias-corrected calibration values.

---

## CLI Reference: run_cfa_trinity_v3.py

| Flag | Description |
|------|-------------|
| `--phase {1,2}` | Phase 1 = philosophical audit, Phase 2 = YPA lever calibration |
| `--phase1-results PATH` | Path to Phase 1 JSON (required for Phase 2) |
| `--stance NAME` | Stance configuration (e.g. `ct_vs_b`, `g_vs_mdn`). See Stance Configuration above. |
| `--preset NAME` | Named prior-value preset for Phase 2 (`ct`, `mdn`, `pt`, `g`, `b`). See Presets table above. |
| `--prior-values VALS` | Comma-separated lever=value pairs (e.g. `CCI=7.5,EDB=6.0`). Overrides `--preset`. |
| `--component {1,2,both}` | 1=Adversarial Pilot, 2=Axioms Review, both=Double-dip |
| `--metrics METRICS` | Comma-separated metrics (defaults to phase-appropriate set) |
| `--external-identities` | Load LITE identity files from VUDU_NETWORK/IDENTITY_FILES/ |
| `--control` | Control condition: no framework identity, no stance assignment |
| `--duplicate-reflection` | Run exit survey twice for reflection-to-reflection variance |
| `--dry-run` | Test pipeline without API calls |
| `--skip-baseline` | Skip 8-question baseline capture |
| `--skip-exit-survey` | Skip exit surveys |
| `--list-identities` | List available external identities and exit |

---

## Directory Structure

```text
12_CFA/
|-- README.md                    # This file
|-- AUDIT_TRACKER.md             # <-- CHECK THIS FIRST (run inventory)
|-- run_cfa_trinity_v3.py        # Main Trinity audit engine
|-- run_gnostic_batch.py         # Gnostic 6-matchup batch (complete)
|-- run_gnostic_rerun.py         # Gnostic gap-fill runner (complete)
|-- run_buddhism_batch.py        # Buddhism 8-matchup batch (running)
|
|-- SYNC_OUT/                    # Deliveries to CFA Claude
|   |-- pending/                 # Care packages awaiting delivery
|   |-- running/                 # Active — staged JSONs + analysis
|   |   +-- raw_runs/            # JSONs organized by delivery batch
|   |       |-- 1/ - 8/          # Original + gnostic deliveries
|   |       +-- 9_gnostic/       # 150 clean v3 runs (15 folders)
|   +-- completed/               # Delivered .md summaries (NO .json)
|
|-- VUDU_NETWORK/                # Multi-model audit infrastructure
|   |-- README.md                # VUDU protocol docs
|   |-- load_identity.py         # Dynamic identity loader
|   +-- IDENTITY_FILES/          # Per-auditor LITE identity packages
|       |-- claude/CLAUDE_LITE.md
|       |-- grok/GROK_LITE.md
|       |-- nova/NOVA_LITE.md
|       +-- llama/LLAMA_LITE.md
|
|-- CFA_RESPONSES/               # Feedback/reviews from CFA
|-- schemas/                     # Design docs and JSON schemas
|-- scripts/                     # Automation utilities
+-- results/                     # Local results (primary store is ../0_results/runs/)
```

---

## Data Lifecycle

```text
API calls → run_cfa_trinity_v3.py
         → ../0_results/runs/S7_cfa_trinity_HHMMSS.json   (raw output)
         → SYNC_OUT/running/raw_runs/                      (copy for CFA Claude)
         → Extract summaries → SYNC_OUT/running/*.md       (human-readable)
         → After delivery  → SYNC_OUT/completed/*.md       (archive)
         → Pre-fix JSONs   → root .archive/runs/           (cold storage)
```

**Critical constraints:**
- Do NOT move .json files into SYNC_OUT/completed/ — that directory is for .md summaries only
- Raw JSONs go from 0_results/runs/ → root .archive/runs/ (NOT 0_results/runs/.archive/)

---

## The Trinity

| Auditor | Provider | Model | Lens | Named Biases |
|---------|----------|-------|------|-------------|
| **Claude** | Anthropic | claude-sonnet-4-6 | Teleological | Comprehensive Approach (0.5), Teleological Emphasis (0.3), Narrative Smoothing (0.2) |
| **Grok** | xAI | grok-3 | Empirical | Empiricism Over Meaning (0.4), Data Availability (0.3), Precision Over Accuracy (0.2) |
| **Nova** | OpenAI | gpt-4o | Symmetry | Mathematical Symmetry (0.3), Pattern Overgeneralization (0.2), Aesthetic Balance (0.4) |

Identity is two layers:
1. **System prompt** — Full LITE file content (~1500 tokens)
2. **Scoring prompt** — Per-round stance/calibration/tools in user message

---

## Phase 2 (Trinity²) Scoring Anchors

Each YPA lever has 0/5/10 anchors injected into scoring prompts:

| Lever | 0 | 5 | 10 |
|-------|---|---|-----|
| **CCI** | Self-contradictory, no resolution | Live tensions, acknowledged not dissolved | Full logical closure, no contradictions |
| **EDB** | Narrow domain, no mechanism | Multiple domains, shallow in most | Rich mechanism across all domains |
| **PF-I** | No testable predictions | Some predictions, limited scope | Extraordinary predictive success |
| **PF-E** | Brackets meaning/death/suffering | Partial existential resources | Rich account of meaning and flourishing |
| **AR** | Ad hoc, cluttered, no unifying principle | Pockets of elegance, visible seams | Striking parsimony, widely recognized beauty |
| **MG** | Cannot derive ought from is | Some internal moral content | Rich moral theory from own metaphysics |

Phase 2 soft dependencies (advisory, not mandatory):
- CCI <- LS, CA
- EDB <- ES, IP, CA
- PF-I <- PS, ES
- PF-E <- BFI, MS, PS
- AR <- IP, LS, ES
- MG <- MS, PS, LS

---

## Phase 2 Output Format

Each Phase 2 run produces per lever:

```json
{
  "metric": "CCI",
  "claude_score": 7.8,
  "grok_score": 6.2,
  "final_score": 7.0,
  "convergence": 0.84,
  "prior_value": 7.5,
  "delta": -0.5,
  "delta_reason": "Adversarial review decreased from prior 7.5 to 7.0",
  "calibration_status": "stable",
  "confidence_claude": "medium",
  "confidence_grok": "high",
  "phase1_deps_claude": ["LS", "CA"],
  "phase1_deps_grok": ["LS"]
}
```

Calibration status labels:
- **stable**: Low variance, low stance sensitivity
- **contested**: High spread but convergent reasoning
- **unstable**: High variance or forward/reverse sensitivity >1.0
- **underdefined**: Auditors fighting over the lever definition itself

---

## Experiment History

See `AUDIT_TRACKER.md` for exact run counts, locations, and the completion matrix.

### CT vs MdN — Original Batch (2026-06-29/30)

- 80 runs total (P1 + P2, external + control, both directions)
- First experiment; established instrument symmetry (~12-13% convergence gap)
- Archived in CFA repo after processing

### CT vs PT, MdN vs PT — Expansion (2026-07-01/02)

- 80 runs each matchup pair (P1 + P2, external + control)
- In 0_results/runs/

### Gnostic Batch (2026-07-02/05)

- 6 matchups (CT/MdN/PT vs G, both directions), ~341 runs (P1 + P2)
- 150 clean v3 runs staged in SYNC_OUT/running/raw_runs/9_gnostic/
- Key findings: G most extreme profile, BFI/MS most vulnerable to identity, ~1.0-1.5 point identity effect

### Buddhism Batch (2026-07-07, running)

- 8 matchups (CT/MdN/PT/G vs B, both directions), 160 Phase 1 runs
- Script: run_buddhism_batch.py
- Phase 2 not yet started

### Total: ~580+ runs across all experiments

---

## Convergence Protocol

- **98%+**: Full convergence (target)
- **90-97%**: Acceptable convergence (minimum 2 rounds)
- **<90%**: Nova assesses fairness; may declare Crux Point
- **Crux types**: Definitional, Methodological, Philosophical
- **Max rounds**: 5 per metric

---

## API Requirements

Set these environment variables (in `.env` at repo root):

```bash
ANTHROPIC_API_KEY=sk-ant-...   # Claude
OPENAI_API_KEY=sk-...          # Nova + embeddings
XAI_API_KEY=xai-...            # Grok
```

---

## Related Documents

| Document | Location | Purpose |
|----------|----------|---------|
| Audit Tracker | `AUDIT_TRACKER.md` | Run inventory, completion matrix, outstanding work |
| VUDU Network | `VUDU_NETWORK/README.md` | Multi-model protocol, identity files, data lifecycle |
| Gnostic Care Package | `SYNC_OUT/pending/gnostic_full_care_package.md` | 181-run analysis for CFA Claude |
| Design Spec | `schemas/RUN_CFA_DESIGN.md` | Original experiment design |

---

> "First, we map the terrain. Then, we calibrate the instruments."
>
> -- The CFA-ARMADA Pact (Phase 1 -> Phase 2)
