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

**Last Updated:** 2026-06-30
**Status:** OPERATIONAL (v3.1 — Phase 1 complete, Trinity² implemented)

---

## Quick Start

```bash
# Phase 1: Philosophical quality audit (BFI/CA/IP/ES/LS/MS/PS)
py run_cfa_trinity_v3.py --external-identities --component 1 --skip-exit-survey

# Phase 1 reverse stance (MdN scored, role swap)
py run_cfa_trinity_v3.py --reverse --external-identities --component 1 --skip-exit-survey

# Phase 1 control (no identity, base model priors)
py run_cfa_trinity_v3.py --control --component 1 --skip-exit-survey

# Phase 2 (Trinity²): YPA lever calibration (CCI/EDB/PF_I/PF_E/AR/MG)
py run_cfa_trinity_v3.py --phase 2 --external-identities --component 1 --skip-exit-survey \
  --phase1-results ../0_results/runs/S7_cfa_trinity_20260629_132540.json \
  --prior-values CCI=7.5,EDB=7.0,PF_I=3.0,PF_E=8.0,AR=7.0,MG=8.0

# Dry run (no API calls, tests pipeline)
py run_cfa_trinity_v3.py --dry-run --phase 2 --phase1-results <path> --prior-values <vals>

# List available external identities
py run_cfa_trinity_v3.py --list-identities
```

---

## Two-Phase Experiment Design

### Phase 1: Philosophical Quality Audit (done)

Maps the philosophical terrain — what does the worldview claim, how strong are those claims?

**Metrics:** BFI, CA, IP, ES, LS, MS, PS
**Purpose:** Establish agreed-upon battleground before calibrating utility scores
**Status:** 30 validated runs (CT: 10 golden + 10 control, MdN: 10 golden)

### Phase 2: Trinity² — YPA Lever Calibration

Armed with Phase 1 findings, scores HOW WELL the worldview performs on utility dimensions.

**Metrics:** CCI, EDB, PF_I, PF_E, AR, MG (with 0/5/10 scoring anchors)
**Purpose:** Produce adversarially-validated lever values for YPA formula
**Requires:** Phase 1 results JSON as context input + current YAML lever values as priors
**Status:** Implemented, ready to run

### Why Two Phases?

Phase 1 FEELS like scoring — you get numbers. But BFI/CA/IP/ES/LS/MS/PS describe *what* a worldview claims. The YPA formula needs *how well* it performs (CCI/EDB/PF/AR/MG). You can't honestly answer the second without the first.

---

## Stance Configuration

Each experiment runs in a stance that assigns advocacy/challenge roles:

| Stance | Flag | Claude Role | Grok Role | Subject |
|--------|------|-------------|-----------|---------|
| **Forward** | (default) | PRO-CT (teleological advocate) | ANTI-CT (empirical challenger) | Classical Theism |
| **Reverse** | `--reverse` | ANTI-MdN (teleological challenger) | PRO-MdN (empirical advocate) | Methodological Naturalism |

The reverse stance is a **role swap**, not just a subject swap. Each framework gets scored by its lens-aligned advocate:
- CT scored by Claude PRO (teleological lens aligns with CT)
- MdN scored by Grok PRO (empirical lens aligns with MdN)

The forward/reverse averaging produces bias-corrected calibration values.

---

## CLI Reference: run_cfa_trinity_v3.py

| Flag | Description |
|------|-------------|
| `--phase {1,2}` | Phase 1 = philosophical audit, Phase 2 = YPA lever calibration |
| `--phase1-results PATH` | Path to Phase 1 JSON (required for Phase 2) |
| `--prior-values VALS` | Comma-separated lever=value pairs for Phase 2 priors (e.g. `CCI=7.5,EDB=6.0`) |
| `--reverse` | Reverse stance: Claude ANTI-MdN, Grok PRO-MdN |
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
|-- run_cfa_trinity_v3.py        # Main execution script (v3.1)
|
|-- SYNC_OUT/                    # Experiment data exchange with CFA Claude
|   |-- pending/                 # Not yet executed
|   |-- running/                 # Active — current MdN results + raw JSONs
|   |   |-- MDN_GOLDEN_BATCH_RESULTS_20260630.md
|   |   +-- raw_runs/            # JSONs for CFA Claude's SMV pipeline
|   |       |-- S7_cfa_trinity_20260630_*.json   (MdN golden)
|   |       +-- ct_batch_20260629/               (CT golden + control)
|   +-- completed/               # Delivered summaries (.md only, NO .json)
|       |-- GOLDEN_BATCH_RESULTS_20260629.md
|       |-- CALIBRATION_PARAMETERS_20260629.md
|       +-- ...
|
|-- VUDU_NETWORK/                # Multi-model audit infrastructure
|   |-- load_identity.py         # Dynamic identity loader
|   +-- IDENTITY_FILES/          # Per-auditor LITE identity packages
|       |-- claude/CLAUDE_LITE.md   (Teleological, v5.0.0, hash 1bbec1e1)
|       |-- grok/GROK_LITE.md       (Empirical, v3.5.2, hash 00cd7327)
|       |-- nova/NOVA_LITE.md       (Symmetry)
|       +-- llama/LLAMA_LITE.md     (Dialectic)
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

## Completed Experiments

### CT Golden Batch (2026-06-29)
- 10 runs, Claude PRO-CT / Grok ANTI-CT
- Conv: 85.8% in 4.0 rounds
- Key finding: "Identity Creates Debate, Not Inflation"

### CT Control Batch (2026-06-29)
- 10 runs, no identity
- Conv: 97.9% in 1.8 rounds
- Base model priors favor CT (IP=9.2, MS=8.4)

### MdN Golden Batch (2026-06-30)
- 10 runs, Claude ANTI-MdN / Grok PRO-MdN (role swap)
- Conv: 86.2% in 4.1 rounds
- MS is asymmetric metric — both auditors score MdN low
- Instrument stability confirmed: nearly identical convergence as CT

### Pending
- MdN control batch (10 runs with `--reverse --control`)
- Trinity² Phase 2 runs for both CT and MdN (forward + reverse)

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
| CT Golden Results | `SYNC_OUT/completed/GOLDEN_BATCH_RESULTS_20260629.md` | 10-run CT + control comparison |
| MdN Golden Results | `SYNC_OUT/running/MDN_GOLDEN_BATCH_RESULTS_20260630.md` | 10-run MdN + cross-stance symmetry |
| Calibration Parameters | `SYNC_OUT/completed/CALIBRATION_PARAMETERS_20260629.md` | LITE identity extraction for CalibrationDrawer |
| Design Spec | `schemas/RUN_CFA_DESIGN.md` | Original experiment design |

---

> "First, we map the terrain. Then, we calibrate the instruments."
>
> -- The CFA-ARMADA Pact (Phase 1 -> Phase 2)
