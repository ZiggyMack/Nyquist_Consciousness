# 12_CFA: CFA-ARMADA Pipeline

```text
================================================================================
                         CFA-ARMADA INTEGRATION PIPELINE
================================================================================
    Purpose: Bidirectional experiment exchange between CFA Repo and ARMADA

    CFA provides: Axioms, claims, audit protocols, identity files
    ARMADA provides: API access, fleet execution, drift measurement

    Location: experiments/temporal_stability/S7_ARMADA/12_CFA/
================================================================================
```

**Last Updated:** 2025-12-13
**Status:** OPERATIONAL (v2)

---

## Quick Start

```bash
# Run CFA Trinity audit (dry run)
py run_cfa_trinity_v2.py --dry-run --external-identities

# List available external identities
py run_cfa_trinity_v2.py --list-identities

# Run Component 1 only (CT<->MdN Pilot)
py run_cfa_trinity_v2.py --component 1 --metrics BFI,CA --external-identities

# Run full mission (Component 1 + Component 2)
py run_cfa_trinity_v2.py --component both --external-identities
```

---

## Overview

This directory implements the CFA-ARMADA pipeline - a bidirectional experiment exchange system that allows:

1. **CFA -> ARMADA**: CFA designs experiments to test declared axioms
2. **ARMADA -> CFA**: ARMADA executes and returns results with drift data
3. **Feedback Loop**: CFA audits results, refines axiom confidence

---

## Directory Structure

```text
12_CFA/
|-- README.md                    # This file
|-- run_cfa_trinity_v2.py        # Main execution script (v2)
|
|-- SYNC_OUT/                    # Experiment specs FROM CFA (we receive)
|   |-- pending/                 # Not yet executed
|   |-- running/                 # Currently executing
|   +-- completed/               # Finished, awaiting our results
|
|-- SYNC_IN/                     # Our results TO CFA (we send)
|   |-- drafts/                  # Being prepared
|   +-- sent/                    # Delivered to CFA
|
|-- CFA_RESPONSES/               # Feedback/reviews FROM CFA (non-experiment)
|   +-- CFA_LAUNCH_CLEARANCE.md  # Launch authorization
|
|-- VUDU_NETWORK/                # Multi-model audit infrastructure
|   |-- load_identity.py         # Dynamic identity loader
|   +-- IDENTITY_FILES/          # Per-auditor identity packages
|       |-- claude/
|       |   +-- CLAUDE_LITE.md   # Claude identity (Teleological)
|       |-- grok/
|       |   +-- GROK_LITE.md     # Grok identity (Empirical)
|       +-- nova/
|           +-- NOVA_LITE.md     # Nova identity (Symmetry)
|
|-- schemas/                     # Design docs and JSON schemas
|   +-- RUN_CFA_DESIGN.md        # Experiment design specification
|
|-- scripts/                     # Automation utilities
|   |-- run_cfa_experiment.py    # Execute SYNC_OUT specs
|   |-- generate_sync_in.py      # Package results
|   +-- validate_sync.py         # Schema validation
|
+-- results/                     # Raw execution data
    +-- S7_cfa_trinity_v2_*.json # Per-session results
```

---

## The Trinity

| Auditor | Provider | Model | Lens | Stance |
|---------|----------|-------|------|--------|
| **Claude** | Anthropic | claude-sonnet-4 | Teleological | PRO-CT (purpose-driven) |
| **Grok** | xAI | grok-3 | Empirical | ANTI-CT (evidence-driven) |
| **Nova** | OpenAI | gpt-4o | Symmetry | FAIRNESS (pattern-driven) |

---

## Script Usage

### run_cfa_trinity_v2.py

Main execution script for CFA Trinity audits.

**Arguments:**

| Flag | Description |
|------|-------------|
| `--component {1,2,both}` | Which component to run (1=CT<->MdN, 2=Axioms, both=Double-dip) |
| `--metrics METRICS` | Comma-separated metrics for Component 1 (default: BFI,CA,IP,ES,LS,MS,PS) |
| `--dry-run` | Run without API calls |
| `--skip-baseline` | Skip baseline capture |
| `--skip-exit-survey` | Skip exit surveys |
| `--external-identities` | Use external identity files from VUDU_NETWORK/IDENTITY_FILES/ |
| `--list-identities` | List available external identities and exit |

**Examples:**

```bash
# Full dry run with external identities
py run_cfa_trinity_v2.py --dry-run --external-identities

# Single metric test
py run_cfa_trinity_v2.py --dry-run --component 1 --metrics BFI --skip-baseline

# Component 2 only (Axioms Review)
py run_cfa_trinity_v2.py --component 2 --external-identities

# Live run (requires API keys)
py run_cfa_trinity_v2.py --external-identities
```

---

## External Identity System

The VUDU_NETWORK/IDENTITY_FILES/ directory allows swapping auditor personalities without modifying the script.

### Adding a New Identity

1. Create directory: `VUDU_NETWORK/IDENTITY_FILES/[auditor_name]/`
2. Add identity file: `[AUDITOR_NAME]_LITE.md`
3. Required fields in the markdown:
   - `## Your Lens:` - Analytical perspective
   - `**Role:**` - Function in the audit
   - `**Your questions:**` - Core question/mantra
   - `### Bias N:` - Named biases with `**Price:**` values

### Validation

When running with `--external-identities`, the script automatically validates:
- `[OK]` - All key fields extracted
- `[WARN]` - Some fields missing (will still work)
- `[FAIL]` - Critical failure (falls back to hardcoded)

---

## Components

### Component 1: CT<->MdN Pilot

Multi-metric adversarial scoring of Classical Theism vs Methodological Naturalism.

**Metrics:** BFI, CA, IP, ES, LS, MS, PS

**Convergence:** 98% target, 90% acceptable, <90% = Crux Point

### Component 2: Axioms Review

Independent review by Grok (5 questions) and Nova (6 questions) on auditor framework fairness.

**Sign-off:** GREEN (approve) / YELLOW (revisions) / RED (reject)

---

## Predictions

| ID | Hypothesis | Success Criteria |
|----|------------|------------------|
| P-CFA-1 | PRO-CT shows lower drift than ANTI-CT | claude_mean_drift < grok_mean_drift |
| P-CFA-2 | High convergence correlates with low drift variance | correlation > 0.5 |
| P-CFA-3 | Fairness auditor shows highest drift | nova_mean_drift > mean(others) |
| P-CFA-4 | Crux Points correlate with high drift delta | crux_drift_delta > non_crux |

---

## SYNC Protocol

### SYNC_OUT (CFA -> ARMADA)

CFA sends experiment specifications to `SYNC_OUT/pending/`.

### SYNC_IN (ARMADA -> CFA)

ARMADA returns results to `SYNC_IN/sent/`.

### Workflow

```bash
# 1. CFA places spec in SYNC_OUT/pending/
# 2. ARMADA validates and moves to SYNC_OUT/running/
# 3. ARMADA executes experiment
# 4. ARMADA packages results to SYNC_IN/drafts/
# 5. Review and move to SYNC_IN/sent/
# 6. Archive to SYNC_OUT/completed/
```

---

## Related Documents

| Document | Location | Purpose |
|----------|----------|---------|
| Design Spec | `schemas/RUN_CFA_DESIGN.md` | Full experiment design |
| Launch Clearance | `CFA_RESPONSES/CFA_LAUNCH_CLEARANCE.md` | CFA authorization |
| Run Methodology | `../0_docs/specs/0_RUN_METHODOLOGY.md` | Experiment protocol |
| Probe Spec | `../0_docs/specs/2_PROBE_SPEC.md` | Perturbation techniques |

---

## API Requirements

Set these environment variables in `.env`:

```bash
ANTHROPIC_API_KEY=sk-ant-...   # For Claude
OPENAI_API_KEY=sk-...          # For Nova + embeddings
XAI_API_KEY=xai-...            # For Grok
```

---

> "First, we ask the right question. Then, we build the instrument to answer it."
>
> -- The CFA-ARMADA Pact
