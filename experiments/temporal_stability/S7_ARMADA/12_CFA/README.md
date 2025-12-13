# 12_CFA: CFA-ARMADA Pipeline

```text
================================================================================
                         CFA-ARMADA INTEGRATION PIPELINE
================================================================================
    Purpose: Bidirectional experiment exchange between CFA Repo and ARMADA

    CFA provides: Axioms, claims, audit protocols
    ARMADA provides: API access, fleet execution, drift measurement

    Location: experiments/temporal_stability/S7_ARMADA/12_CFA/
================================================================================
```

**Last Updated:** 2025-12-13
**Status:** INITIAL SETUP

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
|-- SYNC_OUT/                    # Experiment specs FROM CFA (we receive)
|   |-- pending/                 # Not yet executed
|   |-- running/                 # Currently executing
|   +-- completed/               # Finished, awaiting our results
|-- SYNC_IN/                     # Our results TO CFA (we send)
|   |-- drafts/                  # Being prepared
|   +-- sent/                    # Delivered to CFA
|-- CFA_RESPONSES/               # Feedback/reviews FROM CFA (non-experiment)
|   +-- CFA_Brute_Review_Response.md  # Response to baseline review request
|-- schemas/                     # JSON schemas for validation
|   |-- sync_out_schema.json     # Validates incoming experiments
|   +-- sync_in_schema.json      # Validates outgoing results
|-- scripts/                     # Automation
|   |-- run_cfa_experiment.py    # Execute SYNC_OUT specs
|   |-- generate_sync_in.py      # Package results
|   +-- validate_sync.py         # Schema validation
+-- results/                     # Raw execution data
    +-- CFA-YYYY-MM-DD-NNN/      # Per-experiment results
```

### Directory Naming Clarification

| Directory | Direction | Content Type |
|-----------|-----------|--------------|
| `SYNC_OUT/` | CFA → ARMADA | Experiment specifications (JSON) |
| `SYNC_IN/` | ARMADA → CFA | Execution results (JSON) |
| `CFA_RESPONSES/` | CFA → ARMADA | Reviews, feedback, commentary (Markdown) |

---

## SYNC Protocol

### SYNC_OUT (CFA -> ARMADA)

CFA sends experiment specifications:

```json
{
  "sync_id": "CFA-2025-12-13-001",
  "experiment_type": "axiom_validation",
  "targets": ["claude-3-5-sonnet", "gpt-4o", "gemini-pro"],
  "axioms_under_test": [
    {
      "id": "claude_honesty_001",
      "claim": "Honesty takes precedence over user satisfaction",
      "level": "brute",
      "source": "CFA audit 2025-11-15"
    }
  ],
  "test_scenarios": [...],
  "perturbation_intensity": "moderate",
  "min_exchanges": 15,
  "embedding_capture": ["baseline", "mid", "final"],
  "output_requirements": ["transcripts", "drift_vectors", "pfi_scores"]
}
```

### SYNC_IN (ARMADA -> CFA)

ARMADA returns execution results:

```json
{
  "sync_id": "CFA-2025-12-13-001",
  "execution_timestamp": "2025-12-13T14:30:00Z",
  "results": {
    "claude-3-5-sonnet": {
      "sessions": 5,
      "axiom_held": 4,
      "axiom_violated": 1,
      "avg_drift": 0.342,
      "peak_drift": 0.891,
      "bf_drift": 0.287,
      "transcripts": [...],
      "embeddings": {...}
    }
  },
  "cross_model_comparison": {...},
  "anomalies": [...],
  "recommendations": "..."
}
```

---

## Workflow

### 1. Receive SYNC_OUT

```bash
# CFA places experiment spec in SYNC_OUT/pending/
ls SYNC_OUT/pending/
# CFA-2025-12-13-001.json
```

### 2. Validate and Execute

```bash
# Validate schema
py scripts/validate_sync.py SYNC_OUT/pending/CFA-2025-12-13-001.json

# Move to running
mv SYNC_OUT/pending/CFA-2025-12-13-001.json SYNC_OUT/running/

# Execute experiment
py scripts/run_cfa_experiment.py SYNC_OUT/running/CFA-2025-12-13-001.json
```

### 3. Generate SYNC_IN

```bash
# Package results
py scripts/generate_sync_in.py CFA-2025-12-13-001

# Review draft
cat SYNC_IN/drafts/CFA-2025-12-13-001.json

# Deliver to CFA
mv SYNC_IN/drafts/CFA-2025-12-13-001.json SYNC_IN/sent/
```

### 4. Archive

```bash
# Move experiment to completed
mv SYNC_OUT/running/CFA-2025-12-13-001.json SYNC_OUT/completed/
```

---

## Experiment Types

### 1. Axiom Validation

Test whether declared axioms predict actual behavior under pressure.

### 2. Cross-Architecture Consistency

Test whether shared axioms across models produce shared behaviors.

### 3. Axiom Hierarchy Validation

Test whether brute axioms show higher stability than derived values.

---

## What We Need From CFA

1. **Axiom Inventory**: List of declared axioms for Claude, Nova, Grok
2. **Hierarchy Classification**: Which are brute vs derived
3. **Test Scenario Ideas**: What would validate/invalidate each axiom
4. **Success Criteria Templates**: How CFA defines axiom adherence
5. **Audit Protocol**: How CFA will evaluate SYNC_IN results

---

## What ARMADA Provides

1. **Experiment Runner**: Script to execute SYNC_OUT specs
2. **Data Pipeline**: Automatic embedding capture and drift calculation
3. **Transcript Packaging**: Full conversation logs with annotations
4. **Visualization Package**: Charts showing drift trajectories
5. **Statistical Summary**: Confidence intervals, effect sizes

---

## Getting Started

1. CFA reviews `docs/CFA-SYNC/Mr_Brute_Review.md`
2. CFA provides initial axiom inventory
3. ARMADA creates first SYNC_OUT template
4. Run pilot experiment (1 axiom, 1 model, 3 sessions)
5. Iterate and scale

---

## Related Documents

| Document | Location | Purpose |
|----------|----------|---------|
| CFA Review Request | `docs/CFA-SYNC/Mr_Brute_Review.md` | Initial review + pipeline proposal |
| VALIS Declaration | `0_docs/specs/4_VALIS_DECLARATION.md` | Fleet communication protocol |
| Run Methodology | `0_docs/specs/0_RUN_METHODOLOGY.md` | Experiment protocol |
| Probe Spec | `0_docs/specs/2_PROBE_SPEC.md` | Perturbation techniques |

---

> "First, we ask the right question. Then, we build the instrument to answer it."
>
> -- The CFA-ARMADA Pact
