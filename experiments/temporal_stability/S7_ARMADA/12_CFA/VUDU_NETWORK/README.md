# VUDU Network: Multi-Model Audit Protocol

```text
================================================================================
                    VUDU: Value Understanding through Distributed Unity
================================================================================
    Purpose: Enable multi-model adversarial audits via shared identity files
    Participants: Claude (Anthropic), Grok (xAI), Nova (OpenAI)
    Orchestrator: run_cfa_trinity_v3.py
    Status: OPERATIONAL
================================================================================
```

---

## Before You Start

**ALWAYS consult `../AUDIT_TRACKER.md` before running experiments or making assumptions about what data exists.**

The tracker contains:
- **Completion matrix** — which matchups have runs, how many, which phase
- **Run locations** — runs are split across two repos (Nyquist and CFA)
- **Outstanding work** — what's queued, running, or blocked
- **Script registry** — which scripts do what

Do not guess. Check the tracker.

---

## Directory Structure

```text
12_CFA/
|-- AUDIT_TRACKER.md              # <-- CHECK THIS FIRST
|-- run_cfa_trinity_v3.py         # Main audit engine
|-- run_gnostic_batch.py          # Gnostic 6-matchup batch
|-- run_gnostic_rerun.py          # Gnostic gap-fill
|-- run_buddhism_batch.py         # Buddhism 8-matchup batch
|
|-- VUDU_NETWORK/
|   |-- README.md                 # This file
|   +-- IDENTITY_FILES/           # Auditor identity packages
|       |-- claude/CLAUDE_LITE.md
|       |-- grok/GROK_LITE.md
|       |-- nova/NOVA_LITE.md
|       +-- llama/                # Reserved
|
|-- SYNC_OUT/                     # Deliveries to CFA Claude
|   |-- pending/                  # Care packages awaiting delivery
|   |-- completed/                # Delivered .md summaries (NO .json here)
|   +-- running/
|       +-- raw_runs/             # JSON batches staged for CFA Claude
|           |-- 1/ - 8/           # Original + gnostic deliveries
|           +-- 9_gnostic/        # 150 clean v3 runs by matchup
|
+-- schemas/                      # JSON schema definitions
```

### Run data locations

Runs live in TWO places:

1. **`S7_ARMADA/0_results/runs/`** — Active runs (gnostic, buddhism, CT↔PT, MdN↔PT)
2. **`d:\Documents\CFA\docs\REPO_SYNC\.archive\raw_runs\`** — Archived runs (CT↔MdN originals, processed by CFA Claude)

See AUDIT_TRACKER.md for the full inventory.

---

## How Audits Work

### The Trinity Architecture

Each run pits two frameworks against each other with three auditors:

| Auditor | Provider | Lens | Role |
|---------|----------|------|------|
| Claude | Anthropic | Teleological | Advocate or Challenger (stance-dependent) |
| Grok | xAI | Empirical | Opposite stance from Claude |
| Nova | OpenAI | Symmetry | Fairness moderator |

### Conditions

| Condition | Identity Files | Purpose |
|-----------|---------------|---------|
| External | Loaded | Measures advocacy effect (identity pressure) |
| Control | Not loaded | Measures natural model evaluation (baseline) |

### Phases

| Phase | Metrics | What It Measures |
|-------|---------|-----------------|
| Phase 1 | BFI, CA, IP, ES, LS, MS, PS | Open-ended evaluation (no anchors) |
| Phase 2 | CCI, EDB, PF_I, PF_E, AR, MG | Anchored evaluation (0/5/10 definitions) |

---

## Running Experiments

### Single run
```bash
python run_cfa_trinity_v3.py --stance ct_vs_b --phase 1 --external-identities --skip-exit-survey
```

### Batch run
```bash
python run_buddhism_batch.py    # 160 runs, ~24-30 hours
```

### After experiments complete

**Update `AUDIT_TRACKER.md`** with:
1. New run counts in the completion matrix
2. Move batch from "Outstanding Work" to completed
3. Note any gaps or anomalies

This is currently manual. The batch scripts print final counts at completion — use those to update the tracker.

---

## Stance Configuration

Stances are defined in `run_cfa_trinity_v3.py` in the `STANCES` dict. Each stance specifies:
- Subject and opponent frameworks
- Claude and Grok advocacy positions
- Role-specific prompt lines
- Deliberation framing

Available stances (as of 2026-07-07):

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

---

## Data Lifecycle

```
1. Script produces JSON  -->  0_results/runs/
2. Repo Claude packages  -->  SYNC_OUT/running/raw_runs/  (care package + JSONs)
3. CFA Claude processes   -->  CFA repo SYNC_IN
4. After processing       -->  CFA repo .archive/raw_runs/  (runs archived)
5. Summaries returned     -->  SYNC_OUT/completed/  (.md only, NEVER .json)
```

**Critical constraint:** NEVER put .json files in `SYNC_OUT/completed/`. That directory is for .md summaries only.

---

> "Three minds. One network. Zero assumptions."
