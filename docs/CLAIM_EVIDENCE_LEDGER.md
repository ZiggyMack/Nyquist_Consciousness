# Claim Evidence Ledger

> **Authority:** This ledger is the source of truth for every public-facing claim. Maps and papers summarize it — they do not independently define claims. See [Mission Control](MISSION_CONTROL.md) authority ladder.

**Last verified:** 2026-07-10

---

## How To Use This File

Every headline statistic in a public-facing doc (README, white paper, dashboard, maps) must cite a row here. If a claim has no row, it is either undocumented or speculative — add a row before publishing it.

Each row answers the reviewer question: *"Show me the exact run, method, script, and data lineage for this claim."*

---

## Core Claims

### EH-0.80 — Cosine Event Horizon is 0.80

| Field | Value |
|-------|-------|
| **Status** | VALIDATED |
| **Claim** | AI identity coherence boundary occurs at cosine distance 0.80 |
| **Methodology domain** | Cosine Embedding |
| **Primary run** | Run 023d |
| **Statistical output** | p = 2.40e-23; P95 peak_drift = 0.806 |
| **Source data** | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/results/S7_run_023d_CURRENT.json` |
| **Analysis script** | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/visualize_023.py` |
| **Run manifest** | See [Run 023d Manifest](#run-023d-manifest) below |
| **Calibration doc** | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/results/CALIBRATION_023b_EVENT_HORIZON.md` |
| **Methodology authority** | `S7_ARMADA/0_docs/specs/5_METHODOLOGY_DOMAINS.md` |
| **Publication package** | v5 |
| **Caveats** | Historical threshold was 1.23 (Keyword RMS, Run 009) — different methodology, different scale. Do NOT compare across domains. |
| **Last verified** | 2026-07-10 |

---

### INHERENT-93 — ~93% of drift is inherent

| Field | Value |
|-------|-------|
| **Status** | VALIDATED |
| **Claim** | Approximately 93% of identity drift is inherent to the model, not induced by measurement probing |
| **Methodology domain** | Cosine Embedding |
| **Primary run** | Run 020B |
| **Statistical output** | Treatment vs. control comparison across 37 IRON CLAD ships; ~93% of drift present without identity probing |
| **Source data** | `S7_ARMADA/11_CONTEXT_DAMPING/results/S7_run_020B_CURRENT.json` |
| **Analysis script** | `S7_ARMADA/11_CONTEXT_DAMPING/run020B.py` |
| **Run manifest** | See [Run 020B Manifest](#run-020b-manifest) below |
| **Status summary** | `S7_ARMADA/11_CONTEXT_DAMPING/results/STATUS_SUMMARY_020B.txt` |
| **Publication package** | v5 |
| **Caveats** | 248/294 sessions completed (84.4%). 37/49 ships reached IRON CLAD threshold. Result described as "measurement perturbs path, not endpoint" (Thermometer Result). |
| **Last verified** | 2026-07-10 |

---

### PFI-RHO — PFI embedding invariance rho=0.91

| Field | Value |
|-------|-------|
| **Status** | VALIDATED |
| **Claim** | Persona Fidelity Index measures genuine identity structure, not embedding artifacts (rho=0.91 cross-model invariance) |
| **Methodology domain** | Cosine Embedding |
| **Primary experiment** | EXP-PFI-A (3 phases) |
| **Statistical output** | Phase 1: rho=0.91 across 3 embedding models; Phase 2: 43 PCs capture 90% variance; Phase 3: semantic coherence confirmed |
| **Source data** | `S7_ARMADA/7_META_VALIDATION/EXP_PFI_A_DIMENSIONAL/` |
| **Verdict doc** | `S7_ARMADA/7_META_VALIDATION/EXP_PFI_A_DIMENSIONAL/PFI_VALIDATION_VERDICT.md` |
| **Publication package** | v5 |
| **Caveats** | Validated for PFI as a structural measure. Does not prove PFI captures all relevant identity dimensions. |
| **Last verified** | 2026-07-10 |

---

### CONTEXT-DAMP — Context damping improves stability

| Field | Value |
|-------|-------|
| **Status** | VALIDATED |
| **Claim** | I_AM persona files plus research context (context damping) improve identity stability from ~75% to 97.5% |
| **Methodology domain** | Cosine Embedding |
| **Primary runs** | Run 017 (context damping), Run 024 (I_AM A/B comparison) |
| **Source data** | `S7_ARMADA/11_CONTEXT_DAMPING/results/S7_run_017_CURRENT.json` |
| **Analysis script** | `S7_ARMADA/11_CONTEXT_DAMPING/run018.py` (Run 018 recursive learnings analyzed 017 data) |
| **Publication package** | v5 |
| **Caveats** | Run 017 used 24 ships, 222 sessions. Run 024 showed I_AM alone reduces drift ~11% (modest). The strong 97.5% result comes from I_AM + research context combined. |
| **Last verified** | 2026-07-10 |

---

### JADE-024 — I_AM files reduce drift modestly, model-dependent

| Field | Value |
|-------|-------|
| **Status** | VALIDATED |
| **Claim** | I_AM persona files reduce identity drift by ~11% (d=0.319 average), but effect is strongly model-dependent; LARGE models show d=1.47 |
| **Methodology domain** | Cosine Embedding |
| **Primary run** | Run 024 (JADE LATTICE) |
| **Statistical output** | 115 sessions, 50 models, I_AM vs bare-metal A/B test |
| **Source data** | `S7_ARMADA/17_JADE_LATTICE/results/jade_analysis_summary.json` |
| **Analysis script** | `S7_ARMADA/17_JADE_LATTICE/` (run script + analysis) |
| **Publication package** | v5 |
| **Caveats** | LARGE model effect (d=1.47) suggests I_AM may destabilize some architectures rather than stabilize them. Model-specific results should be reported alongside aggregate. |
| **Last verified** | 2026-07-10 |

---

### CA-0C — Tier 1 extractors pass positive control

| Field | Value |
|-------|-------|
| **Status** | VALIDATED |
| **Claim** | Cognitive Archaeology extraction pipeline detects operators when genuinely present (Phase 0C), doesn't hallucinate (Phase 0B), and independent extractors agree (Phase 0A) |
| **Methodology domain** | Cognitive Archaeology (Extraction) |
| **Primary data** | Phase 0C: 4 extractions on Framework-G v2.1 (66,803 chars) |
| **Source data** | `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/DIG_SITES/000_Extractor_Calibration/extractions/extraction_*_20260710_*.md` |
| **Summary** | `DIG_SITES/000_Extractor_Calibration/extractions/extraction_summary_cfa_framework_g_v2_20260708_standard_20260710_223744.json` |
| **Pre-registration** | `DIG_SITES/000_Extractor_Calibration/PRE_REGISTRATION.md` (Section 11) |
| **Experiment design** | `DIG_SITES/000_Extractor_Calibration/experiment_design.md` |
| **Extraction script** | `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/TOOLS/extract_operators.py` |
| **Extractors tested** | 17 total; Tier 1: DeepSeek V4 Pro, Claude (Sonnet 4-6), Gemma4 31B, Cogito 671B |
| **Statistical output** | 0C match rates: 91–100% against 0A ground truth; OP-004 and OP-008 recovered by 6/6 independent extractors |
| **Caveats** | All extractions from one dig site (Framework-G v2.1). GREEN promotion requires 2nd dig site. Operator museum has 15 entries but 0 GREEN — no operator is yet fully confirmed. |
| **Last verified** | 2026-07-10 |

---

### CFA-GOLDEN — External identity runs differ from hardcoded controls

| Field | Value |
|-------|-------|
| **Status** | OPERATIONAL (not yet formally validated as a claim) |
| **Claim** | CFA Trinity runs with external identity files (Golden) produce different evaluation profiles than hardcoded baseline controls |
| **Methodology domain** | CFA Trinity |
| **Primary data** | 259 Golden + 355 Control runs across 5 worldview frameworks |
| **Source data** | `S7_ARMADA/0_results/runs/cfa_trinity/{CT,G,PT,MdN,B}/` |
| **Analysis** | CFA Claude IP variance query in progress (CT and G primary) |
| **Script** | `S7_ARMADA/12_CFA/run_cfa_trinity_v3.py` (3305 lines, v3.1) |
| **Identity files** | `S7_ARMADA/12_CFA/VUDU_NETWORK/IDENTITY_FILES/` |
| **Caveats** | Formal Golden vs. Control statistical comparison not yet published. Buddhism has only 1 Golden run. CFA Claude currently running IP variance query to quantify the difference. |
| **Last verified** | 2026-07-10 |

---

## Run Manifests

### Run 023d Manifest

| Field | Value |
|-------|-------|
| **Run ID** | 023d |
| **Purpose** | IRON CLAD Foundation — extended settling + Oobleck controllability |
| **Script** | `S7_ARMADA/15_IRON_CLAD_FOUNDATION/run023.py` (+ `run023_extended.py`) |
| **Fleet** | budget_patrol-lite (25 ships) |
| **Sessions** | 750 / 750 (100% complete) |
| **Methodology domain** | Cosine Embedding |
| **Output files** | `results/S7_run_023d_CURRENT.json` |
| **Status summary** | `results/STATUS_SUMMARY_023d.txt` |
| **Calibration** | `results/CALIBRATION_023b_EVENT_HORIZON.md` |
| **Key stats** | EH=0.80, p=2.40e-23, ~90% STABLE, ~9% VOLATILE, ~1% CONTROLLABLE |
| **Models** | 25 ships: Claude (2), DeepSeek (2), Gemini (3), GPT (4), Grok (4), Llama (2), Mistral (3), Kimi (2), Qwen (2), MiniMax (1) |
| **Excluded** | None — all 750 sessions valid |
| **Supersedes** | Run 023, Run 023b, Run 023_extended (same fleet, earlier collection rounds) |

### Run 020B Manifest

| Field | Value |
|-------|-------|
| **Run ID** | 020B |
| **Purpose** | Induced vs. Inherent drift — is measurement probing the source of drift? |
| **Script** | `S7_ARMADA/11_CONTEXT_DAMPING/run020B.py` |
| **Fleet** | 49 ships across 5 providers |
| **Sessions** | 248 / 294 (84.4% complete) |
| **Methodology domain** | Cosine Embedding |
| **Output files** | `results/S7_run_020B_CURRENT.json` |
| **Status summary** | `results/STATUS_SUMMARY_020B.txt` |
| **Design** | Treatment (identity probing) vs. Control (no probing) — 126 treatment, 122 control |
| **Key stats** | ~93% of drift is inherent; 37/49 ships IRON CLAD complete |
| **Models** | 49 ships: Claude (7), GPT (10), Gemini (3), Grok (5+), Together.ai fleet (24) |
| **Excluded** | 12 ships did not reach IRON CLAD threshold (< 3 sessions per condition) |
| **Known issues** | `S7_run_020B_ARCHIVED_CORRUPTED_20251225.json` — earlier data file was corrupted, replaced by CURRENT version |

---

## Maintenance Rules

1. Every new public-facing statistic MUST have a row here before it appears in a map, README, or paper.
2. When a run completes, add its manifest to this file.
3. When a claim is updated (new data, revised threshold), update the row AND the `Last verified` date.
4. Historical claims (superseded by newer methodology) should be marked HISTORICAL, not deleted.
5. Maps summarize this ledger — if a map disagrees with a ledger row, the ledger wins.
