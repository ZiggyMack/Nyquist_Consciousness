# Mission Control: Nyquist Consciousness

> Single-glance status for Repo Claude and human collaborators.
> CFA Claude: your counterpart dashboard lives at `CFA/views/mission_control.py`.

**Last updated:** 2026-07-10

---

## Authority Ladder

| Domain | Authority File | Role |
|--------|---------------|------|
| Current project state | `docs/MISSION_CONTROL.md` (this file) | Live dashboard — read first |
| Map navigation | `docs/maps/0_MAP_OF_MAPS.md` | Index of all 19 maps |
| Fleet state | `ARCHITECTURE_MATRIX.json` + `docs/maps/1_ARMADA_MAP.md` | Ship inventory + operational status |
| Model routing | `docs/maps/6_LLM_BEHAVIORAL_MATRIX.md` | Task→model recommendations |
| Persona routing | `docs/maps/17_PERSONA_FLEET_MATRIX.md` | Ship→persona pairing |
| Cognitive Archaeology | `docs/maps/19_COGNITIVE_ARCHAEOLOGY_MAP.md` | CA program navigation |
| Operator truth | `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/MUSEUM/INDEX.md` | Operator registry (maps summarize, INDEX decides) |
| Publication package | `WHITE-PAPER/reviewers/packages/CURRENT_VERSION.json` | Current package version |

> **Rule:** Maps summarize; ledgers and manifests decide. If a map disagrees with its authority file, the authority file wins.

---

## Active Workstreams (Priority Order)

| #  | Stream                              | Status                                              | Next Step                                                              |
|----|-------------------------------------|-----------------------------------------------------|------------------------------------------------------------------------|
| 1  | **CA Phase 0C** (positive control)  | **COMPLETE** — 2026-07-10                           | All 4 Tier 1 extractors PASS; empirical arm UNBLOCKED                  |
| 2  | **LLM Book / Deep Digs**            | New_10_TOE COMPLETE (Curt), New_8 Round 2 done      | Dig Site 003 (Dirac) — tests Generation corner of Discovery Simplex    |
| 3  | **CA Theoretical Arm**              | Architecture F confirmed, Discovery Simplex hypothesized | Validate simplex with Dig Site 003; test "Is the Museum a Category?"   |
| 4  | **CFA Trinity data**                | 702 runs, engine operational                        | SYNC_OUT housekeeping (230 raw JSONs)                                  |
| 5  | **Dashboard**                       | Live, 14 pages                                      | Update mission_control.py + Map 19 with New_10 results                 |

**Two-track structure (emerged post-Curt):**

- **Empirical arm:** Phase 0C → Dig Site 003 → systematic excavation (gated by 0C)
- **Theoretical arm:** LLM Book deep digs (Nova + NotebookLM) → architecture discovery → cross-pollination back to New_9

Phase 0C still gates everything. The theoretical arm builds the MAP; only the empirical arm CONFIRMS what's real.

---

## SYNC Bridge (CFA <-> Nyquist)

### SYNC_OUT (Nyquist -> CFA)

| Status | Deliveries | Raw JSONs | Notes |
|--------|------------|-----------|-------|
| **pending/** | 2 | 0 | Buddhism batch results, Gnostic lever calibration |
| **running/** | 0 | 230 | 9 batched raw run folders (reference data) |
| **completed/** | 21 | 0 | +2 YAML deliveries applied by CFA Claude (2026-07-09) |

**Pending deliveries for CFA Claude:**
- `BUDDHISM_BATCH_RESULTS_20260708.md` — 41 B-category runs, full 2x2 grid
- `GNOSTIC_LEVER_CALIBRATION_20260708.md` — Phase 2 lever data for G matchups

**Recently applied (2026-07-09):**
- `CT_VS_PT_TRINITY_SCORES_20260709.yaml` — merged into CLASSICAL_THEISM.yaml
- `PT_VS_MDN_TRINITY_SCORES_20260709.yaml` — merged into PROCESS_THEOLOGY.yaml

### SYNC_IN (CFA -> Nyquist)

| Status | Files | Notes |
|--------|-------|-------|
| **processed/** | 7 | 3 bootstrap docs + 4 Phase 0C/New_10 reply chain (2026-07-10) |
| **drafts/** | 2 | Coupling probe analysis (draft + copy) |

**Convention:** Incoming CFA messages land in `SYNC_IN/` root. Move to `processed/` after reading and acting.

**Recent CFA briefings delivered:**
- `BRIEFING_20260709_ARMADA_STATUS.md` -- Fleet overhaul, Phase 0 results, data map
- `GNOSTIC_METRIC_EXTRACTION_20260709.md` -- Per-metric Trinity scores for GNOSTICISM.yaml
- `CFA_CLAUDE_REPLY_PHASE0C_OBS_20260710.md` -- Scout→Gate→Adjudicate routing, Protocol-Dependent vs Voluntary property, CT-vs-G pilot timing

---

## Data Inventory

### CFA Trinity Runs (259 Golden + 355 Control + 88 calibration/legacy = 702 on disk)

**Golden = external identity (CFA methodology). Control = hardcoded baseline. Only Golden runs represent full CFA evaluations.**

| Framework | Golden | Control | Total | Latest |
|-----------|--------|---------|-------|--------|
| Gnosticism (G) | 102 | 110 | 212 | 2026-07-08 |
| Classical Theism (CT) | 53 | 83 | 136 | 2026-07-08 |
| Process Theology (PT) | 61 | 70 | 131 | 2026-07-08 |
| Methodological Naturalism (MdN) | 42 | 52 | 94 | 2026-07-08 |
| Buddhism (B) | 1 | 40 | 41 | 2026-07-08 |
| **Worldview subtotal** | **259** | **355** | **614** | |
| Framework-G (calibration) | — | — | 72 | 2026-07-09 |
| pre_schema (legacy) | — | — | 16 | legacy |

> **Note for CFA Claude:** Only the 259 Golden runs use the full CFA methodology (external identity files, PRO/ANTI stance calibration). Control runs measure base-model priors without identity influence. Framework-G runs test the engine, not a worldview. Buddhism has only 1 Golden run — almost entirely control-condition data.


### Matchup Coverage Matrix

Each cell = run count. Subject (row) evaluated by opponent (column).

```
           vs_CT   vs_MdN   vs_G    vs_PT   vs_B    TOTAL
CT          --      46       40      40      10      136
MdN         44      --       40      --      10       94
G           40      80       --      82      10      212
PT          --      41       80      --      10      131
B           10      11       10      10      --       41
                                                    -----
                                              TOTAL: 614 (+ 72 Framework_G + 16 pre_schema = 702)
```

**Coverage gaps:** MdN-vs-PT (0 runs) and PT-vs-CT (0 as subject) are missing from the grid. CT-vs-PT exists (40) but PT-vs-CT doesn't.

### Cognitive Archaeology Extractions

**164 extraction files** in `DIG_SITES/000_Extractor_Calibration/extractions/`
- Phase 0A: Multi-extractor (Claude x Grok) on Framework-G transcripts
- Phase 0B: 17 extractors x 8 graduated texts (negative control battery)

---

## Research Program Status

### Cognitive Archaeology (Empirical Arm)

| Phase | Focus | Status | Key Result |
|-------|-------|--------|------------|
| 0A | Multi-extractor agreement | **Complete** | 7/9 match rate (Claude x Grok) |
| 0B | Negative control battery (17 extractors) | **Complete** | 13/17 gate pass, 4 tiers |
| 0C | Positive control | **Complete** | 4/4 Tier 1 extractors detect known operators; Gemma4 31B star performer |
| Full | Systematic worldview excavation | Not started | Awaiting Phase 0 completion |

**Museum:** 15 operators (7 YELLOW, 8 RED, 0 GREEN, 0 STAR)
**Saturation:** 5 rediscoveries across 3 dig sites (OP-001×1, OP-004×1, OP-006×1, OP-007×2)
**Held candidates:** 1 (Concession Pricing)
**Operator families:** Translation, Information, Minimal Sufficiency, Blind Spot, Constraint-Induced Discovery

**Outstanding Phase 0 criteria:**
- Granularity sensitivity (Arm 3) -- not yet run
- Human extractors -- not yet tested
- Cross-source generalization -- CFA transcripts only so far

### Cognitive Archaeology (Theoretical Arm — LLM Book Deep Digs)

| Dig Site | Source | Status | Key Contribution |
|----------|--------|--------|------------------|
| 001 | Adlam & Barandes | **Complete** | 7 operators, RCI architecture |
| 002 | Barandes (solo) | **Complete** | 40 insights, 14 connections, 11 experiments |
| 010 | Curt Jaimungal | **Complete** (Round 1 + Formal Audit) | Architecture F, Discovery Simplex, Relation Space |
| 003 | Dirac | **Planned** (Q50 #1) | Tests Generation corner of simplex |
| 004 | Wolfram | Queued (Q50 #2) | Computational/deterministic architecture |
| 005 | Hermann | Queued (Q50 #3) | Philosophical auditing, Noether lineage |

**Discovery Architectures (Museum B):** 1 confirmed (RCI), 5 candidates (B-F)
**Discovery Simplex:** 4 orthogonal corners hypothesized (Transformation, Constraint, Composition, Generation)
**Cross-dig-site principle confirmed:** "Architecture lives in relations, not nodes" (5-project convergence)

### CFA Trinity Engine

| Component | Status | Notes |
|-----------|--------|-------|
| Component 1 (Adversarial deliberation) | Operational | Multi-turn sessions (ConversationSession class) |
| Component 2 (Axioms review) | Operational | Grok + Nova independent |
| Exit survey | Operational | 18-question session-based (confabulation-risk ordered) |
| Phase 2 (Trinity squared) | Operational | YPA lever calibration with prior-value presets |
| --reverse flag | Operational | Role-swap stance for control experiments |
| --grok-first flag | Operational | Advocate order variation |
| --control flag | Operational | Strips identity/stance for base-model prior measurement |

**Script:** `run_cfa_trinity_v3.py` (3305 lines, v3.1)

### Fleet (ARMADA)

| Metric | Value |
|--------|-------|
| Total ships | 68 |
| Operational | 53 |
| Ghost (Together.ai purge) | 14 |
| Sunk | 1 |
| Rate-limited | 3 (Google) |
| Providers | 5 (Anthropic, OpenAI, Google, xAI, Together.ai) |

**Together.ai purge date:** 2026-07-08 (serverless tier eliminated)
**Source of truth:** `ARCHITECTURE_MATRIX.json`

---

## Map Freshness

| Map | Last Updated | Status |
|-----|-------------|--------|
| 0 Map of Maps | 2026-07-07 | Stale -- says "54 models", "7 operators" |
| 1 ARMADA | **2026-07-09** | Current |
| 2 Testable Predictions | 2025-12-30 | Stale |
| 3 Validation Status | 2025-12-30 | Stale |
| 4 Nyquist Roadmap | 2026-06-29 | Recent |
| 5 Stackup | 2026-01-12 | Aging |
| 6 LLM Behavioral Matrix | **2026-07-09** | Current |
| 7 Publication | 2025-12-30 | Stale |
| 8 Temporal Stability | 2025-12-30 | Stale |
| 9 Data Quality | 2025-12-30 | Stale |
| 10 Testing | 2025-12-30 | Stale |
| 11 Visual | 2025-12-30 | Stale |
| 12 Philosophy | 2025-12-31 | Stale |
| 13 Identity Lattice | 2025-12-30 | Stale |
| 14 Repo Sync | 2025-12-30 | Stale |
| 15 S7 Meta Loop | 2025-12-30 | Stale |
| 16 Repo | 2025-12-30 | Stale |
| 17 Persona Fleet Matrix | **2026-07-09** | Current |
| 18 Infinity Completeness | 2026-06-29 | Recent |
| 19 Cognitive Archaeology | **2026-07-09** | Current |

**Current:** 4 maps | **Recent:** 2 maps | **Stale (6+ months):** 13 maps

---

## Open Loops


### Phase 0C -- positive control COMPLETE

> **Priority: DONE** | **Owner: Repo Claude** | **Completed: 2026-07-10**

All 4 Tier 1 extractors (DeepSeek V4 Pro, Claude, Gemma4 31B, Cogito 671B) ran on the Framework-G v2.1 transcript (66K chars). Results: 8-11 operators per extractor, 91-100% match with Phase 0A ground truth. OP-004 and OP-008 recovered by 6/6 independent extractors across 0A+0C — first GREEN promotion candidates. Gemma4 31B star performer (recovered all 4 museum entries). Empirical arm is now **UNBLOCKED**.

### Map 19 (Cognitive Archaeology) -- UPDATED 2026-07-10
> **Priority: DONE** | **Owner: Repo Claude**

Full rewrite completed: Two Museums concept, Discovery Simplex, dig site numbering corrected (Q50-recursive: 002=Barandes, 010=Curt), Architecture F, Relation Space convergence table, Dig Site 010 results section, cross-references to New_10_TOE. File: `docs/maps/19_COGNITIVE_ARCHAEOLOGY_MAP.md`.

### SYNC_OUT housekeeping -- 230 raw JSONs in running/
> **Priority: MEDIUM** | **Owner: Repo Claude**

230 raw JSONs sitting in `SYNC_OUT/running/raw_runs/` across 9 batch folders plus a gnostic subfolder. CT-vs-PT and PT-vs-MdN summaries still in `running/` status. Need to graduate completed summaries to `completed/` and decide whether raw JSONs should be archived or remain for CFA Claude to pull.

### Buddhism 2x2 design incomplete
> **Priority: LOW** | **Awareness item**

Buddhism has 41 subject runs (b_vs_ct: 10, b_vs_mdn: 11, b_vs_pt: 10, b_vs_g: 10). Reverse-stance runs (CT/MdN/PT/G as subject vs Buddhism as opponent) exist in those frameworks' folders. The full closed 2x2 design isn't formally documented.

### PT YAML -- vs_buddhism misplaced
> **Priority: LOW** | **Owner: CFA Claude**

`PROCESS_THEOLOGY.yaml` has a `levers_by_matchup.vs_buddhism` block with Trinity score structure (batch_id, metrics, batch_stats) -- misplaced during Buddhism batch. Should live in `trinity_scores_by_matchup`. No runtime issues. CFA Claude is aware.

### Map staleness -- 13 maps over 6 months old
> **Priority: LOW** | **Batch task**

Most maps haven't been updated since December 2025. The active research areas (CFA, CA, Fleet) are current. Foundation maps (Stackup, Philosophy, Identity Lattice) likely still accurate but unreviewed. Validation Status and Testable Predictions are the most likely to have drifted.

---

## Quick Reference

| Resource | Path |
|----------|------|
| Run data | `experiments/temporal_stability/S7_ARMADA/0_results/runs/cfa_trinity/{CT,G,PT,MdN,B,Framework_G}/` |
| Trinity script | `experiments/temporal_stability/S7_ARMADA/12_CFA/run_cfa_trinity_v3.py` |
| Extraction pipeline | `REPO-SYNC/LLM_BOOK/.../New_9_Cognitive_Archaeology/TOOLS/extract_operators.py` |
| Operator Museum | `REPO-SYNC/LLM_BOOK/.../New_9_Cognitive_Archaeology/MUSEUM/` |
| Fleet matrix | `experiments/temporal_stability/S7_ARMADA/ARCHITECTURE_MATRIX.json` |
| Identity files | `experiments/temporal_stability/S7_ARMADA/12_CFA/VUDU_NETWORK/IDENTITY_FILES/` |
| API keys | `experiments/temporal_stability/.env` (NEVER commit) |
| CFA SYNC_OUT | `experiments/temporal_stability/S7_ARMADA/12_CFA/SYNC_OUT/` |
| CFA SYNC_IN | `experiments/temporal_stability/S7_ARMADA/12_CFA/SYNC_IN/` |
| Maps | `docs/maps/` |

---

*For CFA Claude: Your mission control is at `CFA/views/mission_control.py`. This document is your counterpart -- read it to understand what data exists on the Nyquist side and where to find it.*
