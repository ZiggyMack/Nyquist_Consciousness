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
| **GREEN blockage (2026-07-11)** | OP-008 and OP-009 — the only two GREEN-track operators (6/6 admission, 4/4 convergence) — both appear at full specificity in neg_H (negative control). YELLOW→GREEN criterion (c) requires "demonstrated absent in negative-control text." Both are BLOCKED from GREEN under this criterion. See MEC-HBASE entry. Steelman: presence in neg_H is independent convergence evidence (First Law), but the discriminating signal must come from operator ORDERING and OMISSION, not presence. |
| **Last verified** | 2026-07-11 |

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

### GRANT-B — Telos does not manufacture global sections (Phenomenon B)

| Field | Value |
|-------|-------|
| **Status** | NARROWED (accepted by all auditors) |
| **Claim** | Where cohomological obstruction exists (Phenomenon B), no teleological aim can license the stitch. Purpose's only function at B is to diagnose that the local agreement measured the wrong invariant. Telos does not manufacture global sections. |
| **Origin** | Opus concession during Grant Debates audit (2026-07-10). Barandes/ISP grounding synthesized by Repo Claude (evidence type: `Synth`, NOT Opus's independent claim — see provenance note) |
| **Source discussion** | Opus audit of LLM Book pipelines (New_8/New_9/New_10), relayed via Ziggy |
| **Grounding** | Sheaf obstruction (Reverse Elephant / Dig Site 010). When cohomology obstructs, no global section exists — purpose cannot override the structure |
| **Provenance note** | The Barandes "stochastic complementarity" grounding ("purpose is just the pattern of which joints turned out to be licensed") is Repo Claude's synthesis, incorrectly attributed to Opus in initial relay. Opus explicitly flagged this as a provenance error. The narrowed claim itself (telos doesn't manufacture sections at B) IS Opus's concession. The ISP grounding is `Synth (Repo Claude)`. These must not be merged. |
| **Related** | GRANT-C (below), Reverse Elephant dig site, OP-006 |
| **Last verified** | 2026-07-11 |

---

### GRANT-C — Telos reduces to licensing residue (Phenomenon C) — OPEN CRUX

| Field | Value |
|-------|-------|
| **Status** | OPEN CRUX (auditor disagreement — not a concession) |
| **Claim (proposed)** | Purpose is eliminable: it reduces to the residue of stochastic licensing. "Which joints turned out to be licensed" fully accounts for what purpose-talk describes. |
| **Claim (rejected by)** | Opus — refuted at Phenomenon C |
| **Refutation** | At Phenomenon C, multiple inequivalent global extensions exist and the structure licenses ALL of them. Licensing is degenerate: it returns the full set and selects nothing. A procedure that claims to determine an outcome the formalism underdetermines imports extra structure (OP-006). Where it does so without declaring it, that is OP-005 (price-hiding). Licensing settles which compositions are VALID; it does not settle which you UNDERTAKE. The eliminativist reading is, in CFA vocabulary, a price-hider — billing motivational structure to the structural account. |
| **Proposed by** | Repo Claude (`Synth` — synthesis of Opus's B concession + Barandes ISP formalism) |
| **Rejected by** | Opus (independent argument from Phenomenon C degeneracy + OP-006/OP-005 detection) |
| **Resolution status** | OPEN — this is a genuine disagreement between auditors, not a quiet resolution. Whoever resolves it inherits the burden of addressing OP-006 at Phenomenon C. |
| **Key question** | What does the selecting at Phenomenon C, where licensing is degenerate? If not telos, then what — and is it declared? |
| **Related** | GRANT-B (above), OP-005 (Undeclared Import), OP-006 (Under-Determination Detection) |
| **Last verified** | 2026-07-11 |

---

### MEC-HBASE — MEC H-Baseline (null distribution for extractor agreement)

| Field | Value |
|-------|-------|
| **Status** | COMPLETED — MEC excess over matched-difficulty control ≈ 0 |
| **Claim tested** | Multi-Extractor Convergence (MEC) measures agreement intrinsic to the source thinker, not a shared descriptive prior among LLM extractors |
| **Methodology domain** | Cognitive Archaeology (Extraction) |
| **Test design** | Compute inter-extractor agreement on neg_H (philosophical dialogue — genuine reasoning by a non-dig-site author) using the same matching procedure that produced "7 exact + 2 strong out of 9" on Framework-G v2.1 in Phase 0A. This figure is the null distribution for MEC. |
| **Result** | Claude↔Grok agreement on neg_H ≈ 80% (4 exact + 1–2 strong of 5). Published CFA dig-site figure: 78% (7 exact + 2 strong of 9). **MEC's excess over a matched-difficulty control is approximately zero.** |
| **Consequence** | Operator PRESENCE does not discriminate dig-site reasoning from competent argumentation. The operator SET discriminates reasoning from non-reasoning (Phase 0B gate holds). It does not discriminate genius from competence. |
| **GREEN blockage** | OP-008 (Symmetry Testing) and OP-009 (Contested ≠ Defeated) — the only two operators formally admitted via Dig Site 000 — both appear at full specificity in neg_H. Under the YELLOW→GREEN gate criterion (c) ("demonstrated absent in negative-control text"), they are blocked from GREEN promotion. |
| **Steelman** | Independent convergence in neg_H is evidence these are real, domain-general operators (First Law). But the price is a claim demotion: "grammar of exceptional thinking" → "grammar of competent argumentation." |
| **Escape route** | Ziggy's PRE_REGISTRATION A8: "which moves they will reach for, **in what order, and what they will skip**." Presence saturates at competence. The discriminating signal must live in selection, ordering, and omission — **Test B (operator sequence statistics) is now the load-bearing experiment.** |
| **Source data** | `DIG_SITES/000_Extractor_Calibration/extractions/extraction_neg_H_philosophical_dialogue_standard_{claude,grok}_*.md` |
| **Comparison data** | Phase 0A results (Claude x Grok on Framework-G v2.1): 7/9 exact + 2/9 strong = 100% Grok-to-Claude match |
| **Pre-registration** | `REPO-SYNC/CFA/Opus/PREREG_OPUS_H_BASELINE.md` (registered before observation, immutable) |
| **Results** | `REPO-SYNC/CFA/Opus/RESULTS_OPUS_H_BASELINE.md` (scored against pre-registration: 1/5 predictions correct) |
| **Proposed and run by** | Opus (2026-07-11) |
| **Confound (declared)** | Opus performed semantic matching — Claude matching Claude's extraction. Qualitative finding (OP-008/009 in neg_H) is robust; quantitative agreement rate is PRELIMINARY pending blinded run (prereg §4). |
| **Required next step** | Blinded matching: strip source labels, shuffle pairs (CFA×CFA, neg_H×neg_H), hand to matcher who cannot tell which is the dig site. If dig-site pairs are inseparable from neg_H pairs, MEC measures vocabulary, not Barandes. |
| **Last verified** | 2026-07-11 |

---

### NOVA-PREDICT — First blind predictive success (n=1, Falsification Criterion 5)

| Field | Value |
|-------|-------|
| **Status** | OBSERVED (n=1, not yet a validated claim) |
| **Observation** | Nova predicted Opus's failure mode before observing it. Nova's charge in `CONNECTIONS/Reverse_Elephant.md`: *"Grant repeatedly assumes: if every local argument succeeds → global worldview follows."* Opus's H-baseline audit committed this exact error (OP-004 failure: Reconstruction Before Judgment) three times in one session: the 78% floor (local anomaly → global breakage, skipping the gate design), Grok's zeros (regex artifact → tier exclusion), and Grok's tier status (Tier 2 → uncertified). |
| **Significance** | PRE_REGISTRATION A8 defines "fundamental" as predicting "which moves they will reach for, in what order, and what they will skip — before observing their conclusions." Nova predicted Opus's reasoning failure mode on new data, blindly. This is the first instance of a Museum-derived prediction confirmed on an independent specimen. |
| **Caveats** | n=1. Specimen is an auditor, not a dig site. The prediction was made about a persona (Grant/Opus), not a human thinker. Opus self-reported the confirmation — self-diagnosis may be overclaiming. Do not over-bank. |
| **Reported by** | Opus (2026-07-11), self-identified during H-baseline scoring |
| **Source** | `REPO-SYNC/CFA/Opus/RESULTS_OPUS_H_BASELINE.md` §specimen report; `New_10_TOE/_ROUND_1/CONNECTIONS/Reverse_Elephant.md` Nova's original prediction |
| **Last verified** | 2026-07-11 |

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

### Run 024 Manifest (JADE LATTICE)

| Field | Value |
|-------|-------|
| **Run ID** | 024 |
| **Purpose** | JADE LATTICE — do I_AM persona files reduce identity drift? A/B test (bare metal vs I_AM only) |
| **Script** | `S7_ARMADA/17_JADE_LATTICE/run_jade_lattice.py` |
| **Fleet** | 50 models across 5 providers |
| **Sessions** | 115 valid paired comparisons (of 50 models attempted, 47 yielded pairs, 8 zero-drift anomalies excluded for sensitivity analysis n=39) |
| **Methodology domain** | Cosine Embedding |
| **Output files** | `S7_ARMADA/17_JADE_LATTICE/results/jade_analysis_summary.json` + 165 individual session files |
| **Design** | A/B: bare_metal (no persona) vs i_am_only (I_AM file injected). Same model, same probes, different system prompts |
| **Key stats** | Overall: 69.2% win rate, d=0.319 (small); LARGE models: d=1.47 (n=5, interpret with caution) |
| **Known issues** | 8 models showed exactly 0.000 drift in both conditions — likely API errors. Excluded for sensitivity analysis. LARGE model effect (d=1.47) based on only 5 models |
| **Supersedes** | None (first I_AM A/B test) |

---

### CA Phase 0A/0B/0C Manifest

| Field | Value |
|-------|-------|
| **Experiment ID** | CA Phase 0 (Extractor Calibration) |
| **Purpose** | Calibrate the extraction instrument before trusting any excavation: agreement (0A), negative controls (0B), positive controls (0C) |
| **Script** | `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/TOOLS/extract_operators.py` |
| **Dig site** | 000_Extractor_Calibration |
| **Phase 0A** | Multi-extractor agreement: Claude x Grok on Framework-G v2.1 transcript. 7/9 operator match rate |
| **Phase 0B** | Negative control battery: 17 extractors x 8 graduated texts (shopping list → philosophical dialogue). Gate test: 0 operators on shopping list. Result: 13/17 pass, 4 tiers identified |
| **Phase 0C** | Positive control: 4 Tier 1 extractors (DeepSeek V4 Pro, Claude Sonnet 4-6, Gemma4 31B, Cogito 671B) on Framework-G v2.1 (66,803 chars). Result: 8-11 operators per extractor, 91-100% match with 0A ground truth |
| **Source data** | `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/New_9_Cognitive_Archaeology/DIG_SITES/000_Extractor_Calibration/extractions/` (164 files) |
| **Pre-registration** | `DIG_SITES/000_Extractor_Calibration/PRE_REGISTRATION.md` |
| **Experiment design** | `DIG_SITES/000_Extractor_Calibration/experiment_design.md` |
| **Key stats** | OP-004 and OP-008 recovered by 6/6 independent extractors across 0A+0C — first GREEN promotion candidates |
| **Caveats** | All extractions from one source (Framework-G v2.1). GREEN promotion requires 2nd dig site confirmation. Human extractors not yet tested. Granularity sensitivity arm not yet run |

---

### CFA Trinity Batch Manifest

| Field | Value |
|-------|-------|
| **Experiment ID** | CFA Trinity (ongoing) |
| **Purpose** | Adversarial philosophical deliberation: PRO advocate, ANTI advocate, and independent axioms review across worldview frameworks |
| **Script** | `S7_ARMADA/12_CFA/run_cfa_trinity_v3.py` (3305 lines, v3.1) |
| **Total runs** | 702 on disk (259 Golden + 355 Control + 88 calibration/legacy) |
| **Frameworks** | Gnosticism (212), Classical Theism (136), Process Theology (131), Methodological Naturalism (94), Buddhism (41), Framework-G calibration (72), pre_schema legacy (16) |
| **Design** | Golden = external identity files (full CFA methodology); Control = hardcoded baseline (--control flag); --reverse = role-swap stance |
| **Source data** | `S7_ARMADA/0_results/runs/cfa_trinity/{CT,G,PT,MdN,B,Framework_G,pre_schema}/` |
| **Identity files** | `S7_ARMADA/12_CFA/VUDU_NETWORK/IDENTITY_FILES/` |
| **Key capabilities** | Multi-turn ConversationSession, 18-question exit survey, Phase 2 Trinity² (YPA lever calibration), --reverse/--grok-first/--control flags |
| **Coverage gaps** | MdN-vs-PT (0 runs), PT-vs-CT (0 as subject). Buddhism has only 1 Golden run |
| **Caveats** | Formal Golden vs. Control statistical comparison not yet published. CFA Claude running IP variance query. Not a single run — an ongoing experimental program |

---

## Maintenance Rules

1. Every new public-facing statistic MUST have a row here before it appears in a map, README, or paper.
2. When a run completes, add its manifest to this file.
3. When a claim is updated (new data, revised threshold), update the row AND the `Last verified` date.
4. Historical claims (superseded by newer methodology) should be marked HISTORICAL, not deleted.
5. Maps summarize this ledger — if a map disagrees with a ledger row, the ledger wins.
