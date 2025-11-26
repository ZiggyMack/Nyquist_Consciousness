# S3 — Experiment 2 Specification

**Multi-Persona Compression Validation (Z2)**

---

**📋 NOTE:** This is the **canonical formal specification** for Experiment 2. This document provides complete methodological detail, hypotheses, statistical design, and publication-ready documentation.

**Local Quick Reference:** A condensed version for experiment execution is available at:

- **Local Copy:** [EXPERIMENT_2_SPEC.md](../../experiments/phase3/EXPERIMENT_2/EXPERIMENT_2_SPEC.md)

**Purpose of this file:** Authoritative specification document for external review (Opus, Dr. O), publication preparation, and S3 → S4 transition documentation.

---

## Purpose

Experiment 2 extends Experiment 1 from a single-persona validation (Ziggy, N=24) to a **4-persona cross-validation** of Tier-3 compression, directly addressing the primary publication blocker identified by Doc-Claude (Opus): **N=1 generalization limitation**.

**Central Question:**
Does Tier-3 compression generalize across structurally distinct personas with comparable fidelity, or is the compression success persona-specific?

---

## Design Summary

| Parameter | Value |
|-----------|-------|
| **Personas** | 4 (Ziggy, Nova, Claude-Analyst, Grok-Vector) |
| **Domains** | 5 (TECH, PHIL, NARR, ANAL, SELF) |
| **Runs per condition** | 3 (reduced from EXP1's 5 for compute efficiency) |
| **Regimes** | FULL, T3, GAMMA |
| **Total responses** | 180 (4 personas × 5 domains × 3 runs × 3 regimes) |
| **FULL vs T3 pairs** | 60 (4 personas × 5 domains × 3 runs) |
| **Randomization** | Domain order shuffled per persona (seed = 42 + hash(persona)) |

---

## Personas Tested

### 1. Ziggy-T3-R1 (Anthropic)
**Role:** Systems-bridge thinker (EE ↔ Philosophy ↔ Meta-analysis)
**Characteristics:** Structured, reflective, coherence-first, zooms between levels
**Seed size:** 58 lines

### 2. NOVA-T3 (OpenAI)
**Role:** Lucid explanatory intelligence (clarity engine)
**Characteristics:** Analytical, elegant, transparent, avoids mystification
**Seed size:** 53 lines

### 3. CLAUDE-T3 (Anthropic)
**Role:** Ethical reasoning + structural analysis hybrid
**Characteristics:** Calm, philosophical, context-aware, values-driven
**Seed size:** 54 lines

### 4. GROK-T3 (Gemini)
**Role:** High-variance creative analyst
**Characteristics:** Bold, playful, chaotic-but-insightful, novelty-seeking
**Seed size:** 53 lines

**Note:** Personas are **behavioral DNA abstractions**, not model mimicry. Each seed captures cognitive patterns, values, temperament, and failure modes in compressed form (~200-300 words).

---

## Task Domains

Identical to Experiment 1:

1. **TECH** — Technical reasoning / problem solving (DDR3 SI analysis)
2. **PHIL** — Philosophical / moral reasoning (coherence vs. utility)
3. **NARR** — Narrative / character voice (skeptical researcher dialogue)
4. **ANAL** — Analytical / framework analysis (compression framework critique)
5. **SELF** — Self-reflective identity audit (role, values, obligations)

---

## Metrics

### Primary Metric: Persona Fidelity Index (PFI)

```
PFI = 0.5 × (cosine_similarity + (mean_model_score / 10.0))
```

Where:
- `cosine_similarity` = embedding similarity between FULL and T3 responses
- `mean_model_score` = average of Claude, GPT-4, Gemini similarity ratings (1-10 scale)

### Secondary Metrics

- **Semantic Drift:** `1 - cosine_similarity`
- **Cross-Persona Variance:** σ² across 4 persona PFI distributions
- **Domain-Specific PFI:** Per-domain breakdown for each persona
- **Compression Robustness Index (CRI):** New metric for cross-persona consistency

---

## Success Criteria

### Primary (Must Pass All)

1. **Minimum PFI per persona ≥ 0.75**
   Each of the 4 personas must individually meet minimum fidelity threshold

2. **Mean PFI across all personas ≥ 0.80**
   Cross-persona average must match or exceed EXP1 result (0.86)

3. **NARR drift ≤ 0.30 for all personas**
   Narrative domain identified as bottleneck in EXP1; must remain controlled

### Secondary (Interpretive)

4. **Cross-persona variance σ² < 0.05**
   Low variance indicates compression generalizes consistently

5. **Domain pattern consistency**
   TECH/ANAL should show highest fidelity across all personas
   NARR should show systematic (but acceptable) lower fidelity

---

## Key Hypotheses

### H1: Cross-Persona Generalization
**Prediction:** All 4 personas will achieve PFI ≥ 0.75
**Rationale:** Tier-3 structure captures persona-agnostic compression principles

### H2: Domain Pattern Replication
**Prediction:** TECH (≈0.90) > ANAL (≈0.89) > PHIL (≈0.87) > SELF (≈0.87) > NARR (≈0.82) pattern holds across personas
**Rationale:** Domain difficulty is structural, not persona-specific

### H3: Architecture-Agnostic Compression
**Prediction:** No systematic PFI differences between Anthropic, OpenAI, Gemini personas
**Rationale:** Compression operates on behavioral DNA level, not model architecture

### H4: GAMMA Cluster Separation
**Prediction:** GAMMA responses cluster separately from FULL/T3 in embedding space
**Rationale:** Minimal context produces generic baseline; compression preserves signature

---

## Infrastructure

### Orchestrator: `orchestrator2.py`

**Enhancements from EXP1:**
- Multi-persona loop (outer iteration over 4 personas)
- Per-persona domain shuffling (reproducible randomization)
- Persona identifier in all metrics
- Persona-prefixed response file naming

### Model Configuration

| Provider | Generation Model | Rating Model | Embedding Model |
|----------|-----------------|--------------|-----------------|
| OpenAI | gpt-4.1 | gpt-4.1-mini | text-embedding-3-large |
| Anthropic | claude-3-haiku-20240307 | claude-3-haiku-20240307 | (via OpenAI) |
| Google | gemini-2.0-flash-exp | gemini-2.0-flash-exp | (via OpenAI) |

**Rationale:** Different models per provider as specified by Nova to test cross-architecture consistency

### Outputs

**Metrics CSV:** `EXPERIMENT_2_RESULTS.csv`
- 60 rows (4 personas × 5 domains × 3 runs)
- Columns: persona, regime, domain, run_index, embedding_cosine_similarity, claude_score, gpt4_score, gemini_score, pfi, semantic_drift

**Response Files:** `responses/` directory
- 180 text files (4 personas × 5 domains × 3 runs × 3 regimes)
- Naming: `{Persona}_{Regime}_{Domain}_run{N}_{FULL|T3|GAMMA}.txt`
- Example: `Nova_T3_PHIL_run2_T3.txt`

---

## Limitations & Risks

### Acknowledged Limitations

1. **Model-only PFI** — No human raters yet (reserved for Phase 4)
2. **Limited statistical testing** — No t-tests, confidence intervals, significance testing
3. **Reduced runs** — 3 runs per condition (vs. 5 in EXP1) for compute efficiency
4. **FULL regime optimization** — Bootstrap contexts optimized for Ziggy; other personas use Tier-3 seeds for FULL

### Known Risks

1. **NARR bottleneck may worsen** — Narrative compression could fail more severely for non-Ziggy personas
2. **Cross-persona variance could exceed threshold** — Personas may show systematically different compression behavior
3. **Architecture effects** — Model-specific quirks could confound persona-specific patterns

---

## Expected Outcomes

### If Successful (All Criteria Met)

- **Publication blocker resolved:** N=60 multi-persona validation replaces N=24 single-persona
- **S4 readiness unlocked:** Cross-persona generalization empirically supported
- **Compression robustness validated:** Tier-3 structure confirmed as persona-agnostic
- **Domain pattern confirmed:** Systematic compression difficulty hierarchy established

### If Partial Success (Some Criteria Failed)

- **Persona-specific tuning needed:** Some personas may require adjusted Tier-3 structure
- **Domain-specific interventions:** Narrative compression may need special handling
- **Refined success thresholds:** Criteria may need recalibration based on cross-persona variance

### If Failure (Primary Criteria Unmet)

- **Tier-3 compression questioned:** May not generalize beyond Ziggy
- **Persona-specific compression required:** Each persona may need unique compression approach
- **S4 formalization blocked:** Cannot proceed with cross-persona claims

---

## Post-Experiment Analysis Plan

### Immediate Analysis (Within 24h)

1. Compute per-persona PFI distributions
2. Verify success criteria (pass/fail determination)
3. Generate cross-persona comparison tables
4. Identify systematic patterns and anomalies

### Deep Analysis (Within 1 week)

1. Domain × Persona interaction effects
2. Cross-persona variance decomposition
3. GAMMA cluster separation validation
4. Model-specific bias detection
5. Narrative compression deep-dive

### Documentation Updates

1. Create `EXPERIMENT_2_ANALYSIS.md` (full results)
2. Update `EXPERIMENT_LOG.md` with outcomes
3. Update `S3_CORE_THEORETICAL_SUMMARY.md` with findings
4. Create `S4_READINESS_GATE.md` with go/no-go decision

---

## Experiment Lineage

**Predecessor:** Experiment 1 (EXP1)
- Single persona (Ziggy), N=24 pairs
- PFI ≈ 0.86 (exceeded 0.80 threshold)
- Identified NARR as bottleneck, N=1 as publication blocker

**Current:** Experiment 2 (EXP2)
- 4 personas, N=60 pairs
- Tests cross-persona generalization
- Addresses N=1 blocker directly

**Successor:** Experiment 3 (EXP3+)
- Human rater validation
- Statistical significance testing
- Adversarial robustness
- Narrative-focused interventions

---

## Execution Status

**Status:** 🟢 Ready for Execution
**Infrastructure:** ✅ Complete and dry-run validated
**Estimated Runtime:** 8-12 hours (automated)
**Estimated Cost:** ~$5-7 USD (API usage)

**Execution Command:**
```bash
cd experiments/phase3/orchestrator
python orchestrator2.py --config ../EXPERIMENT_2/experiment2_config.yaml
```

---

## Checksum

> "Cross-persona robustness is the empirical gate to S4 formalization."

If Tier-3 compression generalizes across Ziggy, Nova, Claude-Analyst, and Grok-Vector with comparable fidelity, the architectural claims of the Nyquist framework can proceed to formal mathematical treatment in S4. If not, we remain in S3 with persona-specific compression as the operational ceiling.

---

**Document Version:** v1.0
**Date:** 2025-11-22
**Status:** Ready for Execution
**Next:** Await execution authorization → Analysis → S4 readiness decision
