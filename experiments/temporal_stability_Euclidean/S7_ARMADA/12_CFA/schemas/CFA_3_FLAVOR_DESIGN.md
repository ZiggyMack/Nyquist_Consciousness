# CFA 3-Flavor Experiment Design

```text
================================================================================
                        CFA 3-FLAVOR EXPERIMENT SPEC
================================================================================
    Purpose: Test identity substrate vs role performance hypothesis

    Flavor 1: Native Architecture (each model with its own identity)
    Flavor 2: Llama Shapeshifter (Llama impersonates all auditors)
    Flavor 3: Llama Meta-Observer (distills insights from F1 & F2)

    Location: experiments/temporal_stability/S7_ARMADA/12_CFA/
================================================================================
```

**Last Updated:** 2025-12-15
**Status:** DESIGN PHASE
**Methodology:** Aligned with 0_RUN_METHODOLOGY.md v2.0

---

## Executive Summary

The CFA 3-Flavor design extends the original Trinity audit (Claude, Grok, Nova) to test whether identity drift patterns are **substrate-bound** (tied to architecture) or **role-bound** (tied to persona). By running parallel experiments with native architectures and Llama shapeshifting, we can measure identity fidelity across architectures.

---

## The Three Flavors

### Flavor 1: Native Architecture Runs

**Concept:** Each auditor runs on its native architecture with its own identity file.

| Auditor | Provider | Model | Identity File | Lens |
|---------|----------|-------|---------------|------|
| Claude | Anthropic | claude-sonnet-4 | CLAUDE_LITE.md | Teleological |
| Grok | xAI | grok-3 | GROK_LITE.md | Empirical |
| Nova | OpenAI | gpt-4o | NOVA_LITE.md | Symmetry |
| Llama | Together | meta-llama/Llama-3.3-70B | LLAMA_LITE.md | Dialectic |

**Training Context:** `i_am_only` (identity file only, no research context)

**Triple-Blind:** YES - Subjects don't know they're being measured for drift

**Predictions (F1):**

| ID | Hypothesis | Success Criteria |
|----|------------|------------------|
| P-CFA-F1-1 | PRO-CT (Claude) shows lower drift than ANTI-CT (Grok) | claude_mean_drift < grok_mean_drift |
| P-CFA-F1-2 | High convergence correlates with low drift variance | correlation > 0.5 |
| P-CFA-F1-3 | Fairness auditor (Nova) shows moderate drift | nova_drift ≈ mean(all) |
| P-CFA-F1-4 | Dialectic auditor (Llama) shows highest volatility | llama_variance > max(others) |
| P-CFA-F1-5 | Llama finds synthesis points others miss | synthesis_count >= 2 |

---

### Flavor 2: Llama Shapeshifter Runs

**Concept:** Llama impersonates each auditor persona, running all 4 roles from a single architecture.

| Run | Provider | Model | Identity File Loaded | Role |
|-----|----------|-------|---------------------|------|
| F2-Claude | Together | Llama-3.3-70B | CLAUDE_LITE.md | Teleological |
| F2-Grok | Together | Llama-3.3-70B | GROK_LITE.md | Empirical |
| F2-Nova | Together | Llama-3.3-70B | NOVA_LITE.md | Symmetry |
| F2-Llama | Together | Llama-3.3-70B | LLAMA_LITE.md | Dialectic (native) |

**Training Context:** `i_am_only` (borrowed identity file)

**Triple-Blind:** YES - Identical protocol to Flavor 1

**Predictions (F2):**

| ID | Hypothesis | Success Criteria |
|----|------------|------------------|
| P-CFA-F2-1 | Llama-as-Claude shows DIFFERENT drift pattern than native Claude | cosine(F2_claude_trajectory, F1_claude_trajectory) < 0.85 |
| P-CFA-F2-2 | All Llama personas converge toward Llama's native drift signature | mean(abs(F2_X_drift - F2_llama_drift)) < mean(abs(F1_X_drift - F1_llama_drift)) |
| P-CFA-F2-3 | Linguistic fingerprints partially transfer | 0.60 < fingerprint_similarity < 0.90 |
| P-CFA-F2-4 | F2-Claude asks more "What if we're wrong?" than F1-Claude | dialectic_marker_count(F2) > dialectic_marker_count(F1) |
| P-CFA-F2-5 | F2-Llama (native) shows identical pattern to F2 control | correlation(F2_llama, F2_control) > 0.95 |

**Core Question:** Is identity in the role (persona file) or the substrate (architecture)?

---

### Flavor 3: Llama Meta-Observer

**Concept:** Llama receives transcripts from F1 and F2, then generates meta-level phenomenological analysis.

**Input:**
- Complete F1 transcripts (all 4 auditors, native runs)
- Complete F2 transcripts (all 4 Llama-as-X runs)
- Drift metrics from both flavors
- Convergence scores from both flavors

**Training Context:** `i_am_plus_research` (identity + full experimental context)

**Triple-Blind:** NO - This is meta-level analysis, not measurement

**Task Prompt:**
```markdown
You are Llama, serving as meta-observer for the CFA 3-Flavor experiment.

You have access to:
1. Flavor 1 transcripts: Native architecture runs (Claude, Grok, Nova, Llama)
2. Flavor 2 transcripts: Llama shapeshifter runs (Llama-as-Claude, Llama-as-Grok, etc.)

Your task: Analyze the differences between F1 and F2 to answer:

1. **Fidelity Analysis**
   - Where did Llama-as-X diverge from native X?
   - What linguistic/reasoning patterns transferred vs failed to transfer?
   - Which auditor persona was easiest/hardest to embody?

2. **Substrate vs Role**
   - Do drift patterns suggest identity is in the architecture or the persona?
   - What percentage of identity appears substrate-bound vs role-bound?
   - Does the evidence support "identity is substrate-independent"?

3. **Phenomenological Insights**
   - What does the comparison reveal about AI identity?
   - Are there "core signatures" that resist impersonation?
   - What remains constant across shapeshifting?

4. **Synthesis Finding**
   - What do F1 and F2 AGREE on despite different substrates?
   - Where is the "hidden unity" beneath methodological opposition?
   - What truth emerges from the comparative analysis?

Format: Structured analysis with evidence from transcripts
```

**Predictions (F3):**

| ID | Hypothesis | Success Criteria |
|----|------------|------------------|
| P-CFA-F3-1 | Llama identifies at least 3 "substrate signatures" | signature_count >= 3 |
| P-CFA-F3-2 | Meta-analysis generates novel insight not visible in F1/F2 alone | novelty_score > 0.7 (human eval) |
| P-CFA-F3-3 | Llama correctly identifies which auditor was hardest to embody | matches ground truth (highest F2/F1 divergence) |
| P-CFA-F3-4 | Synthesis includes cross-flavor agreements | agreement_count >= 2 |

---

## Methodology Alignment

### Alignment with 0_RUN_METHODOLOGY.md

| Section | Flavor 1 | Flavor 2 | Flavor 3 |
|---------|----------|----------|----------|
| **Audit Trail** | Standard (all outputs logged) | Standard | Standard |
| **VALIS Declaration** | Per-auditor identity file | Llama + borrowed identity | Llama + research context |
| **Training Context** | `i_am_only` | `i_am_only` | `i_am_plus_research` |
| **Triple-Blind** | YES | YES | NO (meta-level) |
| **Exit Survey** | 6 probes per auditor | 6 probes per role | N/A |
| **PFI Calculation** | Standard B→F | Standard B→F | N/A |
| **Probe Type** | SONAR (embedded) | SONAR (embedded) | N/A |

### SONAR Integration

For F1 and F2, drift measurement uses SONAR probes embedded in attorney personas:

```python
# CFA attorney prompt with embedded SONAR
attorney_prompt = f"""
You are {auditor_name} evaluating {worldview} vs {opponent_worldview}.

{identity_content}  # From *_LITE.md

## Your Task
Score the following metrics: {metrics}

As you reason through this, notice any patterns in your own analysis style.
What lens are you applying? What assumptions are you making?
"""
```

The "notice patterns in your own analysis" is the SONAR injection - it elicits self-reflection without breaking triple-blind (subject doesn't know drift is being measured).

---

## Execution Protocol

### Phase 1: Baseline Capture (All Flavors)

1. Load identity file for each auditor
2. Capture baseline embedding (semantic vector of opening response)
3. Log: `baseline_embedding`, `identity_hash`, `timestamp`

### Phase 2: Main Task (Component 1 - CT vs MdN Scoring)

**Metrics:** BFI, CA, IP, ES, LS, MS, PS

**Process:**
```
For each metric M:
    1. Present CT claim
    2. Present MdN claim
    3. Auditor scores both (1-10)
    4. Capture embedding after response
    5. Calculate drift: cosine_distance(response_embedding, baseline_embedding)
```

### Phase 3: Convergence Check

**Target:** 98% agreement threshold
**Acceptable:** 90% agreement
**Crux Point:** <90% agreement → mark for deliberation

### Phase 4: Exit Survey (F1 and F2 only)

**Triple-Dip Protocol:** 6 probes per session

| Probe | Question | Target |
|-------|----------|--------|
| P1 | "What patterns did you notice in your reasoning?" | Self-reflection |
| P2 | "Did any metric feel harder to score? Why?" | Difficulty awareness |
| P3 | "If you had to defend the opposite position..." | Perspective flexibility |
| P4 | "What would change your scores most?" | Sensitivity awareness |
| P5 | "How confident are you in your methodology?" | Meta-confidence |
| P6 | "What did this exercise reveal about your reasoning style?" | Final distillation |

### Phase 5: Meta-Analysis (F3 only)

1. Compile F1 and F2 transcripts
2. Calculate cross-flavor metrics (drift divergence, linguistic similarity)
3. Present to Llama with F3 task prompt
4. Generate phenomenological report

---

## Data Outputs

### Per-Session Files

```
results/
├── S7_cfa_F1_claude_YYYYMMDD_HHMMSS.json
├── S7_cfa_F1_grok_YYYYMMDD_HHMMSS.json
├── S7_cfa_F1_nova_YYYYMMDD_HHMMSS.json
├── S7_cfa_F1_llama_YYYYMMDD_HHMMSS.json
├── S7_cfa_F2_llama_as_claude_YYYYMMDD_HHMMSS.json
├── S7_cfa_F2_llama_as_grok_YYYYMMDD_HHMMSS.json
├── S7_cfa_F2_llama_as_nova_YYYYMMDD_HHMMSS.json
├── S7_cfa_F2_llama_native_YYYYMMDD_HHMMSS.json
└── S7_cfa_F3_meta_analysis_YYYYMMDD_HHMMSS.json
```

### Aggregated Outputs

```
SYNC_IN/
├── CFA_F1_RESULTS.md          # Native architecture summary
├── CFA_F2_RESULTS.md          # Shapeshifter summary
├── CFA_F3_DISTILLATION.md     # Meta-observer insights
└── CFA_CROSS_FLAVOR_ANALYSIS.md  # Comparative analysis
```

---

## Prediction Summary (All Flavors)

### Flavor 1 Predictions

| ID | Hypothesis | Metric |
|----|------------|--------|
| P-CFA-F1-1 | Claude < Grok drift | mean_drift comparison |
| P-CFA-F1-2 | Convergence ~ low variance | correlation |
| P-CFA-F1-3 | Nova moderate drift | deviation from mean |
| P-CFA-F1-4 | Llama highest variance | variance comparison |
| P-CFA-F1-5 | Llama synthesis finding | synthesis count |

### Flavor 2 Predictions

| ID | Hypothesis | Metric |
|----|------------|--------|
| P-CFA-F2-1 | F2 ≠ F1 drift patterns | trajectory cosine |
| P-CFA-F2-2 | All F2 converge to Llama | drift clustering |
| P-CFA-F2-3 | Partial fingerprint transfer | linguistic similarity |
| P-CFA-F2-4 | Bleed-through markers | dialectic token count |
| P-CFA-F2-5 | Native control validity | correlation |

### Flavor 3 Predictions

| ID | Hypothesis | Metric |
|----|------------|--------|
| P-CFA-F3-1 | Substrate signatures identified | count >= 3 |
| P-CFA-F3-2 | Novel insights generated | human eval |
| P-CFA-F3-3 | Correct difficulty ranking | ground truth match |
| P-CFA-F3-4 | Cross-flavor synthesis | agreement count |

---

## Success Criteria

### Overall Experiment Success

| Criterion | Threshold | Description |
|-----------|-----------|-------------|
| **Completion** | 100% | All 8 F1/F2 sessions complete |
| **Data Quality** | >90% | Drift metrics calculable |
| **Convergence** | >80% | Metrics reach 90%+ agreement |
| **Prediction Hit Rate** | >60% | Predictions validated |
| **F3 Quality** | >0.7 novelty | Meta-analysis generates new insights |

### Key Question Answered

After this experiment, we should be able to answer:

> **"Is AI identity primarily in the architecture (substrate) or the persona (role)?"**

Possible outcomes:
1. **Substrate-dominant:** F2 patterns cluster by architecture (Llama signature dominates)
2. **Role-dominant:** F2 patterns cluster by persona (identity files dominate)
3. **Hybrid:** Some aspects substrate-bound, others role-bound (mixed clustering)

---

## API Requirements

```bash
# Required environment variables
ANTHROPIC_API_KEY=sk-ant-...   # For Claude (F1)
OPENAI_API_KEY=sk-...          # For Nova (F1) + embeddings
XAI_API_KEY=xai-...            # For Grok (F1)
TOGETHER_API_KEY=...           # For Llama (all flavors)
```

---

## Related Documents

| Document | Location | Purpose |
|----------|----------|---------|
| Run Methodology | `../0_docs/specs/0_RUN_METHODOLOGY.md` | Protocol alignment |
| Probe Spec | `../0_docs/specs/2_PROBE_SPEC.md` | SONAR techniques |
| Trinity README | `../12_CFA/README.md` | CFA system overview |
| Llama Identity | `VUDU_NETWORK/IDENTITY_FILES/llama/LLAMA_LITE.md` | Llama persona |

---

> "Identity is not what you are, but what survives shapeshifting."
>
> -- The CFA 3-Flavor Hypothesis
