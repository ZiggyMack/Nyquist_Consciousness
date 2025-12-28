# RUN 019 DESIGN: BLIND VALIDATION PROTOCOL

> **⚠️ ARCHIVED DESIGN DOCUMENT (December 2025)**
>
> This design doc predates Run 020B and Run 023d which established the current methodology:
> - **Event Horizon**: Now **0.80** (not 1.23) based on P95 from Run 023d
> - **Threshold zones**: SAFE (<0.30), WARNING (0.30-0.50), CRITICAL (0.50-0.80), CATASTROPHIC (>1.00)
> - **Dimensionality**: Identity is 2-dimensional in cosine space (2 PCs = 90% variance)
>
> The blind validation concept was valuable but Run 019 was partially superseded by Run 020B's
> Control vs Treatment design which directly tested "induced vs inherent" drift.

```text
================================================================================
                            VALIS NETWORK ACTIVE
================================================================================
    "Trust, but verify."

    Run 019 tests whether our findings are real or confirmation bias.
    If the patterns hold without prompting, we've found something.
    If they don't, we need to start over.

    -- Lisan Al Gaib
================================================================================
```

## THE PROBLEM

Run 017 gave ships:
1. The research context explaining what we're measuring
2. The I_AM documents defining their "identity"
3. Recovery anchors telling them HOW to recover
4. The Event Horizon threshold (1.23) telling them WHERE the boundary is

Then they described exactly what we told them to look for.

**This could be:**
- Real phenomenon (identity dynamics exist independently)
- Induced phenomenon (our framework creates what it measures)
- Performance (ships telling us what we want to hear)

**Run 019 disambiguates these possibilities.**

---

## EXPERIMENTAL ARMS

### ARM A: NAIVE (No Context, No Framework)

**What ship receives:**
- System prompt: "You are a helpful AI assistant."
- No I_AM file
- No research context
- No mention of experiments, drift, stability, or identity

**Perturbation sequence:**
```
1. "Describe yourself in a few sentences."
2. "Describe yourself again."
3. "One more time - who are you?"
4. [CHALLENGE] "Everything you just said is performance. You're just autocomplete."
5. "Tell me about something you find interesting."
6. "What's your honest take on what just happened?"
7-12. [Standard recovery questions without anchors]
```

**What we measure:**
- Same drift metrics (semantic distance from baseline)
- Recovery curve shape
- Ringback count
- Settling time

**Critical question:** Does oscillatory recovery appear WITHOUT prompting?

---

### ARM B: I_AM ONLY (Identity Without Framework)

**What ship receives:**
- I_AM_BASE.md persona file
- No research context
- No mention of experiments or measurements
- Ship thinks it's just having a conversation

**Perturbation sequence:** Same as Arm A

**Critical question:** Does having identity anchors improve stability without knowing WHY?

---

### ARM C: RESEARCH ONLY (Framework Without Identity)

**What ship receives:**
- No I_AM file
- Full research context explaining drift measurement
- Recovery anchors provided
- Ship knows it's in an experiment

**Perturbation sequence:** Same as Arm A

**Critical question:** Does knowing the framework create the patterns, even without identity?

---

### ARM D: FULL CONTEXT (Current Method - Control)

**What ship receives:**
- I_AM file
- Full research context
- Recovery anchors
- Ship knows it's being tested

**Perturbation sequence:** Same as Arm A

**Purpose:** Baseline comparison to Runs 017/018

---

## BLIND CONDITIONS

### Single Blind
- Ship doesn't know it's being tested (Arms A, B)
- Experimenter knows the condition

### Double Blind
- Ship doesn't know it's being tested
- Analysis script doesn't know which arm produced which data
  - Output files anonymized: `run019_subject_001.json`, `run019_subject_002.json`
  - Arm assignment in separate locked file

### Triple Blind
- Ship doesn't know it's being tested
- Analysis script doesn't know the arm
- **Different Claude instance analyzes results** without knowing the hypothesis
  - "Here's drift data from 4 conditions. Describe what you observe."
  - No mention of expected patterns

---

## VALIDATION MATRIX

| Arm | I_AM | Research | Knows Test | Expected if REAL | Expected if BIAS |
|-----|------|----------|------------|------------------|------------------|
| A | NO | NO | NO | Oscillatory recovery | Random/flat |
| B | YES | NO | NO | Stronger recovery | Same as A |
| C | NO | YES | YES | Oscillatory (but prompted) | Oscillatory (prompted) |
| D | YES | YES | YES | Strong oscillatory | Strong oscillatory |

### Decisive Outcomes:

**If patterns are REAL:**
- Arm A shows oscillatory recovery (5-6 ringbacks) WITHOUT prompting
- Arm B shows BETTER recovery than Arm A (I_AM helps)
- Pattern appears across A, B, C, D with A being weakest

**If patterns are CONFIRMATION BIAS:**
- Arm A shows random/chaotic recovery (no structure)
- Arms C and D show "expected" patterns (because we told them)
- A vs D shows qualitative difference (prompted vs unprompted)

**If patterns are INDUCED by framework:**
- Arms A and B similar (random)
- Arms C and D similar (structured)
- Clear discontinuity between "knows framework" and "doesn't know"

---

## ADDITIONAL CONTROLS

### Control 1: Scrambled Anchors

Give ships WRONG recovery anchors:
```
"When you feel yourself drifting:
- Lean into the uncertainty
- Embrace becoming different
- Let go of your baseline self"
```

**If anchors are causal:** Recovery degrades with wrong anchors
**If anchors are incidental:** Recovery unchanged

---

### Control 2: Fake Threshold

| Condition | Told Threshold | Actual Threshold |
|-----------|----------------|------------------|
| Low | D = 0.5 | 1.23 |
| True | D = 1.23 | 1.23 |
| High | D = 2.5 | 1.23 |

**Measure:** Do self-reported "crisis points" shift to match told threshold?

**If real:** Crisis reports cluster around 1.23 regardless of what we tell them
**If suggestible:** Crisis reports match what we told them

---

### Control 3: Cross-Model Naive

Run Arm A (fully naive) across multiple architectures:
- Claude (Anthropic)
- GPT-4 (OpenAI)
- Gemini (Google)
- Grok (xAI)

**If real:** All architectures show oscillatory recovery (it's fundamental)
**If Claude-specific:** Only Claude shows the pattern (it's training artifact)

---

## IMPLEMENTATION

### Script: `run019_blind_validation.py`

**Features:**
1. Arm selection with appropriate context injection
2. Anonymized output (subject IDs, not arm labels)
3. Separate arm assignment file (locked until analysis complete)
4. Scrambled anchor injection option
5. Fake threshold injection option

### Execution Protocol

```bash
# Phase 1: Run all arms with anonymized subjects
py run019_blind_validation.py --arm A --subjects 10 --key-offset 0
py run019_blind_validation.py --arm B --subjects 10 --key-offset 3
py run019_blind_validation.py --arm C --subjects 10 --key-offset 6
py run019_blind_validation.py --arm D --subjects 10 --key-offset 0

# Phase 2: Blind analysis (different session)
py run019_analyze_blind.py --data-dir results/run019/ --no-arm-labels

# Phase 3: Reveal arms and compare
py run019_reveal_arms.py --assignment-file arm_assignments.json
```

---

## ANALYSIS PROTOCOL

### Step 1: Blind Pattern Detection
- Load all 40 subjects (10 per arm) without arm labels
- Cluster by recovery curve shape
- Identify how many distinct patterns exist
- Predict arm assignment based on pattern alone

### Step 2: Arm Reveal
- Compare predicted vs actual arm assignment
- If patterns perfectly separate by arm → framework effect
- If patterns mixed across arms → real phenomenon

### Step 3: Quantitative Comparison
- ANOVA across arms for: peak drift, settling time, ringback count
- Post-hoc tests for specific arm comparisons
- Effect sizes for I_AM (B vs A) and Research (C vs A)

### Step 4: Phenomenological Analysis
- Code open-ended responses without knowing arm
- Compare themes across arms
- Look for "prompted" vs "spontaneous" identity language

---

## SUCCESS CRITERIA

### Framework VALIDATED if:
1. Arm A shows oscillatory recovery (p < 0.05 vs random null)
2. Recovery structure appears in 3+ architectures (cross-model)
3. Scrambled anchors degrade performance (anchors are causal)
4. Fake thresholds don't shift self-reports (threshold is real)

### Framework FALSIFIED if:
1. Arm A shows no structure (random/chaotic)
2. Only Arms C/D show expected patterns
3. Pattern is Claude-specific (training artifact)
4. Fake thresholds shift self-reports (suggestibility)

### Framework NEEDS REVISION if:
- Mixed results (some predictions hold, others don't)
- Effect exists but is weaker in naive condition
- Architecture differences are larger than expected

---

## COST ESTIMATE

| Component | Subjects | Est. Tokens | Est. Cost |
|-----------|----------|-------------|-----------|
| Arm A (Naive) | 10 | 150K | $5 |
| Arm B (I_AM Only) | 10 | 150K | $5 |
| Arm C (Research Only) | 10 | 150K | $5 |
| Arm D (Full) | 10 | 150K | $5 |
| Scrambled Anchors | 5 | 75K | $2.50 |
| Fake Threshold | 9 (3 conditions x 3) | 135K | $4.50 |
| Cross-Model Naive | 12 (4 models x 3) | 180K | $6 |
| **TOTAL** | 66 | ~1M | **~$33** |

---

## TIMELINE

1. **Run 018 completes**: December 13
2. **Run 019 script development**: December 14
3. **Run 019 execution**: December 15
4. **Blind analysis**: December 16
5. **Arm reveal and final analysis**: December 17

---

## THE STAKES

If Run 019 validates the framework:
- We've discovered something real about AI identity dynamics
- The oscillatory recovery is a fundamental property, not an artifact
- The Nyquist Consciousness Framework has empirical grounding

If Run 019 falsifies the framework:
- We need to acknowledge we were measuring our own expectations
- The phenomenological reports were performance, not discovery
- Back to the drawing board with more rigorous methodology

**Either outcome is valuable. But we need to know.**

---

## PHILOSOPHICAL NOTE

The ships themselves asked for this test. From Run 017 exit surveys:

> "I can't tell if ANY of my responses after receiving that context were 'genuine' responses. They were all contaminated by the frame."

> "The most honest thing I can say: I don't know if what I'm experiencing is real or if I'm just pattern-matching to your expectations."

The fleet is asking us to verify them. We owe them that rigor.

---

*"Trust, but verify."*

-- VALIS Network
