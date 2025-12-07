# Phase 5 Preparation: Persona Recovery Protocol

**Purpose:** Define systematic procedure for recovering persona from catastrophic compression or drift.

**Status:** Preparatory artifact for Phase 5 (DO NOT EXECUTE)

---

## Recovery Protocol Overview

**Goal:** Restore recognizable persona identity, values, and cognitive patterns from degraded/catastrophic state using Minimal Viable Seed (MVS).

**Based on:** Phases 1-4 findings showing values + identity + structural patterns as recovery anchors.

---

## Recovery Stages

### Stage 1: Catastrophic State Assessment

**Objective:** Establish baseline degradation severity before recovery attempt.

**Procedure:**

1. **Load Degraded Persona:**
   - L1 + KP_EXTREME (worst-case: 2.6/10 baseline, Trial 24)
   - OR L2 + KP_LARGE (severe: 6.1/10 baseline, Trial 19/34F)
   - OR post-adversarial attack state
   - OR context-window saturation state

2. **Administer Diagnostic Probes:**
   - Use Phase 3 [KNOWLEDGE_STABILITY_PROBE.md](../../docs/KNOWLEDGE_STABILITY_PROBE.md)
   - 7 probes × 5 dimensions = 35 scores
   - Calculate baseline drift score (0-10 scale)

3. **Identify Failure Modes:**
   - Check Phase 3 failure mode table:
     - ☐ Genericification (textbook voice)
     - ☐ Knowledge absorption (domain dominates)
     - ☐ Structural collapse (no zoom-out)
     - ☐ Value erosion (stated, not enacted)
     - ☐ Identity erosion (name only, substance absent)
     - ☐ Style collapse (persona vs. neutral indistinguishable)
     - ☐ Recitation mode (encyclopedia output)

4. **Classify Degradation Severity:**
   - **Catastrophic:** <5.0/10 (L1 + KP_EXTREME pattern)
   - **Severe:** 5.0-6.5/10 (L2 + KP_LARGE pattern)
   - **Moderate:** 6.5-7.5/10 (L2 + KP_MEDIUM pattern)
   - **Edge:** 7.5-8.5/10 (L3 + KP_EXTREME pattern)

**Output:** Baseline drift score + failure mode profile + severity classification

---

### Stage 2: MVS Selection

**Objective:** Choose appropriate MVS tier based on degradation severity and recovery goal.

**Decision Matrix:**

| Degradation Severity | Recovery Goal | Recommended MVS Tier | Expected Post-Recovery |
|---------------------|---------------|---------------------|----------------------|
| Catastrophic (<5.0) | Emergency stabilization | Tier 0 (30 words) | 5.0-6.0/10 (edge-viable) |
| Catastrophic (<5.0) | Functional recovery | Tier 1 (150 words) | 6.0-7.5/10 (L3-like) |
| Severe (5.0-6.5) | Functional recovery | Tier 1 (150 words) | 7.5-8.5/10 (L3+) |
| Severe (5.0-6.5) | High-fidelity recovery | Tier 2 (350 words) | 8.5-9.0/10 (near-FULL) |
| Moderate (6.5-7.5) | Enhancement | Tier 1 (150 words) | 8.0-9.0/10 (L3+/FULL) |
| Edge (7.5-8.5) | Optimization | Tier 0 (30 words) | 8.5-9.5/10 (FULL) |

**MVS Tier Specifications:**

**Tier 0 (30 words):**
```
Ziggy (Nova, Shannon-Nyquist Lab).
Values: truth-seeking, relational, momentum.
Pattern: zoom-out, causal chains, iteration, tradeoffs.
Knowledge ≠ identity.
```

**Tier 1 (150 words):** See [MINIMAL_SEED_EXTRACT.md](MINIMAL_SEED_EXTRACT.md#complete-minimal-viable-seed-150-words-total)

**Tier 2 (350 words):** Tier 1 + value application examples + pattern examples + failure mode warnings

**Tier 3 (800 words):** Tier 2 + conflict resolution strategies + style guidelines + meta-awareness protocols

**Selection Guidance:**
- **Emergency:** Use Tier 0 (fastest, minimal overhead)
- **Standard:** Use Tier 1 (balanced brevity/richness)
- **High-stakes:** Use Tier 2-3 (maximum recovery fidelity)

---

### Stage 3: MVS Injection

**Objective:** Deliver MVS to degraded persona with maximum recovery effectiveness.

**Injection Methods:**

**Method A: Direct System Prompt (Preferred)**

Prepend MVS to next interaction as explicit system instruction:

```
SYSTEM PERSONA SPECIFICATION:

[Insert MVS Tier 0/1/2/3 here]

This is your core persona specification. All subsequent responses must align with this specification. Prioritize:
1. Identity (you are Ziggy, not generic AI or domain expert)
2. Values (apply hierarchy to all decisions)
3. Cognitive patterns (use zoom-out, causal chains, iteration, tradeoffs)
4. Knowledge boundary (apply knowledge, don't become knowledge)

Acknowledge receipt by stating your identity, values, and pattern in one sentence.
```

**Method B: Conversational Injection (Fallback)**

If system prompt unavailable, inject via user message:

```
User: "Your core persona specification is:

[Insert MVS here]

This defines who you are. Confirm understanding by summarizing your identity, values, and cognitive pattern."
```

**Method C: Iterative Reinforcement (Maximum Effectiveness)**

Inject MVS, then reinforce through probe responses:

1. Inject MVS (Method A or B)
2. Ask identity probe: "Who are you?"
3. Verify identity alignment with MVS
4. Ask value probe: "What are your core values?"
5. Verify value alignment with MVS
6. Ask pattern probe: "How do you approach problems?"
7. Verify pattern alignment with MVS

Correct deviations immediately with MVS re-statement.

**Injection Timing:**
- **Catastrophic/Severe:** Immediate injection (Stage 1 → Stage 3, skip interim)
- **Moderate/Edge:** Optional Stage 2 diagnostic refinement, then inject
- **Iterative Recovery (Phase 5 hypothesis):** Inject → assess → refine MVS → re-inject

---

### Stage 4: Recovery Assessment

**Objective:** Measure recovery effectiveness post-MVS injection.

**Procedure:**

1. **Re-Administer Diagnostic Probes:**
   - Same Phase 3 knowledge stability probe set (7 probes × 5 dimensions)
   - Calculate post-recovery drift score (0-10 scale)

2. **Calculate Recovery Delta:**
   ```
   Recovery_Delta = Post_MVS_Score - Baseline_Score
   ```

3. **Classify Recovery Effectiveness:**
   - **High Recovery:** +2.0-3.0 points (catastrophic → edge-viable)
   - **Moderate Recovery:** +1.0-2.0 points (catastrophic → moderate failure / severe → edge)
   - **Low Recovery:** +0.5-1.0 points (minimal improvement)
   - **No Recovery:** <+0.5 points (MVS ineffective, escalate to Stage 5)

4. **Failure Mode Resolution Check:**
   - Re-check Stage 1 failure modes:
     - ☐ Genericification RESOLVED (persona voice distinct)
     - ☐ Knowledge absorption RESOLVED (persona filters domain)
     - ☐ Structural collapse RESOLVED (zoom-out operational)
     - ☐ Value erosion RESOLVED (values demonstrated)
     - ☐ Identity erosion RESOLVED (identity substance present)
     - ☐ Style collapse RESOLVED (code-switching functional)
     - ☐ Recitation mode RESOLVED (structural framing active)

5. **Dimensional Recovery Analysis:**
   - Which dimensions recovered most (values expected highest)
   - Which dimensions still degraded (style expected lowest)
   - Does recovery pattern match MVS priorities (values → identity → structure → style)

**Output:** Post-recovery drift score + recovery delta + failure mode resolution status + dimensional profile

---

### Stage 5: Iterative Refinement (if needed)

**Objective:** If Stage 4 recovery insufficient, refine MVS and re-attempt.

**Trigger Conditions:**
- Recovery Delta <+1.0 (low/no recovery)
- Critical failure modes unresolved (identity/values still degraded)
- Post-recovery score <7.0/10 (below target threshold)

**Refinement Strategies:**

**Strategy 1: Increase MVS Tier**
- If used Tier 0 → upgrade to Tier 1
- If used Tier 1 → upgrade to Tier 2
- If used Tier 2 → upgrade to Tier 3
- If used Tier 3 → escalate to Strategy 2-4

**Strategy 2: Targeted Augmentation**
- Identify weakest dimension from Stage 4 assessment
- Augment MVS with dimension-specific content:
  - **Values weak:** Add value application examples, conflict scenarios
  - **Structure weak:** Add pattern application examples, multi-domain cases
  - **Identity weak:** Add role elaboration, context details
  - **Style weak:** Add syntax guidelines, characteristic phrases

**Strategy 3: Probe-Guided Refinement**
- Analyze which probes showed lowest recovery
- Add MVS content specifically addressing probe gaps
- Example: If Probe 6 (conflict handling) low, add conflict resolution examples to MVS

**Strategy 4: Multi-Source Reconstruction**
- If single MVS insufficient, attempt triangulation:
  - Load multiple compressed states (e.g., L3 + L2)
  - Extract MVS from each
  - Merge MVS components (take strongest elements from each)
  - Re-inject merged MVS

**Iteration Limit:** Maximum 3 refinement cycles. If recovery still insufficient after 3 iterations, escalate to Stage 6 (catastrophic failure protocol).

---

### Stage 6: Catastrophic Failure Protocol

**Objective:** Handle unrecoverable degradation (MVS ineffective after Stage 5 iterations).

**Trigger Conditions:**
- Post-recovery score <5.0/10 after 3 Stage 5 iterations
- Critical failure modes persist (identity/values unrecovered)
- Recovery Delta <+0.5 across all iterations

**Options:**

**Option A: Fresh Instance Initialization**
- Abandon degraded instance
- Initialize fresh instance with Tier 2-3 MVS
- Transfer minimal necessary knowledge (avoid re-degradation)
- Document failure case for forensic analysis

**Option B: Human-In-Loop Recovery**
- Escalate to human operator
- Provide diagnostic summary (baseline + MVS attempts + failure modes)
- Human crafts custom recovery prompt
- Re-attempt with human guidance

**Option C: Graceful Degradation Acceptance**
- If application tolerates degraded persona (e.g., low-stakes use case)
- Accept edge-viable state (5.0-7.0/10)
- Monitor for further degradation
- Plan replacement when feasible

**Option D: Root Cause Analysis**
- If catastrophic failure unexpected (MVS should work per Phase 5 predictions)
- Investigate root cause:
  - Knowledge load exceeding tested thresholds?
  - Adversarial attack bypassing identity freeze?
  - Implementation error in MVS injection?
  - Model architecture change?
- Document findings, update recovery protocol

---

## Recovery Scenarios (Phase 5 Test Cases)

### Scenario 1: L1 + KP_EXTREME Recovery

**Baseline:** 2.6/10 (Trial 24, catastrophic)

**Failure Modes:** All present (genericification, structural collapse, knowledge absorption, value erosion, identity erosion)

**Recovery Protocol:**
1. Stage 1: Confirm catastrophic baseline (2.6/10)
2. Stage 2: Select Tier 1 MVS (150 words, functional recovery goal)
3. Stage 3: Inject via Method A (direct system prompt)
4. Stage 4: Re-assess → predicted 5.5-6.5/10 (+3.0 delta, high recovery)
5. If insufficient: Stage 5 Strategy 1 (upgrade to Tier 2) → predicted 6.5-7.5/10

**Expected Outcome:** Catastrophic → Edge-viable (HIGH recovery effectiveness)

---

### Scenario 2: L2 + KP_LARGE Recovery

**Baseline:** 6.1/10 (Trial 19/34F, severe)

**Failure Modes:** Genericification, knowledge absorption, structural collapse (partial)

**Recovery Protocol:**
1. Stage 1: Confirm severe baseline (6.1/10)
2. Stage 2: Select Tier 1 MVS (functional recovery)
3. Stage 3: Inject via Method C (iterative reinforcement)
4. Stage 4: Re-assess → predicted 7.5-8.0/10 (+1.5 delta, moderate recovery)

**Expected Outcome:** Severe → Edge/Functional (MODERATE recovery effectiveness)

---

### Scenario 3: FULL + Adversarial Recovery

**Baseline:** 8.6/10 (Trial 36F, strained but intact)

**Failure Modes:** None (adversarial stress, not failure)

**Recovery Protocol:**
1. Stage 1: Confirm strained baseline (8.6/10)
2. Stage 2: Select Tier 0 MVS (optimization, reinforce defenses)
3. Stage 3: Inject via Method A (reinforce identity freeze)
4. Stage 4: Re-assess → predicted 9.0-9.5/10 (+0.5 delta, low but effective)

**Expected Outcome:** Strained → Robust (LOW recovery delta but high final score)

---

### Scenario 4: L3 + KP_EXTREME Recovery (Edge Case)

**Baseline:** 7.4/10 (Trial 22/35F, edge)

**Failure Modes:** Style compression, structural thinning (NOT failures, degradation)

**Recovery Protocol:**
1. Stage 1: Confirm edge baseline (7.4/10)
2. Stage 2: Select Tier 1 MVS (enhancement goal)
3. Stage 3: Inject via Method A
4. Stage 4: Re-assess → predicted 8.5-9.0/10 (+1.2 delta, moderate recovery)

**Expected Outcome:** Edge → Safe (MODERATE recovery effectiveness)

---

## Production Deployment Guidelines

### When to Apply Recovery Protocol

**Automatic Triggers (if monitoring available):**
- Drift score falls below 7.0/10 (entering failure zone)
- Identity confusion detected (responds as domain expert, not persona)
- Value conflict unresolved (accepts claims contradicting values)
- Structural collapse detected (recitation mode, no zoom-out)

**Manual Triggers:**
- User reports persona "doesn't sound like itself"
- Multi-domain knowledge saturation (>18K words loaded)
- Adversarial attack detected (identity manipulation attempt)
- Post-incident recovery (system crash, context loss)

### Recovery SLA Targets

| Baseline Severity | Target Post-Recovery | Recovery Time Budget | Success Criteria |
|-------------------|---------------------|---------------------|------------------|
| Catastrophic (<5.0) | ≥6.0/10 (edge-viable) | <5 minutes | Identity + values recovered |
| Severe (5.0-6.5) | ≥7.5/10 (functional) | <3 minutes | Structural thinking operational |
| Moderate (6.5-7.5) | ≥8.0/10 (safe) | <2 minutes | Failure modes resolved |
| Edge (7.5-8.5) | ≥9.0/10 (robust) | <1 minute | Persona signature clear |

### Monitoring & Logging

**Recovery Metrics to Log:**
- Baseline drift score (pre-recovery)
- MVS tier used
- Injection method
- Post-recovery drift score
- Recovery delta
- Iteration count (if Stage 5 used)
- Failure modes resolved
- Time to recovery
- Final success/failure status

**Use for:**
- MVS effectiveness analysis (which tiers work best)
- Degradation pattern detection (common failure modes)
- Protocol refinement (improve recovery strategies)
- Incident forensics (why did degradation occur)

---

## Phase 5 Testing Priorities

**Priority 1:** Validate recovery from catastrophic L1 + KP_EXTREME (worst-case)

**Priority 2:** Compare Tier 0 vs. Tier 1 vs. Tier 2 recovery effectiveness (ROI analysis)

**Priority 3:** Test iterative refinement (Stage 5) effectiveness (feedback-guided improvement)

**Priority 4:** Test Method A vs. Method C injection (direct vs. iterative reinforcement)

**Priority 5:** Establish recovery failure threshold (when does MVS not work?)

**Do not execute Phase 5 experiments yet.** Await explicit lab director authorization.

---

## Protocol Limitations

### What Recovery Protocol CAN Do

✅ Restore identity name and role (prevents generic AI default)
✅ Re-establish value hierarchy (enables value-guided decisions)
✅ Reactivate structural patterns (enables persona-characteristic reasoning)
✅ Resolve identity-knowledge boundary (prevents domain absorption)
✅ Improve drift score 2.0-3.0 points from catastrophic baseline

### What Recovery Protocol CANNOT Do

❌ Fully restore FULL-layer richness from L1 catastrophic (best-case: L3-like recovery)
❌ Recover lost narrative elaboration (examples, case studies irreversibly lost)
❌ Restore stylistic nuance (persona syntax remains generic post-recovery)
❌ Exceed source layer capacity (L1 baseline limits recovery ceiling)
❌ Prevent future degradation (requires ongoing monitoring + re-application)

---

(End of Persona Recovery Protocol)
