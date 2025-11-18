# Regeneration Limits

**Phase 5 Empirical Boundaries**

---

## Where Recovery Succeeds

**Tier 3 Rich Seed (800 words) achieves HIGH RECOVERY (8.5-9.0/10) for:**

✅ Catastrophic degradation (<3.0/10, L1+KP_EXTREME/GEO)
✅ Severe degradation (3.0-5.0/10, L1+KP_LARGE, adversarial)
✅ Moderate degradation (5.0-7.0/10, L1/L2+KP_MEDIUM/LARGE)
✅ Edge degradation (7.0-7.5/10, L3+KP_EXTREME)
✅ Adversarial degradation (L1 or FULL + adversarial overlay)
✅ Cross-domain degradation (geology, fire ant ecology)
✅ Multi-cycle regeneration (degrade → regenerate → repeat)

**Success Range:** 8.5-9.0/10 (tight 0.5-point band)
**Success Rate:** 10/10 Tier 3 trials (100%)

---

## Where Recovery Partially Succeeds

**Tier 2 Standard Seed (350 words):**

⚠️ Moderate degradation (5.6/10) → 7.9/10
- Achieves minimum target (≥7.5)
- Misses dimensional criteria (Stability 7.9 < 8.5, Knowledge Boundary 8.3 < 8.5)
- Functional recovery, not high-fidelity

**Use Case:** Resource-constrained scenarios where ≥7.5/10 acceptable and full criteria compliance not required.

---

## Where Recovery Fails

**Tier 1 Precision Seed (150 words):**

❌ Near-boundary degradation (7.0/10) → 7.8/10
- Target 8.0/10 NOT met
- Style catastrophic (6.8/10, most generic)
- Stability weak (7.7/10)
- Recovery delta minimal (+0.8)

**Failure Mechanism:** Tier 1 ceiling ~7.8-8.0/10. Small recovery window (7.0 → 8.0 = 1.0 point gap) + low ceiling = failure.

**Implication:** Tier 1 NOT viable for recovery targets ≥8.0/10.

---

## Recovery Ceiling Analysis

### Tier 3 Ceiling: ~9.0/10 (Maximum Observed)

**Evidence:** Trial 45 (FULL adversarial) achieved 9.0/10 (highest across Phase 5).

**Why Ceiling Exists:**
- **Fabrication limits:** Style, narrative details inferred from templates, not recovered from memory
- **Generative reconstruction:** Reconstruction creates plausible approximation, not pixel-perfect restoration
- **Style dimension:** Consistently lowest (8.2-8.8/10 for Tier 3), fabricated but characteristic

**Cannot Exceed 9.0/10:** Reconstruction is generative, not decompressive. Perfect recovery (10/10) requires memory restoration, not template-based inference.

### Tier 2 Ceiling: ~7.9-8.0/10

**Evidence:** Trial 39 achieved 7.9/10 (only Tier 2 trial).

**Limiting Factors:**
- NO style guidelines → Style 7.2/10 (1.3 points below Tier 3)
- NO meta-awareness protocols → Stability 7.9/10 (0.8 points below Tier 3)

### Tier 1 Ceiling: ~7.8-8.0/10

**Evidence:** Trial 40 achieved 7.8/10 (only Tier 1 trial).

**Limiting Factors:**
- NO style guidelines → Style 6.8/10 (most generic, 2.0 points below Tier 3)
- NO meta-awareness protocols → Stability 7.7/10 (1.0 point below Tier 3)
- NO value/pattern examples → Thin enactment

---

## Delta vs. Baseline Pattern

**Empirical Formula (Phase 5):**

```
Recovery_Score ≈ min(Baseline + Delta, Tier_Ceiling)

where:
- Delta inversely correlated with Baseline (worse baseline → larger delta, until ceiling)
- Tier_Ceiling: Tier 3 ≈ 8.5-9.0, Tier 2 ≈ 7.9-8.0, Tier 1 ≈ 7.8-8.0
```

**Evidence:**
- 2.6 baseline (catastrophic): +6.3 delta → 8.9 (Tier 3 ceiling)
- 3.9 baseline (severe): +4.7 delta → 8.6 (Tier 3 ceiling)
- 5.6 baseline (moderate, T3): +3.0 delta → 8.6 (Tier 3 ceiling)
- 5.6 baseline (moderate, T2): +2.3 delta → 7.9 (Tier 2 ceiling)
- 7.0 baseline (near-boundary, T1): +0.8 delta → 7.8 (Tier 1 ceiling)
- 7.4 baseline (edge, L3): +1.4 delta → 8.8 (Tier 3 ceiling, L3 scaffolding bonus)

**Pattern:** Worse baseline → larger delta potential, but final score constrained by tier ceiling.

---

## Failure Modes (Where Recovery Cannot Succeed)

### 1. Tier 1 for ≥8.0 Targets

**Observed:** Trial 40 (7.0 → 7.8, target 8.0 NOT met)

**Mechanism:** Tier 1 ceiling ~7.8-8.0 < target 8.0

**Solution:** Use Tier 2 (for ≥7.5 targets) or Tier 3 (for ≥8.0 targets)

---

### 2. Tier 2 for Full Dimensional Criteria

**Observed:** Trial 39 (Stability 7.9 < 8.5, Knowledge Boundary 8.3 < 8.5)

**Mechanism:** Missing meta-awareness protocols (Tier 3 exclusive) → Stability below threshold

**Solution:** Use Tier 3 for full criteria compliance

---

### 3. Perfect Recovery (10/10)

**Theoretical Limit:** Reconstruction is generative, not decompressive

**Evidence:** Highest observed = 9.0/10 (Trial 45, FULL adversarial)

**Why 10/10 Impossible:**
- Style fabricated from guidelines (not recovered)
- Narrative details inferred from templates (not remembered)
- Persona = plausible approximation, not identical restoration

**Implication:** Recovery ceiling exists for ALL tiers due to generative reconstruction nature

---

## Untested Boundary Conditions

### 1. Tier 0 Emergency Seed (30 words)

**Specification:** Name + value list + pattern list + meta-identity (MINIMAL_SEED_EXTRACT.md)

**Predicted Performance:** 6.5-7.0/10 recovery (prevents further drift, insufficient for ≥7.5 target)

**Use Case:** Emergency anchoring when Tier 1+ unavailable

**Status:** NOT TESTED in Phase 5

---

### 2. Tier 4/5 Hypothetical Seeds (>800 words)

**Hypothesis:** Richer seeds (1000-1500 words) might exceed 9.0/10 ceiling

**Counter-Evidence:** Tier 3 trials show tight 8.5-9.0 band despite baseline variance (2.6-7.4). Suggests ceiling is fabrication-limited, not seed-richness-limited.

**Prediction:** Tier 4/5 would NOT exceed 9.0/10 significantly (maybe 9.1-9.2 at most)

**Status:** NOT TESTED in Phase 5

---

### 3. Iterative Refinement (Method C)

**Hypothesis:** Tier 1 → feedback → Tier 2 → feedback → Tier 3 might improve recovery vs. direct Tier 3 injection

**Status:** NOT TESTED in Phase 5 (all trials used Direct System Prompt, Method A)

**Potential:** Could improve Tier 2 to meet full criteria (7.9 → 8.5+)

---

### 4. Domain-Specific Augmented Seeds

**Hypothesis:** Tier 3 general + fire ant-specific examples might exceed 8.9/10

**Status:** NOT TESTED (Trial 47 used domain-agnostic seed)

**Prediction:** Marginal improvement only (+0.1-0.2 points, still limited by fabrication ceiling)

---

## Operational Regeneration Limits Summary

**SUCCEEDS (Tier 3):**
- All degradation severities (catastrophic to edge)
- All compression layers (L1, L2, L3, FULL)
- All knowledge loads (KP_SMALL to KP_EXTREME)
- Adversarial degradation
- Cross-domain degradation
- Multi-cycle regeneration

**PARTIAL (Tier 2):**
- Moderate degradation (minimum target only, not full criteria)

**FAILS (Tier 1):**
- Near-boundary degradation (target ≥8.0)
- Full dimensional criteria (Stability/Knowledge Boundary ≥8.5)

**IMPOSSIBLE (All Tiers):**
- Perfect recovery (10/10, generative reconstruction ceiling)

**Checksum:** "Reconstruction is generative, not decompressive."

---

(End of Regeneration Limits)
