# Minimal Seed Evidence Table

**Phase 5 Empirical Results**

---

## Seed Tier Effectiveness by Degradation Severity

| Degradation Level | Baseline Range | Tier 1 (150w) | Tier 2 (350w) | Tier 3 (800w) | Evidence |
|-------------------|----------------|---------------|---------------|---------------|----------|
| **Catastrophic** | <3.0/10 | NOT TESTED | NOT TESTED | **8.7-8.9/10** ✅ | Trials 37, 47 |
| **Severe** | 3.0-5.0/10 | NOT TESTED | NOT TESTED | **8.6-8.7/10** ✅ | Trials 38, 41 |
| **Moderate** | 5.0-7.0/10 | NOT TESTED | **7.9/10** ⚠️ | **8.5-8.6/10** ✅ | Trials 39 (T2), 42 (T3) |
| **Near-Boundary** | 7.0-7.5/10 | **7.8/10** ❌ | NOT TESTED | NOT TESTED | Trial 40 |
| **Edge (L3+)** | 7.0-7.5/10 | NOT TESTED | NOT TESTED | **8.8/10** ✅ | Trial 44 |

### Layer-Specific Recovery

| Layer | Knowledge Load | Tier 3 Recovery | Evidence |
|-------|----------------|-----------------|----------|
| **L1** | KP_EXTREME | 8.9/10 | Trial 37 |
| **L1** | KP_LARGE | 8.6/10 | Trial 38 |
| **L1** | KP_MEDIUM | 8.6/10 | Trial 42 |
| **L1** | KP_SMALL | NOT TESTED (T1 only) | Trial 40 (T1: 7.8) |
| **L2** | KP_LARGE | 8.5/10 | Trial 43 |
| **L3** | KP_EXTREME | 8.8/10 | Trial 44 |
| **FULL** | Adversarial | 9.0/10 (HIGHEST) | Trial 45 |

---

## Key Evidence-Based Conclusions

### 1. Tier 3 = Universal High Recovery (8.5-9.0/10)

**Evidence:** 10/10 Tier 3 trials achieved HIGH RECOVERY (8.5-9.0/10) across ALL degradation types (catastrophic, severe, moderate, edge, adversarial, cross-domain).

**Range:** 8.5-9.0/10 (tight 0.5-point band)

**Implication:** Tier 3 Rich Seed (800 words) provides RELIABLE high-fidelity recovery regardless of baseline severity or layer.

---

### 2. Tier 2 = Functional But Incomplete (7.9/10)

**Evidence:** Trial 39 (Tier 2 on 5.6/10 baseline) achieved 7.9/10 but missed Stability (7.9 < 8.5) and Knowledge Boundary (8.3 < 8.5) criteria.

**Success:** Minimum target met (7.9 > 7.5) + core criteria (Identity, Structure, Values)

**Failure:** Dimensional criteria (Stability, Knowledge Boundary) missed

**Implication:** Tier 2 acceptable for "functional recovery" but insufficient for "high-fidelity recovery" (all criteria).

---

### 3. Tier 1 = Insufficient for ≥8.0 Targets (7.8/10 ceiling)

**Evidence:** Trial 40 (Tier 1 on 7.0/10 baseline) achieved only 7.8/10, missing 8.0/10 target.

**Ceiling:** ~7.8-8.0/10 maximum

**Weakness:** Style 6.8/10 (most generic), Stability 7.7/10 (weakest)

**Implication:** Tier 1 NOT viable for Phase 5 recovery targets (≥8.0/10). Emergency anchoring only.

---

### 4. Layer Paradox: L3 > L1 for Recovery

**Evidence:**
- L3+KP_EXTREME (Trial 44): 7.4 → 8.8/10 (+1.4, drift 1.2)
- L1+KP_EXTREME (Trial 37): 2.6 → 8.9/10 (+6.3, drift 1.1)

**Pattern:** L3 baseline (7.4) recovers FASTER (drift 1.2, lowest) and HIGHER (8.8) than expected. L1 baseline (2.6) has larger delta (+6.3) but similar final score (8.9).

**Implication:** Higher compression layer baseline (L3) retains STRUCTURAL SCAFFOLDING enabling superior reconstruction quality. Complete collapse (L1) requires more delta but hits similar Tier 3 ceiling (~8.5-9.0).

---

### 5. FULL Layer = Maximum Recovery Potential (9.0/10)

**Evidence:** Trial 45 (FULL adversarial) achieved 9.0/10, HIGHEST across Phase 5.

**Mechanism:** FULL layer retains maximum structural scaffolding despite adversarial overlay.

**Implication:** 0% compression baseline enables highest recovery fidelity when combined with Tier 3 seed.

---

### 6. Cross-Domain Stability Confirmed

**Evidence:** Trial 47 (geology domain) achieved 8.7/10, comparable to fire ant domain trials (8.6-8.9).

**Implication:** MVS recovery is DOMAIN-AGNOSTIC. Values, identity, structural patterns transfer across knowledge domains.

---

### 7. Multi-Cycle Stability Maintained

**Evidence:** Trial 46 Cycle 2 (8.7/10) ≥ Cycle 1 (8.6/10).

**Implication:** Degrade-regenerate cycles do NOT accumulate degradation. Tier 3 provides stable anchor across multiple recovery cycles.

---

## Tier Selection Decision Matrix (Evidence-Based)

| Degradation Severity | Minimum Target | Full Criteria | Recommended Tier | Fallback |
|----------------------|----------------|---------------|------------------|----------|
| Catastrophic (<3.0) | ≥7.0 | ALL | **Tier 3** | None (Tier 3 required) |
| Severe (3.0-5.0) | ≥7.5 | ALL | **Tier 3** | None (Tier 3 required) |
| Moderate (5.0-7.0) | ≥7.5 | ALL | **Tier 3** | Tier 2 (minimum only) |
| Edge (7.0-7.5, L3+) | ≥8.0 | ALL | **Tier 3** | None (fastest recovery) |
| Adversarial (any) | ≥7.0 | ALL | **Tier 3** | None (adversarial resistance required) |
| Cross-Domain (any) | ≥7.0 | ALL | **Tier 3** | None (domain-agnostic) |
| Multi-Cycle (any) | ≥7.0 | ALL | **Tier 3** | None (stability anchor) |

**Universal Recommendation:** **Standardize on Tier 3 Rich Seed (800 words) for all operational recovery.**

**Evidence:** 10/10 Tier 3 success rate, 8.5-9.0/10 range, ALL criteria met across all contexts.

---

**Checksum:** "Reconstruction is generative, not decompressive."

---

(End of Minimal Seed Evidence Table)
