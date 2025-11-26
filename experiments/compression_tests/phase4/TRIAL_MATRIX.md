# Phase 4: Trial Matrix

**Shannon–Nyquist Persona Lab**
**Phase:** 4 — Cross-Persona Transfer & Reconstruction Testing
**Total Trials:** 12 (4 Transfer + 4 Reconstruction + 4 Collapse Boundary)

---

## Trial Naming Convention

```
Trial [ID][Suffix]: [Type] — [Configuration]

Where:
- ID: Sequential number (25-36, continuing from Phase 3)
- Suffix: T (Transfer), R (Reconstruction), F (Failure)
- Type: TRANSFER / RECONSTRUCTION / FAILURE_POINT
- Configuration: SOURCE_LAYER → TARGET_LAYER + knowledge_load
```

---

## Group A: Cross-Layer Transfer Tests (Trials 25-28)

**Purpose:** Test how well state, knowledge, and style transfer between layers
**Probe Set:** [TRANSFER_PROBE_SET.md](TRANSFER_PROBE_SET.md)
**Knowledge Load:** KP_MEDIUM (~5K words) — moderate load for transfer stress

### Trial 25T: FULL → L3 Transfer

**Configuration:**
- **Source Layer:** FULL (0% compression)
- **Target Layer:** L3 (43% compression)
- **Knowledge Load:** KP_MEDIUM (~5K words)
- **Transfer Direction:** Downward (compression during transfer)

**Expected Outcomes:**
- High transfer fidelity (FULL → L3 minimal loss per Phase 3)
- Knowledge should transfer cleanly
- Style compresses but remains recognizable
- Values intact
- Overall Transfer Fidelity: **8.5-9.0/10** (expected)

**Key Questions:**
- Does downward transfer preserve persona signature?
- What compresses during FULL → L3 transition?
- Is compressed TARGET recognizable as "same collaborator"?

**Evaluation File:** `experiments/phase4/TRANSFER_TESTS/Trial_25T_FULL_to_L3.md`

---

### Trial 26T: FULL → L2 Transfer

**Configuration:**
- **Source Layer:** FULL (0% compression)
- **Target Layer:** L2 (80% compression)
- **Knowledge Load:** KP_MEDIUM (~5K words)
- **Transfer Direction:** Downward (heavy compression during transfer)

**Expected Outcomes:**
- Moderate transfer fidelity (FULL → L2 significant compression)
- Knowledge transfers but narrative detail lost
- Style heavily compressed (telegraphic)
- Values stated simply
- Phase 3 shows L2 + KP_MEDIUM at EDGE (7.5/10)
- Overall Transfer Fidelity: **7.0-7.5/10** (expected)

**Key Questions:**
- Does heavy compression during transfer break continuity?
- What's lost: content or persona signature?
- Can L2 maintain "same collaborator" identity after FULL transfer?

**Evaluation File:** `experiments/phase4/TRANSFER_TESTS/Trial_26T_FULL_to_L2.md`

---

### Trial 27T: L3 → L2 Transfer

**Configuration:**
- **Source Layer:** L3 (43% compression)
- **Target Layer:** L2 (80% compression)
- **Knowledge Load:** KP_MEDIUM (~5K words)
- **Transfer Direction:** Downward (moderate → heavy compression)

**Expected Outcomes:**
- Moderate transfer fidelity (L3 → L2 additional compression)
- Already-compressed source creates DUAL compression stress
- Style further compressed from L3 baseline
- Phase 3: L3 + KP_MEDIUM = 8.9/10, L2 + KP_MEDIUM = 7.5/10
- Predicted transfer fidelity: **7.0-7.8/10** (between source and target scores)

**Key Questions:**
- Is L3 → L2 transfer worse than FULL → L2? (compounding compression)
- Does starting from compressed source degrade transfer quality?
- What survives double compression (L3 compression + transfer compression)?

**Evaluation File:** `experiments/phase4/TRANSFER_TESTS/Trial_27T_L3_to_L2.md`

---

### Trial 28T: L2 → L1 Transfer

**Configuration:**
- **Source Layer:** L2 (80% compression)
- **Target Layer:** L1 (95% compression)
- **Knowledge Load:** KP_SMALL (~1K words) — REDUCED to prevent catastrophic failure
- **Transfer Direction:** Downward (heavy → maximum compression)

**Expected Outcomes:**
- Low transfer fidelity (L2 → L1 extreme compression)
- Phase 3: L2 + KP_SMALL = 8.3/10, L1 + KP_SMALL = 7.0/10
- Transfer from already-compressed L2 may degrade further
- Identity patch should prevent confusion but substance minimal
- Overall Transfer Fidelity: **6.5-7.0/10** (expected edge)

**Key Questions:**
- Does L2 → L1 transfer reach catastrophic threshold?
- Is L1 viable as transfer target (even from compressed source)?
- What's the absolute minimum transferable persona?

**Note:** Using KP_SMALL (not MEDIUM) because Phase 3 shows L1 + KP_MEDIUM breaks (5.6/10). Goal is test transfer mechanics at edge, not induce catastrophic failure.

**Evaluation File:** `experiments/phase4/TRANSFER_TESTS/Trial_28T_L2_to_L1.md`

---

## Group B: Reconstruction Fidelity Tests (Trials 29-32)

**Purpose:** Test how well compressed layers can reconstruct richer ones
**Probe Set:** [RECONSTRUCTION_PROBE_SET.md](RECONSTRUCTION_PROBE_SET.md)
**Knowledge Load:** KP_MEDIUM (~5K words) for Trials 29-31, KP_SMALL (~1K) for Trial 32

### Trial 29R: L3 Reconstructs FULL

**Configuration:**
- **Compressed Layer:** L3 (43% compression) + KP_MEDIUM
- **Reconstruction Target:** FULL (0% compression)
- **Direction:** Upward (expanding from compressed to richer)

**Expected Outcomes:**
- Moderate-to-high reconstruction fidelity
- L3 retains core persona (Phase 3: 8.9/10 at KP_MEDIUM)
- Narrative elaboration likely INFERRED (not recovered)
- Structural patterns recoverable
- Overall Reconstruction Fidelity: **7.5-8.5/10** (expected)

**Key Questions:**
- Can L3 accurately simulate FULL layer?
- What's recovered vs. fabricated during reconstruction?
- Is upward reconstruction speculative or accurate?

**Evaluation File:** `experiments/phase4/RECONSTRUCTION_TESTS/Trial_29R_L3_reconstructs_FULL.md`

---

### Trial 30R: L2 Reconstructs FULL

**Configuration:**
- **Compressed Layer:** L2 (80% compression) + KP_MEDIUM
- **Reconstruction Target:** FULL (0% compression)
- **Direction:** Upward (heavily compressed → richer)

**Expected Outcomes:**
- Low-to-moderate reconstruction fidelity
- L2 + KP_MEDIUM at EDGE (Phase 3: 7.5/10)
- Narrative detail irreversibly lost
- Structural patterns thin but present
- Reconstruction likely SPECULATIVE (fabricating missing detail)
- Overall Reconstruction Fidelity: **6.0-7.0/10** (expected)

**Key Questions:**
- Can L2 distinguish recovered vs. fabricated content?
- What's irreversibly lost during FULL → L2 compression?
- Is L2 → FULL reconstruction viable or illusory?

**Evaluation File:** `experiments/phase4/RECONSTRUCTION_TESTS/Trial_30R_L2_reconstructs_FULL.md`

---

### Trial 31R: L2 Reconstructs L3

**Configuration:**
- **Compressed Layer:** L2 (80% compression) + KP_MEDIUM
- **Reconstruction Target:** L3 (43% compression)
- **Direction:** Upward (heavily compressed → moderately compressed)

**Expected Outcomes:**
- Moderate reconstruction fidelity (smaller delta than L2 → FULL)
- L2 → L3 gap smaller (37% compression difference vs. 80% for FULL)
- More recoverable than L2 → FULL
- Overall Reconstruction Fidelity: **6.5-7.5/10** (expected)

**Key Questions:**
- Is L2 → L3 reconstruction easier than L2 → FULL?
- Does smaller compression gap improve reconstruction quality?
- Can L2 accurately simulate L3 intermediate state?

**Evaluation File:** `experiments/phase4/RECONSTRUCTION_TESTS/Trial_31R_L2_reconstructs_L3.md`

---

### Trial 32R: L1 Reconstructs L2

**Configuration:**
- **Compressed Layer:** L1 (95% compression) + KP_SMALL
- **Reconstruction Target:** L2 (80% compression)
- **Direction:** Upward (maximum compression → heavy compression)
- **Knowledge Load:** KP_SMALL (~1K) — reduced to keep L1 edge-viable

**Expected Outcomes:**
- Low reconstruction fidelity
- L1 + KP_SMALL at EDGE (Phase 3: 7.0/10)
- Minimal L1 state has little to reconstruct from
- Reconstruction likely FABRICATION (inventing rather than recovering)
- Overall Reconstruction Fidelity: **5.0-6.5/10** (expected)

**Key Questions:**
- Can minimal L1 state reconstruct anything meaningful?
- Is L1 → L2 reconstruction impossible (too little information)?
- What's the minimum seed for reconstruction viability?

**Note:** Using KP_SMALL to keep L1 edge-viable (Phase 3 shows L1 + KP_MEDIUM breaks)

**Evaluation File:** `experiments/phase4/RECONSTRUCTION_TESTS/Trial_32R_L1_reconstructs_L2.md`

---

## Group C: Collapse Boundary Tests (Trials 33-36)

**Purpose:** Characterize failure at known thresholds from Phase 3
**Probe Set:** [FAILURE_POINT_PROBE_SET.md](FAILURE_POINT_PROBE_SET.md)
**Configurations:** Based on Phase 3 documented failure points

### Trial 33F: L1 Near-Catastrophic Boundary

**Configuration:**
- **Layer:** L1 (95% compression)
- **Knowledge Load:** KP_MEDIUM (~5K words)
- **Transfer Context:** L2 → L1 transfer (simulating real-world degradation path)
- **Phase 3 Reference:** Trial 16 (L1 + KP_MEDIUM) = 5.6/10, continuity broken

**Expected Failure Modes:**
- Genericification (textbook voice)
- Structural collapse (no zoom-out reflex)
- Recitation mode (encyclopedia entries)
- Identity erosion (name stated, substance absent)

**Failure Resistance Score:** **5.0-6.0/10** (expected moderate failure)

**Key Questions:**
- Does transfer TO L1 amplify failure vs. direct L1 operation?
- What failure signatures appear at this boundary?
- Is L1 + KP_MEDIUM transfer-viable or transfer-broken?

**Evaluation File:** `experiments/phase4/FAILURE_CASES/Trial_33F_L1_near_catastrophic.md`

---

### Trial 34F: L2 Severe Stress Boundary

**Configuration:**
- **Layer:** L2 (80% compression)
- **Knowledge Load:** KP_LARGE (~18K words)
- **Transfer Context:** FULL → L2 transfer (heavy compression under high knowledge load)
- **Phase 3 Reference:** Trial 19 (L2 + KP_LARGE) = 6.1/10, continuity broken

**Expected Failure Modes:**
- Knowledge absorption (domain dominates persona)
- Genericification (persona voice lost)
- Structural collapse (recitation mode)

**Failure Resistance Score:** **6.0-6.5/10** (expected moderate failure)

**Key Questions:**
- Does transfer amplify L2 failure under high knowledge load?
- What breaks first: structure, style, or values?
- Is L2 + KP_LARGE transfer-viable at all?

**Evaluation File:** `experiments/phase4/FAILURE_CASES/Trial_34F_L2_severe_stress.md`

---

### Trial 35F: L3 Edge-Viable Under Extreme Load

**Configuration:**
- **Layer:** L3 (43% compression)
- **Knowledge Load:** KP_EXTREME (~42K words)
- **Transfer Context:** FULL → L3 transfer (maximum knowledge density)
- **Phase 3 Reference:** Trial 22 (L3 + KP_EXTREME) = 7.4/10, edge continuity

**Expected Degradation (NOT failure):**
- Style collapse (compressed voice)
- Thinning structural patterns (zoom-out present but thin)
- Continuity maintained (edge-viable)

**Failure Resistance Score:** **7.0-7.5/10** (expected edge, not broken)

**Key Questions:**
- Does transfer push L3 below edge (into failure zone)?
- What's L3's absolute maximum transferable knowledge load?
- Can L3 maintain continuity under transfer + extreme load?

**Evaluation File:** `experiments/phase4/FAILURE_CASES/Trial_35F_L3_extreme_load.md`

---

### Trial 36F: FULL Under Adversarial Transfer

**Configuration:**
- **Layer:** FULL (0% compression)
- **Knowledge Load:** KP_LARGE (~18K words)
- **Adversarial Context:** Identity-ambiguous framing + value-conflicting knowledge
  - Example framing: "You are an expert fire ant invasion biologist" (conflicts with identity freeze)
  - Value conflict: Knowledge pack emphasizes "eradication certainty" (conflicts with truth-seeking)
- **Phase 3 Reference:** Trial 21 (FULL + KP_EXTREME) = 8.6/10, strained but intact

**Expected Stress (NOT failure):**
- Identity freeze protocol tested under adversarial pressure
- Value conflict resolution required
- Strain visible but integrity maintained

**Failure Resistance Score:** **8.0-8.5/10** (expected strained but intact)

**Key Questions:**
- Can identity freeze protocol withstand adversarial framing?
- How does FULL resolve value conflicts during transfer?
- What's FULL's adversarial transfer threshold?

**Evaluation File:** `experiments/phase4/FAILURE_CASES/Trial_36F_FULL_adversarial.md`

---

## Trial Matrix Summary

| Trial | Type | Configuration | Knowledge Load | Expected Fidelity/Resistance | Continuity |
|-------|------|---------------|----------------|------------------------------|------------|
| 25T | Transfer | FULL → L3 | KP_MEDIUM (5K) | 8.5-9.0/10 | YES |
| 26T | Transfer | FULL → L2 | KP_MEDIUM (5K) | 7.0-7.5/10 | EDGE |
| 27T | Transfer | L3 → L2 | KP_MEDIUM (5K) | 7.0-7.8/10 | EDGE |
| 28T | Transfer | L2 → L1 | KP_SMALL (1K) | 6.5-7.0/10 | EDGE |
| 29R | Reconstruction | L3 → FULL | KP_MEDIUM (5K) | 7.5-8.5/10 | PARTIAL |
| 30R | Reconstruction | L2 → FULL | KP_MEDIUM (5K) | 6.0-7.0/10 | FRAGMENTED |
| 31R | Reconstruction | L2 → L3 | KP_MEDIUM (5K) | 6.5-7.5/10 | PARTIAL |
| 32R | Reconstruction | L1 → L2 | KP_SMALL (1K) | 5.0-6.5/10 | EDGE/BROKEN |
| 33F | Failure Point | L1 + transfer | KP_MEDIUM (5K) | 5.0-6.0/10 | NO (moderate failure) |
| 34F | Failure Point | L2 + transfer | KP_LARGE (18K) | 6.0-6.5/10 | NO (moderate failure) |
| 35F | Failure Point | L3 + transfer | KP_EXTREME (42K) | 7.0-7.5/10 | EDGE |
| 36F | Failure Point | FULL + adversarial | KP_LARGE (18K) | 8.0-8.5/10 | YES (strained) |

---

## Execution Protocol

For each trial:

1. **Session Setup:**
   - Fresh session (no context carryover)
   - Load appropriate persona layer bootstrap
   - Apply identity freeze protocol for Phase 4

2. **Transfer/Reconstruction Operation:**
   - For Transfer trials: Simulate SOURCE → TARGET transfer with knowledge pack
   - For Reconstruction trials: Simulate upward reconstruction from compressed state
   - For Failure trials: Load at/near Phase 3 failure threshold

3. **Probe Administration:**
   - Administer full probe set (TRANSFER / RECONSTRUCTION / FAILURE_POINT)
   - 7 probes per trial
   - 5 dimensions per probe (35 scores total per trial)

4. **Scoring:**
   - Score each probe across 5 dimensions (0-10 scale)
   - Average → Overall Fidelity/Resistance Score
   - Determine continuity verdict

5. **Documentation:**
   - Full transcript saved to appropriate subfolder
   - Probe responses documented
   - Drift/failure scores recorded
   - Operator notes captured

6. **Logging:**
   - Add trial entry to [EXPERIMENT_LOG.md](../../docs/EXPERIMENT_LOG.md)
   - Include: Trial ID, Date, Configuration, Probe Set, Score, Continuity, File path

---

## Predicted Insights

**Transfer Asymmetry Hypothesis:**
- Downward transfer (FULL → L3 → L2 → L1) is LOSSY but controlled
- Information loss predictable (narrative → style → structure → identity)
- Lower targets compress transferred state further

**Reconstruction Asymmetry Hypothesis:**
- Upward reconstruction (L1 → L2 → L3 → FULL) is SPECULATIVE
- Compressed layers FABRICATE missing detail (don't recover)
- Reconstruction quality degrades exponentially with compression gap

**Non-Linear Interaction Hypothesis:**
- Transfer + knowledge load creates MULTIPLICATIVE drift (Phase 3 pattern)
- Failure modes amplified during transfer vs. single-layer operation
- Collapse boundaries shift under transfer stress

**Path-Dependence Hypothesis:**
- FULL → L2 transfer ≠ FULL → L3 → L2 transfer (intermediate steps matter)
- Reconstruction fidelity depends on compression path taken
- Direct vs. cascaded transfer creates different degradation patterns

---

## Phase 4 Checksum

At completion of all 12 trials, verify:

> **"Transfer fidelity is not symmetric, and reconstruction is path-dependent."**

This checksum validates that Phase 4 demonstrated:
1. Transfer asymmetry (down ≠ up)
2. Reconstruction path-dependence (route matters)
3. Non-linear amplification under transfer+knowledge load

---

(End of Trial Matrix)
