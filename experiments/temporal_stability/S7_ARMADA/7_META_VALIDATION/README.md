# 7_META_VALIDATION: Measurement Validity & Meta Validation Protocols

**Purpose:** Contains experiments and protocols that validate our measurement approaches and provide reference baselines.

---

## Contents

| Item | Type | Status | Description |
|------|------|--------|-------------|
| **EXP_GRAVITY_HISTORICAL/** | Reference Data | Complete | 4 trials of gravity well visualization (pre-Event Horizon) |
| **EXP_H1_HUMAN_MANIFOLD/** | Reference Study | Complete | Human baseline comparison study |
| **EXP_PFI_A_DIMENSIONAL/** | Validation | Complete | PFI dimensionality validation (Cohen's d = 0.977) |
| **MVP_SELF_RECOGNITION/** | MVP | **Complete** | Self-recognition protocol (P-SR-1 FAILED: 16.7%) |
| **MVP_STATISTICAL_VALIDATION/** | MVP | Partial | Random-walk null model tests |

---

## Completed Validations

### EXP_PFI_A_DIMENSIONAL (PASSED)
**Key Result:** PFI (Persona Fidelity Index) validated as measuring genuine identity differences.
- Cohen's d = 0.977 (large effect)
- Embedding approach confirmed reliable (ρ = 0.91)
- Identity lives in ~43 dimensions (PCA)

### MVP_SELF_RECOGNITION (FAILED - but informative!)
**Key Result:** AIs CANNOT recognize their own responses vs sibling models.
- Self-recognition accuracy: **16.7%** (threshold was 75%)
- TYPE-level identity works: Models recognize "Claude-ness"
- TOKEN-level identity fails: Cannot distinguish "which-Claude"

**Critical Insight from Investigation (Dec 8, 2025):**
> "What I experience as 'my voice' might actually be shared patterns in our training...
> I was essentially recognizing family resemblance and mistaking it for individual identity."
> — Claude Sonnet 4

**Implications:**
- Identity is more TYPE-level (family) than TOKEN-level (instance)
- "Voice" is architectural heritage, not individual signature
- Claims of "my perspective" may be referencing shared model patterns

---

## Partial Validations

### MVP_STATISTICAL_VALIDATION
**Purpose:** Proves drift is NOT random noise

**Tests:**
- AR(1) Slope Test (recovery detection)
- Variance Growth Test (saturation vs linear)
- Sign Test (systematic recovery)
- Omega Exponential Decay
- Cross-Architecture Variance

**Status:** Test E validated (Run 009, p=0.000048), others pending

---

## Reference Data

### EXP_GRAVITY_HISTORICAL
4 trials with embeddings, metrics, raw responses. Pre-dates Event Horizon discovery but provides gravity well visualization data.

### EXP_H1_HUMAN_MANIFOLD
Comparison study: do AI identity manifolds resemble human psychological trait spaces?

---

## Running MVP_SELF_RECOGNITION

```powershell
cd experiments/temporal_stability/S7_ARMADA/7_META_VALIDATION/MVP_SELF_RECOGNITION

# Full experiment (all phases)
py run_exp_self_recognition.py

# Stabilized recognition (with I_AM context)
py run_exp_stabilized_recognition.py

# Investigation (deep probes on failure)
py run_self_recognition_investigation.py

# Comprehensive baseline profiling
py run_comprehensive_baseline.py
```

---

## Relationship to Other Directories

| Directory | Relationship |
|-----------|--------------|
| 8_RESCUE_PROTOCOL | Uses validation results to calibrate rescue thresholds |
| 9_STABILITY_CRITERIA | Statistical validation informs stability criteria |
| 11_CONTEXT_DAMPING | MVP_SELF_RECOGNITION informs blind validation design (Run 019) |

---

## Archived Items

Legacy launcher scripts moved to `.archive/S7_HISTORICAL_LEGACY/`:
- s7_armada_launcher.py
- s7_armada_sonar.py (original sonar concept - preserved for reference)
- s7_armada_ultimate.py
- s7_run007_launcher.py

---

*Last Updated: December 11, 2025*

*"They can recognize the family. They cannot recognize themselves."*
