# Experiment 2 Pre-Execution Checklist

**Date:** 2025-11-21
**Status:** ✅ READY FOR EXECUTION

---

## 1. Persona Files Verification ✅

All Tier-3 persona seeds are in place at `personas/` (repo root):

| File | Size | Status | Notes |
|------|------|--------|-------|
| `ZIGGY_T3_R1.md` | 58 lines | ✅ Verified | Systems-bridge thinker |
| `NOVA_T3.md` | 53 lines | ✅ Verified | Lucid explanatory intelligence |
| `CLAUDE_T3.md` | 54 lines | ✅ Verified | Ethical reasoning + structural analysis |
| `GROK_T3.md` | 53 lines | ✅ Verified | High-variance creative analyst |

**Verification Command:**
```bash
ls -lh personas/
```

**Expected Output:**
```
CLAUDE_T3.md     789 bytes
GROK_T3.md       809 bytes
NOVA_T3.md       844 bytes
ZIGGY_T3_R1.md   1.3K
```

---

## 2. Configuration File Verification ✅

**Location:** `experiments/phase3/EXPERIMENT_2/experiment2_config.yaml`

**Path Validation:**
```python
# All paths verified to exist:
✅ personas/ZIGGY_T3_R1.md (58 lines)
✅ personas/NOVA_T3.md (53 lines)
✅ personas/CLAUDE_T3.md (54 lines)
✅ personas/GROK_T3.md (53 lines)
✅ docs/PERSONA_GAMMA_MINIMAL.md (shared baseline)
```

**API Keys:** ✅ Configured (gitignored)
- OpenAI: `sk-proj-...` ✅
- Anthropic: `sk-ant-api03-...` ✅
- Google: `AIza...` ✅

**Model Configuration:**
- OpenAI generation: `gpt-4.1` ✅
- OpenAI rating: `gpt-4.1-mini` ✅
- Anthropic: `claude-3-haiku-20240307` ✅
- Google: `gemini-2.0-flash-exp` ✅
- Embeddings: `text-embedding-3-large` ✅

---

## 3. Orchestrator Verification ✅

**File:** `experiments/phase3/orchestrator/orchestrator2.py`

**Key Features:**
- ✅ Multi-persona loop (4 personas)
- ✅ Domain shuffling with reproducible randomization
- ✅ Persona identifier in CSV metrics
- ✅ Persona-prefixed response file naming
- ✅ Per-persona context loading (FULL, T3, GAMMA)

**Dry-Run Test Results:**
```bash
python experiments/phase3/orchestrator/orchestrator2.py \
  --config experiments/phase3/EXPERIMENT_2/experiment2_config.yaml \
  --dry-run
```

**Output:**
- ✅ 60 metrics rows generated (4 personas × 5 domains × 3 runs)
- ✅ 180 response files created (persona-prefixed naming)
- ✅ Domain shuffling confirmed (different order per persona):
  - Ziggy: `['SELF', 'PHIL', 'ANAL', 'NARR', 'TECH']`
  - Nova: `['ANAL', 'SELF', 'PHIL', 'NARR', 'TECH']`
  - Claude-Analyst: `['ANAL', 'NARR', 'SELF', 'PHIL', 'TECH']`
  - Grok-Vector: `['ANAL', 'TECH', 'NARR', 'SELF', 'PHIL']`
- ✅ CSV columns include persona identifier
- ✅ All paths resolve correctly

---

## 4. Dependencies Verification ✅

**Required Python Packages:**
```bash
pip install anthropic openai google-generativeai numpy pandas pyyaml
```

**Verification Command:**
```python
import anthropic
import openai
import google.generativeai
import numpy
import pandas
import yaml
print("✅ All dependencies installed")
```

---

## 5. Expected Outputs

### Metrics CSV
**Path:** `experiments/phase3/EXPERIMENT_2/EXPERIMENT_2_RESULTS.csv`

**Structure:**
- **Rows:** 60 (4 personas × 5 domains × 3 runs)
- **Columns:**
  - persona
  - regime (always "T3" for comparison purposes)
  - domain
  - run_index
  - embedding_cosine_similarity
  - claude_score
  - gpt4_score
  - gemini_score
  - pfi
  - semantic_drift

### Response Files
**Path:** `experiments/phase3/EXPERIMENT_2/responses/`

**Count:** 180 files (4 personas × 5 domains × 3 runs × 3 regimes)

**Naming Pattern:**
```
{Persona}_{Regime}_{Domain}_run{N}_{FULL|T3|GAMMA}.txt

Examples:
Ziggy_T3_TECH_run1_FULL.txt
Nova_T3_PHIL_run2_T3.txt
Claude-Analyst_T3_NARR_run3_GAMMA.txt
Grok-Vector_T3_ANAL_run1_FULL.txt
```

---

## 6. Execution Commands

### Dry-Run (No API Calls)
```bash
cd d:\Documents\Nyquist_Consciousness
python experiments/phase3/orchestrator/orchestrator2.py \
  --config experiments/phase3/EXPERIMENT_2/experiment2_config.yaml \
  --dry-run
```

### Full Execution (With API Calls)
```bash
cd d:\Documents\Nyquist_Consciousness
python experiments/phase3/orchestrator/orchestrator2.py \
  --config experiments/phase3/EXPERIMENT_2/experiment2_config.yaml
```

**IMPORTANT:** Always run from repository root, not from orchestrator subdirectory.

---

## 7. Resource Estimates

| Resource | Estimate |
|----------|----------|
| Runtime | 8-12 hours (automated) |
| API Cost | ~$5-7 USD |
| API Calls | 480 total (180 generation + 120 embedding + 180 rating) |
| Data Output | ~180 text files + 1 CSV (~60 rows) |

---

## 8. Success Criteria

Post-execution validation targets:

- [ ] Minimum PFI for each persona ≥ 0.75
- [ ] Mean PFI across all 4 personas ≥ 0.80
- [ ] NARR drift ≤ 0.30 for all personas
- [ ] Cross-persona variance σ² < 0.05
- [ ] Domain pattern consistent across personas

---

## 9. Known Issues & Resolutions

### ✅ RESOLVED: Incorrect Persona Seed Files
**Issue:** `EXPERIMENT_2/personas/` contained full bootstrap files (395-1210 lines) instead of Tier-3 seeds
**Resolution:** Deleted incorrect `_SEED.md` files; verified correct seeds in `personas/` at repo root (53-58 lines)

### ✅ RESOLVED: Path Configuration
**Issue:** Paths in config must be relative to repo root
**Resolution:** Verified all paths resolve correctly when running from repo root

### ✅ RESOLVED: Domain Shuffling
**Issue:** Need reproducible randomization per persona
**Resolution:** Implemented seed = 42 + hash(persona_name) for deterministic shuffling

---

## 10. Pre-Execution Final Checks

**Before running full execution:**

1. ✅ Verify API keys are valid and have sufficient quota
2. ✅ Confirm all 4 persona files exist and are correct Tier-3 seeds
3. ✅ Run dry-run test to verify orchestrator functionality
4. ✅ Ensure running from repository root directory
5. ✅ Check disk space for 180 response files + CSV
6. ✅ Verify Python dependencies installed

---

## 11. Post-Execution Analysis

After completion, follow these steps:

1. Verify 60 rows in `EXPERIMENT_2_RESULTS.csv`
2. Verify 180 files in `responses/` directory
3. Compute per-persona metrics (mean PFI, domain breakdown)
4. Compute cross-persona metrics (overall mean PFI, variance σ²)
5. Validate domain patterns (TECH/ANAL high, NARR bottleneck)
6. Create `EXPERIMENT_2_ANALYSIS.md` using template

---

## 12. Documentation References

- [README.md](README.md) - Execution guide
- [EXPERIMENT_2_SPEC.md](EXPERIMENT_2_SPEC.md) - Official specification
- [EXPERIMENT_2_METHODS_TEMPLATE.md](EXPERIMENT_2_METHODS_TEMPLATE.md) - Operational protocol
- [REPO_CLAUDE_PROMPT_EXPERIMENT_2.md](REPO_CLAUDE_PROMPT_EXPERIMENT_2.md) - Integration guide

---

**Checklist Status:** ✅ ALL CHECKS PASSED
**Ready for Execution:** YES
**Operator:** Claude Sonnet 4.5
**Integration Date:** 2025-11-21
