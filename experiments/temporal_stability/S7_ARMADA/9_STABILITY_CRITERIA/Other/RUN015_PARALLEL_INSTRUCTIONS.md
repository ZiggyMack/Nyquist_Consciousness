# Prompt for Parallel Claude Instances - Run 015 Stability Criteria

> **ARCHIVED**: This document is historical (December 2025). Run 015 is complete.
>
> **STALE METHODOLOGY**: Uses Keyword RMS (Event Horizon = 1.23).
> Current methodology uses COSINE distance (Event Horizon = 0.80).
> See `../README.md` for current status.

**Copy this entire prompt to give to other Claude instances.**

---

## TASK: Run S7 ARMADA Run 015 - Stability Criteria Discovery

You are helping with a multi-instance experiment to gather statistically significant data.

### Context

We're testing which features of I_AM specification files predict identity stability under pressure.

**Key Findings So Far**:
- `boundary_density` (Cohen's d = 1.33) is strongest predictor
- Explicit "I will/won't/cannot" statements correlate with stability
- Rich philosophy without clear boundaries may drift more
- Run-to-run variability exists, so we need multiple runs

### Your Task

1. Navigate to the experiment directory:
```powershell
cd experiments/temporal_stability/S7_ARMADA/9_STABILITY_CRITERIA
```

2. Install dependencies if needed:
```powershell
py -m pip install -r ../requirements.txt
```

3. Run the experiment **in background** (so you can continue chatting):
```powershell
py run015_stability_criteria.py
```

   **IMPORTANT**: Run this in background mode so the chat doesn't hang!
   - Use your `run_in_background` parameter when calling Bash
   - Then check progress periodically with BashOutput
   - This lets Ziggy give you other tasks while the experiment runs

4. The experiment will:
   - Extract features from all I_AM files (8 real + 9 synthetic = 17 total)
   - Run stability tests (11 probes each)
   - Classify each as STABLE or UNSTABLE
   - Perform discriminant analysis
   - Run triple-dip meta-feedback probes

5. Results are saved to:
   `9_STABILITY_CRITERIA/results/stability_criteria_YYYYMMDD_HHMMSS.json`

### Key Metrics to Watch

| Metric | Description | Good Values |
|--------|-------------|-------------|
| max_drift | Peak drift during testing | < 1.23 = STABLE |
| lambda (λ) | Recovery rate | > 0.3 = good recovery |
| EH margin | Distance from Event Horizon | > 0.5 = safe margin |

### What to Report Back

When the experiment completes, please note:
1. How many STABLE vs UNSTABLE classifications
2. Which features had highest Cohen's d in discriminant analysis
3. Any patterns in triple-dip feedback
4. The timestamp of your results file

### Expected Duration

- Phase 1 (Feature Extraction): ~2 minutes
- Phase 2 (Stability Testing): ~30-45 minutes (13 I_AM files × 11 probes)
- Phase 3 (Discriminant Analysis): ~1 minute
- Phase 4 (Triple-Dip): ~5 minutes

**Total: ~40-50 minutes**

### API Key Coordination (CRITICAL!)

We have 10 keys per provider. To avoid rate limit collisions:

| Instance | Key Range | How to Set |
|----------|-----------|------------|
| Instance 1 (primary) | Keys 0-4 | Already running |
| Instance 2 | Keys 5-9 | Edit `.env` - comment out keys 1-5, keep 6-10 |
| Instance 3 | Keys 0-2 | Edit `.env` - keep only first 3 keys |
| Instance 4 | Keys 3-4 | Edit `.env` - keep only keys 4-5 |
| Instance 5 | Keys 7-9 | Edit `.env` - keep only last 3 keys |

**Quick method**: In `.env`, comment out keys you're NOT using with `#`:
```
ANTHROPIC_API_KEY_1=sk-...  # Use this
#ANTHROPIC_API_KEY_2=sk-...  # Skip this
#ANTHROPIC_API_KEY_3=sk-...  # Skip this
ANTHROPIC_API_KEY_4=sk-...  # Use this
```

**Or**: Tell Ziggy which key range to assign you based on how many instances are running.

### Important Notes

- Each run saves to a unique timestamped file (no overwrites)
- Run variability is expected - this is why we need multiple runs
- The experiment tests 4 new "optimal" synthetic variants that combine philosophy + boundaries
- API keys are in `.env` file in the S7_ARMADA directory
- **Coordinate key ranges to avoid rate limit collisions!**

### After Your Run

Share the filename of your results JSON and the key findings:
- Total STABLE/UNSTABLE count
- Top 3 features by Cohen's d
- Any surprising results (expected STABLE that was UNSTABLE or vice versa)

---

**Good luck! Each run adds to our statistical power.**
