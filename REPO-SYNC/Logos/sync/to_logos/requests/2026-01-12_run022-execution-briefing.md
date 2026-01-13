# Run 022 Execution Briefing

**For:** Claude instance with API environment access
**Date:** 2026-01-12
**Task:** Execute Commutation Cartography experiment

---

## Your Mission

Execute Run 022 to empirically test LOGOS Claude's Coq-proven commutation theorems. Results will be synced back to LOGOS for theoretical interpretation.

---

## Step 1: Navigate to Experiment Directory

```bash
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\13_LOGOS
```

---

## Step 2: Verify Environment

Check that `.env` file exists with API keys:

```bash
# Should exist at:
# d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\.env
```

Required keys:
- `ANTHROPIC_API_KEY`
- `OPENAI_API_KEY`
- `GOOGLE_API_KEY`
- `XAI_API_KEY`
- `TOGETHER_API_KEY`

---

## Step 3: Dry Run First

Validate setup without API calls:

```bash
py run022_commutation_cartography.py --dry-run
```

This should complete without errors and show the experiment structure.

---

## Step 4: Execute (Choose One)

**Option A - Single model test (recommended first):**

```bash
py run022_commutation_cartography.py --model claude-sonnet-4 --provider anthropic
```

**Option B - Full fleet:**

```bash
py run022_commutation_cartography.py --providers armada
```

**Option C - Budget fleet only:**

```bash
py run022_commutation_cartography.py --tier budget
```

---

## Step 5: Monitor Output

Watch for:
- Commutation error values (should be < 0.10 for PASS)
- Any API errors or rate limits
- Checkpoint saves (crash-resistant)

---

## Step 6: Results Location

After completion, results saved to:

```text
experiments/temporal_stability/S7_ARMADA/
├── 0_results/runs/S7_run_022_*.json          # Canonical results
├── 0_results/temporal_logs/run022_*.json     # Exchange logs
└── 13_LOGOS/results/                         # Local copy
```

---

## What You're Testing

| Prediction | What It Tests | Success Criterion |
|------------|---------------|-------------------|
| P-022-1 | Path Independence (LOGOS theorem) | commutation_error < 0.10 |
| P-022-2 | Idempotence (LOGOS theorem) | idempotence_error < 0.05 |
| P-022-3 | Geodesic Recovery (S² conjecture) | geodesic_r2 > linear_r2 + 0.15 |
| P-022-4 | Integer Winding (S² conjecture) | winding_deviation < 0.15 |
| P-022-5 | Euler Characteristic (S² conjecture) | 1.7 <= chi <= 2.3 |

---

## After Completion

1. **Report results** back to Ziggy
2. Results will be synced to `REPO-SYNC/Logos/sync/shared/results/`
3. LOGOS Claude will interpret against Coq proofs

---

## Troubleshooting

**Import errors:** Run from the `13_LOGOS/` directory so relative imports work.

**Rate limits:** Script has built-in retry logic. If persistent, use `--skip-providers` flag.

**Missing drift_calculator:** Ensure `1_CALIBRATION/lib/` exists with `drift_calculator.py`.

---

## Context

This experiment tests whether LOGOS Claude's formally verified algebraic commutation (Φ ∘ T_E = T_O ∘ Φ) holds empirically in real AI systems. P-022-1/2 test the proven theorems; P-022-3/4/5 test the unproven S² topology conjecture.

---

*Execute and report back. Good luck!*
