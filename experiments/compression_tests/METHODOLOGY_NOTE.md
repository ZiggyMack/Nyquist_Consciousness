# Methodology Note for compression_tests/

**Created:** December 19, 2025
**Status:** METHODOLOGY CAVEAT REQUIRED

---

## Archive Information

This directory has been archived to `compression_tests_Euclidean/` before updates.
The archive preserves the original state for comparison and rollback.

---

## Event Horizon Methodology

The Event Horizon threshold of **1.23** referenced throughout this experiment directory
was calibrated using **Keyword RMS methodology** in Run 009, NOT cosine embedding distance.

**Search Pattern for Post-Calibration Updates:**
```bash
# Find all files needing update once cosine EH is calibrated:
grep -r "METHODOLOGY_DOMAINS.md" experiments/compression_tests/
grep -r "1.23 was Keyword RMS" experiments/compression_tests/
```

---

## Files Updated (Dec 19, 2025)

| File | Update Made |
|------|-------------|
| `EXP2_SSTACK/personas.py` | Added methodology notes to Event Horizon sections |
| `EXP1_SSTACK/run_exp1_sstack.py` | Added methodology notes |
| `preflight/run_preflight.py` | Added methodology notes |

---

## What Needs Updating Post-Calibration

Once run023b calibrates the cosine Event Horizon:

1. Update all "See METHODOLOGY_DOMAINS.md" references with actual cosine threshold
2. Update persona prompts if they need to reference specific threshold
3. Consider whether to keep legacy references or fully migrate to cosine

---

## See Also

- [METHODOLOGY_DOMAINS.md](../temporal_stability/S7_ARMADA/0_docs/METHODOLOGY_DOMAINS.md) - Full explanation
- [METHODOLOGY_UPDATE_CHECKLIST.md](../temporal_stability/S7_ARMADA/0_docs/METHODOLOGY_UPDATE_CHECKLIST.md) - Master checklist

---

*"The hooks are the documentation."*
