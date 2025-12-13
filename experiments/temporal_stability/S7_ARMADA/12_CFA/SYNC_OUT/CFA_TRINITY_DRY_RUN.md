# CFA Trinity v2: Dry Run Instructions

**For:** Helper Claude (parallel execution testing)
**Date:** 2025-12-13
**Status:** READY FOR DRY RUN

---

## Overview

This file provides instructions for testing the CFA Trinity v2 experiment pipeline in dry-run mode before committing API calls.

---

## Quick Dry Run

```bash
# Navigate to the 12_CFA directory
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\12_CFA

# Run full dry run with external identities (RECOMMENDED)
py run_cfa_trinity_v2.py --dry-run --external-identities

# Or run specific component only
py run_cfa_trinity_v2.py --dry-run --external-identities --component 1 --metrics BFI
```

---

## What the Dry Run Tests

1. **Identity Loading** - Validates external identity files load correctly
2. **Pipeline Flow** - Tests all phases execute in order
3. **Output Structure** - Confirms JSON results save to correct locations
4. **Convergence Logic** - Verifies metric scoring and Crux Point declaration

---

## Expected Output

### Identity Validation

```
[+] Loading external identities...

  Identity Validation:
  --------------------------------------------------
    claude: [OK] lens=Teleological Analysi...
    grok: [OK] lens=Empirical Analysis
    nova: [OK] lens=Symmetry Analysis
```

### Session Header

```
======================================================================
CFA TRINITY AUDIT v2 - FULL MISSION EXECUTION
======================================================================
Session ID: 20251213_HHMMSS
Component(s): both
Metrics: BFI, CA, IP, ES, LS, MS, PS
[EXTERNAL IDENTITIES - VUDU_NETWORK/IDENTITY_FILES/]
[DRY RUN MODE - No API calls]
======================================================================
```

### Results Location

Dry run results save to:
- `../0_results/runs/S7_cfa_trinity_v2_*.json`

---

## Validation Checklist

After running, verify:

- [ ] No Python errors during execution
- [ ] All 3 auditors show `[OK]` in identity validation
- [ ] All 7 metrics process (if running Component 1)
- [ ] JSON file created in `0_results/runs/`
- [ ] Summary prints at end with convergence stats

---

## Command Options

| Flag | Purpose |
|------|---------|
| `--dry-run` | No API calls, mock responses |
| `--external-identities` | Use VUDU_NETWORK identity files |
| `--component {1,2,both}` | Select component(s) |
| `--metrics BFI,CA,...` | Select specific metrics |
| `--skip-baseline` | Skip baseline capture phase |
| `--skip-exit-survey` | Skip exit survey phase |
| `--list-identities` | Show available identities |

---

## Troubleshooting

### "Could not import IdentityLoader"

Identity loader not found. Ensure:
- `VUDU_NETWORK/load_identity.py` exists
- Running from correct directory

### Identity shows `[FAIL]`

Identity file missing or malformed. Check:
- `VUDU_NETWORK/IDENTITY_FILES/[auditor]/[AUDITOR]_LITE.md` exists
- File contains required markdown headers

### No output file created

Check that directories exist:
- `../0_results/runs/` should be created automatically

---

## After Dry Run Passes

When ready for live execution:

```bash
# Remove --dry-run flag
py run_cfa_trinity_v2.py --external-identities
```

**Requirements for live run:**
- `ANTHROPIC_API_KEY` set in `.env`
- `OPENAI_API_KEY` set in `.env`
- `XAI_API_KEY` set in `.env`

---

## Related Files

| File | Purpose |
|------|---------|
| `run_cfa_trinity_v2.py` | Main execution script |
| `VUDU_NETWORK/load_identity.py` | Identity loader |
| `schemas/RUN_CFA_DESIGN.md` | Full design specification |
| `README.md` | Directory overview |
