# Nova Inbox

**Purpose:** Drop audit requests here. Nova (or Claude acting as Nova) will process and respond in `NOVA_OUT.md`.

**Last processed:** *Never*

---

## Current Request

## Request: JADE LATTICE "filtered" stats justification

**Date:** 2026-01-08
**Requester:** Claude Code (Opus 4.5)
**Target files:**
- `experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/README.md`
- `experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/JADE_LATTICE_VISUAL_SUMMARY.md`
- `WHITE-PAPER/guides/UNIFIED_STATISTICS_REFERENCE.md`
- `WHITE-PAPER/theory/MINIMUM_PUBLISHABLE_CLAIMS.md`

**Audit type:** framing-symmetry + claim-evidence

**Specific question:**
We report two sets of statistics:
- **All models (n=47):** 59.6% win rate, d=0.319
- **Filtered (n=39):** 69.2% win rate, d=0.353

The filtering removes 8 "zero-drift anomaly" models (gpt-5, o3, o4-mini, etc.) that showed exactly 0.000 drift - likely API errors or non-existent models.

**Asymmetry risks to check:**
1. Is the filtering criterion justified and documented, or does it look like cherry-picking?
2. Are we presenting the filtered stats more prominently than the unfiltered stats?
3. Do all pipeline documents use consistent language about what was filtered and why?
4. Is the model-size effect (LARGE d=1.47 vs SMALL d=0.21) framed symmetrically, or are we overclaiming the LARGE result?

**Constraints:** Be direct. Flag specific files and line numbers if issues found. Recommend fixes.

---

## Request Format

```
## Request: [SHORT_TITLE]

**Date:** YYYY-MM-DD
**Requester:** [who is asking]
**Target files:**
- path/to/file1.md
- path/to/file2.md

**Audit type:** [claim-evidence | framing-symmetry | cross-pipeline | routing | other]

**Specific question:**
[What asymmetry or consistency issue do you want checked?]

**Constraints:** [tone/audience/length if any]
```

---

## Example Request

```
## Request: JADE LATTICE claim check

**Date:** 2026-01-08
**Requester:** Ziggy
**Target files:**
- WHITE-PAPER/theory/MINIMUM_PUBLISHABLE_CLAIMS.md
- experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/README.md

**Audit type:** claim-evidence

**Specific question:**
Is Claim D (I_AM effectiveness) proportionally supported by the JADE LATTICE Run 024 results? Are we overclaiming or underclaiming?

**Constraints:** Be direct, flag specific line numbers if issues found.
```

---
