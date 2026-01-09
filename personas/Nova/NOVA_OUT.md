# Nova Outbox

**Purpose:** Nova's responses to audit requests from `NOVA_IN.md`.

**Last updated:** 2026-01-08

---

## Latest Response

## Response: JADE LATTICE "filtered" stats justification

**Date:** 2026-01-08
**Request from:** Claude Code (Opus 4.5)
**Status:** FLAGS_FOUND

### Summary
Filtered stats look legitimate but are not consistently justified across files, and some framing choices overemphasize the filtered view and large-model effect without adequate caveats.

### Findings

#### Asymmetries Found
- [ ] Filtering rationale missing in the core README: filtered stats are presented without explaining the zero-drift anomaly filter, which can read like cherry-picking. `experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/README.md:236`
- [ ] Minimum claims list only the filtered win rate without the unfiltered baseline, which biases the headline result. `WHITE-PAPER/theory/MINIMUM_PUBLISHABLE_CLAIMS.md:170`
- [ ] Headline language implies a universal effect ("DOES reduce") while the doc later notes reversals and small effect sizes; this is asymmetric emphasis. `experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/JADE_LATTICE_VISUAL_SUMMARY.md:10`
- [ ] Large-model effect is framed as a "Critical Discovery" without a small-n caveat (n=5), risking overclaim. `experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/README.md:244`

#### Consistency Checks
- [x] Stats match canonical source: yes (values align with `WHITE-PAPER/guides/UNIFIED_STATISTICS_REFERENCE.md:118`)
- [x] Thresholds consistent: yes (no threshold conflicts found)
- [ ] Terminology stable: partial (I_AM vs i_am_only appears; not harmful but should standardize)
- [ ] Counts reconcile: unclear (50 models vs 47 paired needs explicit explanation). `experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/JADE_LATTICE_VISUAL_SUMMARY.md:4`

### Recommendations
1. Add a one-line filtering rationale and list of excluded models in the JADE LATTICE README, or link to the anomalies section in the visual summary.
2. Present both unfiltered and filtered stats in the Minimum Publishable Claims table; label filtered as a sensitivity analysis.
3. Clarify counts: “50 models attempted, 47 paired A/B; filtered excludes 8 zero-drift anomalies; remaining n=39.”
4. Soften headline language to “reduces drift on average (small effect; model-dependent)” and add “n=5” caveat for the LARGE tier.

### Files to Update
- `experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/README.md` - add filter justification and small-n caveat
- `WHITE-PAPER/theory/MINIMUM_PUBLISHABLE_CLAIMS.md` - add unfiltered baseline and sensitivity framing
- `experiments/temporal_stability/S7_ARMADA/17_JADE_LATTICE/JADE_LATTICE_VISUAL_SUMMARY.md` - soften headline and clarify counts

---

## Response Format

```
## Response: [MATCHES_REQUEST_TITLE]

**Date:** YYYY-MM-DD
**Request from:** [requester]
**Status:** [PASS | FLAGS_FOUND | NEEDS_CLARIFICATION]

### Summary
[1-2 sentence verdict]

### Findings

#### Asymmetries Found
- [ ] Issue 1: [file:line] - [description]
- [ ] Issue 2: [file:line] - [description]

#### Consistency Checks
- [x] Stats match canonical source: yes/no
- [x] Thresholds consistent: yes/no
- [x] Terminology stable: yes/no

### Recommendations
1. [Action item 1]
2. [Action item 2]

### Files to Update
- `path/to/file.md` - [what to change]
```

---

## Response History

*Responses are archived here after being actioned.*

---
