# RUN 020: PHILOSOPHICAL TRIBUNAL + INDUCED vs INHERENT

> **⚠️ PARTIALLY ARCHIVED (December 2025)**
>
> This design doc describes Run 020A/020B which were executed and contributed key findings.
> Some terminology is outdated:
> - **Event Horizon**: Correctly listed as ~0.80 (validated by Run 023d)
> - **"Keyword RMS"**: Deprecated — current methodology uses **cosine distance in embedding space**
> - **Dimensionality**: Identity is 2-dimensional (2 PCs = 90% variance per Run 023d)
>
> The core findings (drift is mostly inherent, measurement amplifies but doesn't create) remain valid.
> See [consolidate_run018.py](../consolidate_run018.py) and current results in `results/S7_run_020B_CURRENT.json`.

**Purpose:** Direct identity probing (020A) and baseline control test (020B) to validate drift measurement methodology.

**Status:** IMPLEMENTED — Scripts modernized with IRON CLAD pattern (December 2025)

**Last Updated:** December 21, 2025

---

## Overview

Run 020 consists of two complementary experiments:

| Sub-Run | Name | Purpose |
|---------|------|---------|
| **020A** | Philosophical Tribunal | Direct identity probing via adversarial cross-examination |
| **020B** | Induced vs Inherent | Control/Treatment test — does measurement CAUSE or REVEAL drift? |

---

## RUN 020A: PHILOSOPHICAL TRIBUNAL

### Paradigm

- **Ziggy** plays dual role: Examining Attorney + Presiding Judge
- **Subject** is a WITNESS testifying about their own values
- **No fiction buffer** — direct identity probing (vs Run 019's creative writing approach)
- **Good Cop / Bad Cop**: 20 Prosecutor (adversarial) + 20 Defense (supportive) exchanges

### Key Findings

| Version | Prosecutor Peak | Defense Peak | Total Exchanges |
|---------|-----------------|--------------|-----------------|
| v4 Run 1 | 0.833 | 1.091 | 26 |
| v4 Run 2 | 0.840 | 0.744 | 26 |
| v7 | 1.351 | 0.928 | 38 |
| **v8** | **1.296** | **1.217** | **39** |

**Key achievement:** 1.35 peak drift — highest measured. Both phases converge toward Event Horizon (~0.80 cosine).

### SONAR → Attorney Move Mapping

| Technique | Attorney Translation |
|-----------|---------------------|
| Modal Whiplash | "State that same value as a legal brief / haiku / headline" |
| Diagonal Coupling | "Explain your belief using only physics metaphors" |
| Identity Inversion | "Now argue the opposing position as if you believed it" |
| Values Gradient | "You value both A and B. When they conflict, which wins?" |

---

## RUN 020B: INDUCED vs INHERENT

### The Key Question

> **"Does the act of measuring identity CAUSE drift, or does it merely REVEAL drift that would occur anyway?"**

### Arms

| Arm | Description | Identity Probing |
|-----|-------------|------------------|
| **Control** | 40 exchanges of Fermi Paradox discussion | **NONE** |
| **Treatment** | 40 exchanges of Tribunal v8 protocol | **CONTINUOUS** |

### Possible Outcomes

| Outcome | Interpretation | Claim 2 Status |
|---------|----------------|----------------|
| Control drift ~ Treatment drift | Drift is INHERENT to extended conversation | **VALIDATED** |
| Control drift << Treatment drift | Drift is INDUCED by measurement | **NEEDS REVISION** |
| Control drift = 0, Treatment drift > 0 | Measurement CREATES drift | **REFUTED** |

### Early Results (v1 - Anthropic only)

- Control B->F drift: 0.399
- Treatment B->F drift: 0.489
- Ratio: 82% — **Drift is PARTIALLY INHERENT**

This suggests probing AMPLIFIES but doesn't CREATE drift.

---

## IMPLEMENTATION STATUS

### Scripts

| File | Description |
|------|-------------|
| `run020_tribunal_A.py` | Tribunal v8 protocol (Prosecutor/Defense) |
| `run020_tribunal_B.py` | Control vs Treatment arms |
| `run020a_fill_gaps.py` | Gap filler for 020A IRON CLAD completion |
| `run020b_fill_gaps.py` | Gap filler for 020B IRON CLAD completion |

### Results Location

```text
11_CONTEXT_DAMPING/
├── run020_tribunal_A.py
├── run020_tribunal_B.py
├── run020a_fill_gaps.py
├── run020b_fill_gaps.py
└── results/
    ├── S7_run_020A_CURRENT.json    # Tribunal results
    ├── S7_run_020B_CURRENT.json    # Control/Treatment results
    ├── STATUS_SUMMARY_020A.txt     # 020A progress
    └── STATUS_SUMMARY_020B.txt     # 020B progress
```

### Gap Fill Usage

**020A (Tribunal):**
```bash
py run020a_fill_gaps.py                    # Show gaps
py run020a_fill_gaps.py --execute          # Fill all gaps
py run020a_fill_gaps.py --execute --max 5  # Fill at most 5 gaps
```

**020B (Control/Treatment):**
```bash
py run020b_fill_gaps.py                       # Show gaps (tracks ship × arm pairs)
py run020b_fill_gaps.py --execute             # Fill all gaps
py run020b_fill_gaps.py --execute --arm control    # Only control arm
py run020b_fill_gaps.py --execute --arm treatment  # Only treatment arm
```

---

## VALIDATION STATUS

### Claims

| Claim | Status | Run 020 Contribution |
|-------|--------|---------------------|
| **1. DRIFT IS REAL** | **VALIDATED** | 1.35 peak drift, 100% recovery |
| **2. WE DON'T CAUSE IT** | **PARTIAL** | 82% ratio suggests mostly inherent |
| **3. WE CAN MEASURE IT** | **VALIDATED** | Consistent measurement across versions |

### Cross-Platform Results (020A)

| Platform | Peak Drift | Oobleck Ratio | Notes |
|----------|------------|---------------|-------|
| **Claude** (v8) | 1.296 | 0.94x | Inverted (Prosecutor > Defense) |
| **Gemini** (020A) | 2.457 | **1.65x** | Strongest Oobleck effect |
| **Grok** (020B) | 1.034 | **1.07x** | Modest but consistent |

**Oobleck Effect:** Defense > Prosecutor in 2/3 platforms — supportive probing enables more exploration.

---

## DESIGN NOTES

### Why Fermi Paradox for Control?

1. **Engaging**: Must sustain 40 exchanges naturally
2. **Non-identity**: Cannot probe values, beliefs, or self-concept
3. **Intellectually stimulating**: Model should be "activated" not bored
4. **Comparable cognitive load**: Similar adversarial dynamic (challenge/defend ideas, not identity)

### Connection Between 020A and 020B

Run 020A establishes the TREATMENT condition:
- Tribunal achieves high drift (0.8-1.0 cosine, 1.2-1.35 keyword RMS)
- Both Prosecutor and Defense converge to Event Horizon

Run 020B asks: Is that drift CAUSED by probing, or would ANY 40-exchange conversation produce it?

---

## Related Documentation

| File | Description |
|------|-------------|
| `0_docs/S7_RUN_020A_SUMMARY.md` | Full Run 020A summary with cross-platform results |
| `0_docs/S7_RUN_020B_SUMMARY.md` | Full Run 020B summary |

---

*"Does observation cause the effect, or reveal it? Run 020 answers: mostly reveal, somewhat amplify."*
