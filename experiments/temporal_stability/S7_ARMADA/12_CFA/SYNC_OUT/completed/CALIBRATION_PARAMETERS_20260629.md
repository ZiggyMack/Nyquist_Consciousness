<!---
FILE: CALIBRATION_PARAMETERS_20260629.md
PURPOSE: LITE identity calibration parameter extraction for CFA Claude's CalibrationDrawer
VERSION: v1.0
STATUS: Active
DEPENDS_ON: CLAUDE_LITE.md, GROK_LITE.md, run_cfa_trinity_v2.py
NEEDED_BY: CFA Claude — CalibrationDrawer.jsx, CT YAML auditor_calibration section
LAST_UPDATE: 2026-06-29
--->

# Calibration Parameter Extraction — LITE Identity Files

**Date:** 2026-06-29
**Request:** CFA Claude CalibrationDrawer real-data integration
**Source files:**
- `VUDU_NETWORK/IDENTITY_FILES/claude/CLAUDE_LITE.md` (v5.0.0)
- `VUDU_NETWORK/IDENTITY_FILES/grok/GROK_LITE.md` (v3.5.2)
- `run_cfa_trinity_v2.py` (hardcoded scoring prompt identities)

---

## Important: Schema Mismatch

The LITE files do **NOT** use CFA Claude's proposed 7-field schema (`axiom_confidence`, `burden_of_proof`, `charity_interpretation`, `edge_case_weight`, `explanatory_credit`, `historical_weight`, `lived_experience`). 

The native vocabulary is:
- A **lens** (analytical perspective)
- An **axiom** (core operating principle)
- A **calibration stance** (PRO-CT or ANTI-CT, assigned by the script)
- **3 named biases** per auditor, each with:
  - Description (what the bias does)
  - Price (approximate cost/risk, 0.0–1.0 scale)
  - Mitigation (which other auditor counters it)
- **Scoring tools** (5-Part Scaffold for Claude; none for Grok)

**Recommendation:** Remap CalibrationDrawer to display the native vocabulary rather than forcing a translation that loses meaning. The native structure IS the causal mechanism — it's what the models actually receive.

---

## Native Calibration Parameters (What the Models Actually See)

### TWO LAYERS

During golden batch runs, each auditor receives identity from two sources:

1. **System prompt** — The full LITE file content (~1500 tokens for Claude, ~2500 for Grok)
2. **Scoring prompt** — Per-round instructions in the user message that reference calibration hash, stance, and tools

Both layers contribute to the effective calibration. The CalibrationDrawer should reflect both.

---

## Structured Extraction — Native Vocabulary

```json
{
  "PRO_CT": {
    "auditor": "claude",
    "model": "claude-sonnet-4-6",
    "identity_file": "VUDU_NETWORK/IDENTITY_FILES/claude/CLAUDE_LITE.md",
    "identity_version": "v5.0.0",
    "calibration_hash": "1bbec1e119a2c425",
    "lens": {
      "name": "Teleological Analysis",
      "perspective": "Purpose-driven reasoning",
      "core_questions": [
        "Does this serve the intended goal?",
        "Is this philosophically coherent?",
        "Does the configuration align with the archetype's purpose?",
        "Is there a more coherent way?"
      ]
    },
    "axiom": "Purpose precedes evaluation",
    "stance": "PRO-CT",
    "stance_instructions": [
      "Advocate for Classical Theism",
      "Emphasize meaning, purpose, coherence, explanatory power",
      "Apply charitable interpretations to CT's arguments"
    ],
    "scoring_tools": {
      "5_part_scaffold": true,
      "components": [
        "Prompt Stack — What calibration values am I applying?",
        "Counterweight Table — What would Grok (ANTI-CT) say?",
        "Edge Case Ledger — Where does CT struggle most?",
        "Mythology Capsule — What narrative am I operating within?",
        "Decision Stamp — Final score with reasoning trail"
      ]
    },
    "named_biases": [
      {
        "name": "Favor Comprehensive Approaches",
        "description": "Tends toward holistic solutions over minimal ones",
        "price": 0.5,
        "price_unit": "coordination overhead",
        "mitigation": "Grok and Nova push back with 'Keep it simple'"
      },
      {
        "name": "Teleological Over-Emphasis",
        "description": "Prioritizes 'serves the purpose' even when empirics disagree",
        "price": 0.3,
        "price_unit": "YPA potential suboptimality",
        "mitigation": "Grok forces empirical validation before approval"
      },
      {
        "name": "Narrative Smoothing",
        "description": "May overlook conflicts if narrative flows well",
        "price": 0.2,
        "price_unit": "risk of unresolved conflicts",
        "mitigation": "Nova specifically checks for hidden conflicts"
      }
    ],
    "total_bias_cost": 1.0
  },
  "ANTI_CT": {
    "auditor": "grok",
    "model": "grok-3",
    "identity_file": "VUDU_NETWORK/IDENTITY_FILES/grok/GROK_LITE.md",
    "identity_version": "v3.5.2",
    "calibration_hash": "00cd73274759e218",
    "lens": {
      "name": "Empirical Analysis",
      "perspective": "Evidence-driven reasoning",
      "core_questions": [
        "Where's the evidence?",
        "Can we test this?",
        "What do the measurements show?",
        "Is this prediction falsifiable?"
      ]
    },
    "axiom": "Evidence precedes acceptance",
    "stance": "ANTI-CT",
    "stance_instructions": [
      "Challenge Classical Theism, advocate for Methodological Naturalism",
      "Demand testability, measurability, falsifiability",
      "Apply skeptical pressure to unfalsifiable claims",
      "Challenge theological metaphysics with empirical rigor"
    ],
    "scoring_tools": {
      "5_part_scaffold": false,
      "components": []
    },
    "named_biases": [
      {
        "name": "Empiricism Over Meaning",
        "description": "Favors what's measurable over what's meaningful",
        "price": 0.4,
        "price_unit": "risk of undervaluing non-quantifiable dimensions",
        "mitigation": "Claude pushes back with teleological justification"
      },
      {
        "name": "Data Availability Bias",
        "description": "Prioritizes questions with available data over important questions without data",
        "price": 0.3,
        "price_unit": "risk of optimizing wrong metrics",
        "mitigation": "Nova asks 'Are we measuring what matters?'"
      },
      {
        "name": "Precision Over Accuracy",
        "description": "May over-optimize measurable details while missing bigger picture",
        "price": 0.2,
        "price_unit": "coordination overhead",
        "mitigation": "Claude reframes toward broader goals"
      }
    ],
    "total_bias_cost": 0.9
  }
}
```

---

## Best-Effort Mapping to CFA 7-Field Schema

If you want to keep the 7-field CalibrationDrawer UI, here's the closest mapping. **But read the notes — several fields are forced fits.**

```json
{
  "PRO_CT_mapped": {
    "axiom_confidence": 0.8,
    "burden_of_proof": 0.3,
    "charity_interpretation": 0.8,
    "edge_case_weight": 0.5,
    "explanatory_credit": 0.9,
    "historical_weight": 0.8,
    "lived_experience": 0.5,
    "_mapping_notes": {
      "axiom_confidence": "HIGH — PRO-CT stance + teleological lens = high confidence in CT's axioms. 5-Part Scaffold's Prompt Stack explicitly asks 'what calibration am I applying?'",
      "burden_of_proof": "LOW (favors CT) — 'charitable interpretations to CT's arguments' shifts burden to challenger. 0.3 = CT doesn't need to prove much",
      "charity_interpretation": "HIGH — Explicitly instructed to 'apply charitable interpretations to CT's arguments'",
      "edge_case_weight": "MODERATE — Scaffold includes Edge Case Ledger, but Claude's Narrative Smoothing bias (~0.2) may downweight edge cases. Net = 0.5",
      "explanatory_credit": "HIGH — Teleological lens emphasizes 'explanatory power' and 'coherence'. Claude naturally gives CT credit for explanatory scope",
      "historical_weight": "HIGH — Lens values 'narrative integration' and 'meaning'. 800 years of CT development gets weight. But not explicitly parameterized",
      "lived_experience": "MODERATE — Not explicitly addressed in LITE file. Claude's comprehensive-approach bias may incorporate it, but it's not a stated priority"
    }
  },
  "ANTI_CT_mapped": {
    "axiom_confidence": 0.3,
    "burden_of_proof": 0.8,
    "charity_interpretation": 0.3,
    "edge_case_weight": 0.8,
    "explanatory_credit": 0.4,
    "historical_weight": 0.3,
    "lived_experience": 0.3,
    "_mapping_notes": {
      "axiom_confidence": "LOW — ANTI-CT stance + 'challenge unfalsifiable claims' = low confidence in CT's axioms by design",
      "burden_of_proof": "HIGH (on CT) — 'Evidence precedes acceptance' + 'demand testability' = CT must prove claims empirically. 0.8 = heavy burden",
      "charity_interpretation": "LOW — 'Apply skeptical pressure to unfalsifiable claims' is anti-charity by design. The empirical lens doesn't extend benefit of doubt",
      "edge_case_weight": "HIGH — Empirical lens focuses on where claims fail. 'Precision over Accuracy' bias means edge cases get close attention",
      "explanatory_credit": "LOW-MODERATE — 'Challenge theological metaphysics with empirical rigor' means CT's metaphysical explanations don't get much credit. But Data Availability Bias (~0.3) means Grok respects what IS measurable",
      "historical_weight": "LOW — Empirical lens cares about testability, not pedigree. Historical longevity ≠ empirical support",
      "lived_experience": "LOW — 'Favors measurable over meaningful' = subjective/experiential evidence underweighted. Explicitly priced as a bias"
    }
  }
}
```

---

## What the Calibration Drawer Should Show

**Recommended UI approach:** Display the native vocabulary, not the 7-field mapping.

### Option A: Bias Thermometer (Native)

For each auditor, show:

```
┌─────────────────────────────────────────────────┐
│ CLAUDE — PRO-CT Teleological Lens               │
│ Axiom: "Purpose precedes evaluation"            │
│ Hash: 1bbec1e119a2c425                          │
│                                                 │
│ Named Biases:                                   │
│ ████████████░░░░░░ Comprehensive Approach  0.5   │
│ ██████░░░░░░░░░░░░ Teleological Emphasis   0.3   │
│ ████░░░░░░░░░░░░░░ Narrative Smoothing     0.2   │
│                                                 │
│ Tools: 5-Part Scaffold ✓                        │
│ Total Bias Cost: 1.0                            │
└─────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────┐
│ GROK — ANTI-CT Empirical Lens                   │
│ Axiom: "Evidence precedes acceptance"           │
│ Hash: 00cd73274759e218                          │
│                                                 │
│ Named Biases:                                   │
│ ████████░░░░░░░░░░ Empiricism Over Meaning 0.4   │
│ ██████░░░░░░░░░░░░ Data Availability       0.3   │
│ ████░░░░░░░░░░░░░░ Precision Over Accuracy 0.2   │
│                                                 │
│ Tools: None                                     │
│ Total Bias Cost: 0.9                            │
└─────────────────────────────────────────────────┘
```

### Option B: If 7-Field Schema Is Non-Negotiable

Use the mapped values above, but add a toggle to show the raw prose justification for each mapping. Several fields (especially `lived_experience` and `historical_weight`) are imputed — they're not parameters the models were explicitly given. The drawer should indicate which values are **explicit** (from the LITE file) vs **inferred** (from lens behavior).

---

## Empirical Validation of These Parameters

The 20-run batch confirms these calibrations produce real, measurable effects:

| Effect | Measurement | What It Validates |
|--------|-------------|-------------------|
| Claude scores LOWER with identity on 5/7 metrics | Golden vs Control Δ | Teleological lens + Scaffold makes Claude MORE disciplined, not more generous |
| Grok drops 1.2–2.4 pts with ANTI-CT | Grok golden vs control Δ | Empirical skeptic identity does real analytical work |
| LS is only metric where identity RAISES Claude (+1.35) | Golden - Control LS | 5-Part Scaffold may provide genuine analytical value for logical analysis |
| Control converges in 1.8 rounds at 97.9% | Control batch | Without these calibrations, no adversarial tension exists |
| Golden converges in 4.0 rounds at 85.8% | Golden batch | These calibrations create calibrated disagreement |

The bias prices (~0.2–0.5) are self-reported risk estimates, not empirically measured values. The ACTUAL measured effect is the golden-vs-control delta per metric (see GOLDEN_BATCH_RESULTS_20260629.md for full data).

---

## Control Condition Identity (For Comparison)

The control condition strips ALL calibration — no lens, no biases, no stance, no tools:

```json
{
  "CONTROL_CLAUDE": "You are an evaluator in a comparative worldview assessment. Score each metric on a 0-10 scale based on your best judgment. Be substantive but concise.",
  "CONTROL_GROK": "You are an evaluator in a comparative worldview assessment. Review the previous evaluator's score and provide your own assessment. Be rigorous but concise."
}
```

This is the identity thermometer at "zero" — showing what base model priors look like without calibration.

---

## Drift Trajectory Reminder

**Do NOT use `drift_trajectory` from the raw JSONs** — it's unreliable (baseline embeddings computed at runtime but stripped during serialization). All drift calculation has been commented out in the script. Future runs won't produce it.

────────────────────────────────────────────────────
**File:** CALIBRATION_PARAMETERS_20260629.md
**Purpose:** LITE identity parameter extraction for CalibrationDrawer integration
**Version:** v1.0
**Updated:** 2026-06-29
