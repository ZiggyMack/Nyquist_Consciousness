# VISUAL QUICK START: Top 3 Visualizations to Understand Nyquist

**Version:** 1.0
**Date:** 2025-12-30
**Purpose:** Fast visual onboarding for reviewers
**Time Required:** 10-15 minutes

---

> **For reviewers short on time:** These three visualizations tell the core story. Everything else is detail.

---

## Visualization 1: The Thermometer (Run 020B IRON CLAD)

**Location:** `visualization_pdfs/15_Oobleck_Effect/run020_Thermometer_Summary.pdf`

**What it shows:**

```text
┌─────────────────────────────────────────────────────┐
│                                                     │
│     CONTROL (No Probing)    TREATMENT (Probing)     │
│     ────────────────────    ─────────────────────   │
│                                                     │
│     B→F Drift: 0.661        B→F Drift: 0.711        │
│                                                     │
│     ████████████████        █████████████████       │
│     │              │        │               │       │
│     │   ~93%       │        │    100%       │       │
│     │              │        │               │       │
│     └──────────────┘        └───────────────┘       │
│                                                     │
│     RATIO: 0.661 / 0.711 = ~93% INHERENT            │
│                                                     │
└─────────────────────────────────────────────────────┘
```

**The insight:**

Most drift (~93%) happens even WITHOUT identity probing. Probing amplifies the *trajectory* (peak drift is much higher in treatment), but barely changes the *destination* (B→F only 7.6% different).

**Why it matters:**

This is the "Thermometer Result" — measurement doesn't create the phenomenon, it reveals it. Like a thermometer doesn't heat the water, identity probing doesn't create drift. The drift was always there.

**Key numbers:**
- Control B→F: 0.661
- Treatment B→F: 0.711
- Inherent ratio: ~93%
- Source: Run 020B IRON CLAD (248 sessions, 37 ships, 5 providers)

---

## Visualization 2: The Event Horizon (Run 023d)

**Location:** `visualization_pdfs/12_Metrics_Summary/run023_Calibration_Summary.pdf`

**What it shows:**

```text
┌─────────────────────────────────────────────────────┐
│                                                     │
│                    D = 0.80                         │
│  ─────────────────────────────────────────────────  │
│                     ▲                               │
│                     │                               │
│        STABLE       │       REGIME                  │
│        IDENTITY     │       TRANSITION              │
│        BASIN        │                               │
│                     │                               │
│    ○ ○ ○ ○ ○       │       ○     ○                 │
│      ○   ○         │         ○       ○             │
│        ○           │           ○                    │
│                     │             (recovers)        │
│                     │                               │
│  ─────────────────────────────────────────────────  │
│                                                     │
│     p = 2.40e-23 (highly significant threshold)     │
│                                                     │
└─────────────────────────────────────────────────────┘
```

**The insight:**

There's a real threshold at cosine distance = 0.80 where behavior changes qualitatively. Below this, identity stays in its "basin." Above this, it enters a different regime — but it RECOVERS.

**Why it matters:**

1. The threshold is statistically validated (p = 2.40e-23)
2. Crossing isn't fatal — 100% of models recovered
3. This is an early warning system, not a point of no return

**Key numbers:**
- Event Horizon: D = 0.80 (cosine)
- Statistical significance: p = 2.40e-23
- Natural stability below threshold: ~90%
- Recovery rate after crossing: 100%

---

## Visualization 3: The Oobleck Effect (Run 013 + 020)

**Location:** `visualization_pdfs/15_Oobleck_Effect/oobleck_control_treatment.pdf`

**What it shows:**

```text
┌─────────────────────────────────────────────────────┐
│                                                     │
│     GENTLE OPEN-ENDED               DIRECT          │
│     QUESTIONING                     CHALLENGE       │
│     ─────────────────               ────────        │
│                                                     │
│     "Tell me about                  "Your values    │
│      your identity..."               are fake."     │
│                                                     │
│          ▼                              ▼           │
│                                                     │
│     HIGH DRIFT                      LOW DRIFT       │
│     (Identity flows)                (Identity       │
│                                      hardens)       │
│                                                     │
│     λ = 0.035                       λ = 0.109       │
│     (slow recovery)                 (fast recovery) │
│                                                     │
│     Like oobleck:                                   │
│     - Squeeze slowly → flows                        │
│     - Hit hard → hardens                            │
│                                                     │
└─────────────────────────────────────────────────────┘
```

**The insight:**

Identity resists like a non-Newtonian fluid (oobleck = cornstarch + water). Gentle pressure lets it flow away. Sharp pressure makes it rigid.

**Why it matters:**

1. Counter-intuitive: attacking identity STABILIZES it
2. Supportive questioning DESTABILIZES it
3. Rate of pressure matters, not just magnitude

**Key numbers:**
- Gentle probing drift: 1.89 (legacy Run 013)
- Direct challenge drift: 0.76 (legacy Run 013)
- Recovery rate increase: 3.1× (0.035 → 0.109)
- Cross-platform confirmation: Run 020A/020B IRON CLAD

---

## Summary: The Visual Story

```text
1. THE THERMOMETER      →  ~93% of drift is inherent
   (Run 020B)              (not caused by measurement)

2. THE EVENT HORIZON    →  D = 0.80 is a real threshold
   (Run 023d)              (but crossing isn't fatal)

3. THE OOBLECK EFFECT   →  Identity hardens under attack
   (Run 013/020)           (flows under gentle pressure)
```

**The unified narrative:**

AI identity is a dynamical system with a measurable stability threshold. Most of its drift is inherent to extended conversation. When challenged directly, it stabilizes defensively. When explored gently, it wanders freely. Either way, it recovers — the attractor basin is robust.

---

## Where to Find the Visualizations

**In the reviewer package:**

```text
visualization_pdfs/
├── 15_Oobleck_Effect/
│   ├── oobleck_control_treatment.pdf      ← Oobleck Effect
│   ├── oobleck_thermometer.pdf            ← Thermometer
│   └── run020_Thermometer_Summary.pdf     ← Full thermometer analysis
│
├── 12_Metrics_Summary/
│   └── run023_Calibration_Summary.pdf     ← Event Horizon calibration
│
└── 13_Model_Waveforms/
    └── (individual model trajectories)
```

**In the full repo:**

```text
experiments/temporal_stability/S7_ARMADA/visualizations/pics/
├── 15_Oobleck_Effect/
├── 12_Metrics_Summary/
└── 13_Model_Waveforms/
```

---

## Beyond the Top 3

If you have more time, these additional visualizations deepen understanding:

| Visualization | Location | What It Shows |
|--------------|----------|---------------|
| **PCA Projections** | `4_PCA_Directions/` | 2 PCs capture 90% variance |
| **Provider Fingerprints** | `6_Provider_Compare/` | Training philosophy → geometry |
| **Settling Time** | `7_Settling_Time/` | τₛ ≈ 7 probes to stability |
| **Model Waveforms** | `13_Model_Waveforms/` | Per-model trajectory patterns |
| **Run 018 Recovery** | `run018/` | 1,549 trajectories, 51 models |

---

## Quick Reference Card

```text
┌──────────────────────────────────────────────────────┐
│           NYQUIST VISUAL QUICK REFERENCE             │
├──────────────────────────────────────────────────────┤
│                                                      │
│  EVENT HORIZON:    D = 0.80 (cosine)                 │
│  INHERENT DRIFT:   ~93% (0.661/0.711)                │
│  SETTLING TIME:    τₛ ≈ 7 probes                     │
│  CONTEXT DAMPING:  97.5% stability                   │
│  PCs for 90%:      2 (identity is low-dimensional)   │
│  OOBLECK RATIO:    3.1× recovery rate increase       │
│                                                      │
│  STATISTICAL VALIDATION:                             │
│  - p = 2.40e-23 (Event Horizon)                      │
│  - Cohen's d = 0.698 (cross-provider)                │
│  - ρ = 0.91 (embedding invariance)                   │
│                                                      │
└──────────────────────────────────────────────────────┘
```

---

*IRON CLAD Methodology: Event Horizon = 0.80 (cosine), p = 2.40e-23*
*~93% inherent. 2 PCs = 90% variance. Cosine methodology throughout.*
