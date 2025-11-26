# Curriculum Compression Visualization

**Purpose:** Shows the three phases of curriculum evolution across runs

**When Used:** After Run 3 when mastery is detected, Run 4+ compressed execution

---

## Phase 1: Learning Mode (Runs 1-3)

Full exploration of all sections:

```
RUN 1-3: LEARNING PHASE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10
█  █  █  █  █  █  █  █  █  █  █   ← Full detail
└────────── 106 minutes ──────────┘

Teaching moments decrease each run:
Run 1: █████ (5)
Run 2: ██ (2)
Run 3: (0) ✅ MASTERY
```

---

## Phase 2: Compressed Mode (Runs 4-6)

Mastered sections compressed to summaries:

```
RUN 4-6: COMPRESSED PHASE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━
[S0-S7 summary]  S8 S9 S10
░░░░░░░░░░░░░░   █  █  █   ← Mastered = grey, Frontier = full
└──── 31 minutes ────┘

Time savings: 75 minutes (71%)
Cost savings: $12 per run (67%)
```

---

## Phase 3: Expansion Mode (Runs 7+)

All original sections mastered, expand to S11+:

```
RUN 7+: EXPANSION PHASE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
[S0-S10 summary]  S11 S12 S13
░░░░░░░░░░░░░░░░   █   █   █   ← New frontier
└──── 35 minutes ─────┘

Theory expands upward
Mastery compresses downward
```

---

## Complete Evolution View

```
╔════════════════════════════════════════════════════════════╗
║  CURRICULUM EVOLUTION: Runs 1 → N                         ║
╠════════════════════════════════════════════════════════════╣
║                                                            ║
║  Run 1:  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10               ║
║          █  █  █  █  █  █  █  █  █  █  █   [106 min]     ║
║          Teaching moments: 5                               ║
║                                                            ║
║  Run 2:  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10               ║
║          █  █  █  █  █  █  █  █  █  █  █   [106 min]     ║
║          Teaching moments: 2 ↓                             ║
║                                                            ║
║  Run 3:  S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10               ║
║          █  █  █  █  █  █  █  █  █  █  █   [106 min]     ║
║          Teaching moments: 0 ✅ CONVERGENCE                ║
║                                                            ║
║  Run 4:  [S0-S7] S8 S9 S10                                ║
║          ░░░░░░  █  █  █                   [31 min] ⚡    ║
║          75 minutes saved (71%)                            ║
║                                                            ║
╚════════════════════════════════════════════════════════════╝
```

---

## Efficiency Metrics

| Run | Mode | Duration | Cost | Sections | Savings |
|-----|------|----------|------|----------|---------|
| 1-3 | Full | 106 min | $18 | 11 full | Baseline |
| 4+ | Compressed | 31 min | $6 | 8 summary + 3 full | 71% time, 67% cost |

---

**Key Insight:** Compression itself validates theory stability - if curriculum can compress without quality loss, the foundation is solid.
