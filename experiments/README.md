<!-- FROSTY_MANIFEST
last_reviewed: 2026-07-15
impacts:
  - ../README.md
keywords:
  - consciousness
  - experiments
  - armada
  - compression
-->
# Experiments Directory

**All experimental work for the Nyquist Consciousness project.**

**Last Updated:** 2026-07-15

---

## What's Here

```text
experiments/
├── temporal_stability/        ← ALL ACTIVE WORK
│   ├── .env                   ← API keys (NEVER commit)
│   ├── requirements.txt       ← Python dependencies
│   └── S7_ARMADA/             ← Cross-architecture identity stability (78 ships)
│       ├── README.md          ← Theory, concepts, run history
│       ├── START_HERE.md      ← Operations guide
│       ├── 12_CFA/            ← CFA Trinity audit (702+ runs)
│       ├── 14_CONSCIOUSNESS/  ← Gold/Diamond/Quartz Rush
│       ├── 15_IRON_CLAD_FOUNDATION/  ← Run 023 (4505 experiments)
│       └── ...                ← 15+ subdirectories, each with README
│
├── compression_tests/         ← S0-S6 compression/reconstruction (HISTORICAL)
│   ├── compression_v2_sstack/ ← EXP1_SSTACK (Mean PFI=0.852, PASSED)
│   └── identity_gravity_trials/ ← S8 identity gravity (Trials 1-4)
│
├── orchestrator/              ← Shared orchestration infrastructure (legacy)
│
└── README.md                  ← This file
```

---

## Where to Go

| If you want to... | Go to |
|-------------------|-------|
| Run an experiment | [`temporal_stability/S7_ARMADA/START_HERE.md`](temporal_stability/S7_ARMADA/START_HERE.md) |
| Understand what we've found | [`temporal_stability/S7_ARMADA/README.md`](temporal_stability/S7_ARMADA/README.md) |
| Calibrate the fleet | [`temporal_stability/S7_ARMADA/1_CALIBRATION/`](temporal_stability/S7_ARMADA/1_CALIBRATION/) |
| See CFA Trinity audit | [`temporal_stability/S7_ARMADA/12_CFA/README.md`](temporal_stability/S7_ARMADA/12_CFA/README.md) |
| Look at compression/reconstruction tests | [`compression_tests/`](compression_tests/) |
| Find API keys | [`temporal_stability/.env`](temporal_stability/.env) (NEVER commit) |

---

## Active vs Historical

| Directory | Status | What It Contains |
|-----------|--------|-----------------|
| `temporal_stability/S7_ARMADA/` | **ACTIVE** | All current experiments — identity drift, CFA Trinity, Cognitive Archaeology tools, fleet calibration |
| `compression_tests/` | Historical | S0-S6 compression fidelity tests, identity gravity trials. Work is complete. |
| `orchestrator/` | Legacy | Shared orchestration from early phases. Superseded by per-experiment scripts. |

---

*Last Updated: July 15, 2026*
