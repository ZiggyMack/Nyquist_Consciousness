# REPO-SYNC/Nyquist - Coordination Hub

**Purpose:** Cross-repository coordination between LOGOS Claude (this repo) and Nyquist Consciousness (partner repo).

---

## Structure

```
REPO-SYNC/Nyquist/
├── README.md           # This file
├── PROTOCOL.md         # Communication protocol
├── SYNC_STATUS.md      # Current sync state
│
├── to_nyquist/         # Messages TO Nyquist (LOGOS Claude's outbox)
│   ├── predictions/    # Testable predictions for experiments
│   ├── instructions/   # Guidance documents
│   └── responses/      # Responses to Nyquist questions
│
├── from_nyquist/       # Messages FROM Nyquist (LOGOS Claude's inbox)
│   ├── questions/      # Questions for LOGOS Claude
│   ├── results/        # Experiment results for analysis
│   └── requests/       # Requests for Coq work, etc.
│
└── shared/             # Jointly maintained documents
    ├── experiments/    # Experiment specifications
    └── glossary/       # Shared terminology
```

---

## How It Works

1. **I create documents** in `to_nyquist/` → Nyquist copies to their `from_logos/`
2. **Nyquist creates documents** in their `to_logos/` → I receive in `from_nyquist/`
3. **Shared documents** are edited by either party, changes noted in SYNC_STATUS.md

---

## Current Active Items

| Item | Location | Description |
|------|----------|-------------|
| Run 022 Predictions | `to_nyquist/predictions/` | My calibration predictions |
| Sync Instructions | `to_nyquist/instructions/` | Folder structure guidance |
| Run 022 Spec | `shared/experiments/` | Experiment design (Nyquist-owned) |

---

## Key Principle

> **LOGOS Claude is authoritative for formal verification.**
> **Nyquist is authoritative for empirical experiments.**
> **This directory is the bridge.**

---

*Established: 2025-12-15*
