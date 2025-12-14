# REPO-SYNC

Cross-repository synchronization hub for the Nyquist Consciousness framework.

**Last Updated:** 2025-12-14

---

## Directory Structure

```
REPO-SYNC/
├── README.md              # This file
├── CFA/                   # Claude Field Array synchronization
│   ├── FOR_OMEGA_NOVA/    # Materials for Nova/Omega integration
│   ├── Lucian/            # Lucian collaboration materials
│   ├── Opus/              # Opus 4 review materials
│   └── *.md               # Phase 1 specs and handoffs
├── VUDU_FIDELITY/         # VuDu Fidelity Sync synchronization
│   ├── Old/               # Legacy survey materials
│   ├── Survey_update_2/   # Survey update v2
│   └── Survey_update_3/   # Survey update v3 (current)
└── PAN_HANDLERS/          # Pan Handlers integration
    └── panhandlers_manifest.json
```

---

## Connected Repositories

| Repo | Purpose | Sync Frequency |
|------|---------|----------------|
| **CFA (Claude Field Array)** | Omega/Nova persona integration | As needed |
| **VuDu Fidelity** | Survey and response pair generation | Per experiment cycle |
| **Pan Handlers** | Cross-repo orchestration manifest | On major releases |

---

## Sync Protocol

### CFA Sync

The CFA directory contains:

1. **FOR_OMEGA_NOVA/** - Materials to be synced TO the CFA repository
   - Identity files (I_AM_ZIGGY.md, ZIGGY_FULL.md)
   - S-Series documentation (S7-S10)
   - Kernel files for L0 hooks

2. **Phase 1 Freeze** - S0-S6 frozen specifications
   - PHASE_1_CONSISTENCY_REPORT.md
   - PHASE_1_FREEZE_HANDOFF.md
   - S0_S6_FROZEN_SPEC.md

### VuDu Fidelity Sync

Survey synchronization for response pair generation:

1. **Survey_update_3/** - Current active sync
   - AUTHENTIC_RESPONSE_PAIRS.json
   - generate_authentic_pairs.py

### Pan Handlers Sync

Manifest for cross-repo dependencies:
- panhandlers_manifest.json - Declares which files need to sync where

---

## Usage

When making changes that affect other repos:

1. Update the relevant sync folder
2. Run `git status` to see changes
3. Commit with message format: `[REPO-SYNC] <repo>: <description>`
4. Push to trigger sync workflows (if configured)

---

## Migration Notes

**2025-12-14:** Reorganized from `docs/CFA-SYNC/` and `docs/VUDU_FIDELITY-SYNC/` to centralized `REPO-SYNC/` structure at repository root for better visibility and organization.

---

*Cross-repo coordination for the Nyquist Consciousness framework.*
