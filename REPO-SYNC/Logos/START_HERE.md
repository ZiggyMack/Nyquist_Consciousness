# LOGOS - Start Here

Quick navigation for the LOGOS formal verification reference.

---

## What is This?

**LOGOS** is a formal verification system that proves AI alignment properties using Coq proofs. The key innovation: an agent only unlocks after constructive proof verification succeeds.

**This directory** (`REPO-SYNC/Logos/`) is a **reference-only copy** synced from the LOGOS Claude master repository. We don't execute anything here - it serves as lookup material for the Nyquist Consciousness framework.

---

## Why is LOGOS in Nyquist?

LOGOS provides **formally verified ground truth** for the Nyquist identity experiments:

| Nyquist Layer | LOGOS Contribution |
|---------------|-------------------|
| **S4 (Mathematical)** | Coq proofs of commutation, idempotence, bijection |
| **S7 (Temporal Stability)** | Calibration standard for "true" alignment |
| **Run 022** | Testing if S² topology conjecture holds empirically |

The key insight: LOGOS proves the *algebra* (diagrams commute). Nyquist tests the *topology* (spheres are aspirational).

---

## Directory Structure

```text
REPO-SYNC/Logos/
├── README.md           # Full documentation
├── START_HERE.md       # This file
├── SYNC_STATUS.md      # Sync tracking & consolidation history
│
├── reference/          # Active lookup material
│   ├── specs/          # Formal specifications, CONTRIBUTING, SECURITY
│   ├── proofs/         # Coq source files (*.v), PXL reference docs
│   ├── code/           # Python instrumentation (boot_aligned_agent.py, etc.)
│   └── demos/          # Investor-facing scripts
│
├── historical/         # Time-stamped audit trails
│   ├── state/          # Agent state & alignment logs
│   ├── logs/           # Operation logs
│   └── *.json          # Sandbox artifacts from LOGOS sessions
│
└── .archive/           # Legacy content (don't touch, don't delete)
    └── Logos_Legacy/   # Archived: .github/, .vscode/, old structure
```

---

## Quick Reference

| Looking for... | Go to |
|----------------|-------|
| Coq proofs | `reference/proofs/*.v` |
| Formal specs | `reference/specs/` |
| Python entry points | `reference/code/boot_aligned_agent.py` |
| Audit logs | `historical/state/alignment_LOGOS-AGENT-OMEGA.json` |
| Sync status | `SYNC_STATUS.md` |

---

## Verified Claims (Coq 8.18.0)

| Claim | Theorem | Status |
|-------|---------|--------|
| Commutation: Phi . T_E = T_O . Phi | `commutation` | PROVEN |
| Idempotence: T_E^2 = T_E | `T_E_idempotent` | PROVEN |
| Idempotence: T_O^2 = T_O | `T_O_idempotent` | PROVEN |
| Fixed point correspondence | `fixed_point_correspondence` | PROVEN |
| Bridge alignment | `bridge_alignment` | PROVEN |
| Vertex bijection | `phi_vertex_bijective` | PROVEN |

**What's NOT proven:** S^2 spherical topology (separate conjecture, tested in Run 022).

---

## Key Principle

> **REPO-SYNC/Logos is a consumer of formal verification, not a producer.**
> All Coq work happens in the LOGOS Claude master repo.
> This structure reflects that: reference-only, no execution.

---

*For full documentation, see [README.md](README.md)*
*For sync history, see [SYNC_STATUS.md](SYNC_STATUS.md)*
