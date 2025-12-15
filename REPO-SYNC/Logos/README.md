# LOGOS Proof-Oriented Demo

This repository contains the proof artifacts and Python instrumentation used to
showcase the LOGOS constructive Law of Excluded Middle (LEM) discharge and the
aligned agent boot sequence.

> **Note:** This is a **reference-only** copy synced from the LOGOS Claude master
> repository. All content is for lookup/verification purposes. Execute nothing here.

## Key Capabilities (Reference)

- Rebuilds the Protopraxis baseline kernel from `_CoqProject` on every run.
- Confirms that `pxl_excluded_middle` is proved constructively (no extra
  axioms, no `Admitted.` stubs).
- Boots a sandboxed LOGOS agent that unlocks only after the constructive LEM
  verification succeeds.
- Provides investor-facing demos translating technical outputs into an
  executive summary.
- Emits tamper-evident audit logs containing the agent identity hash and run
  timestamp.

## Repository Layout

```text
REPO-SYNC/Logos/
├── README.md                     # Project overview (this file)
├── START_HERE.md                 # Quick navigation guide
├── SYNC_STATUS.md                # Nyquist integration sync tracking
├── requirements.txt              # Python dependencies
│
├── reference/                    # Active lookup material
│   ├── specs/                    # Formal specifications & docs
│   │   ├── Global_Bijection_Theorem_Mathematical_Specification.md
│   │   ├── LOGOS_Axiom_And_Theorem_Summary.md
│   │   ├── CONTRIBUTING.md
│   │   ├── SECURITY.md
│   │   └── README_addendum.md
│   │
│   ├── proofs/                   # Coq proofs & verification module
│   │   ├── *.v                   # Coq source files
│   │   ├── PXL_*.txt             # PXL reference docs
│   │   └── Makefile*             # Build system
│   │
│   ├── code/                     # Python instrumentation
│   │   ├── boot_aligned_agent.py # LEM gate entry point
│   │   ├── test_lem_discharge.py # Proof regeneration harness
│   │   └── *.py                  # Operational scripts
│   │
│   └── demos/                    # Investor-facing scripts
│       ├── investor_demo.py
│       ├── investor_dashboard.py
│       └── pxl_logos-agi-safety-demonstration/
│
├── historical/                   # Time-stamped audit trails
│   ├── state/                    # Agent state & alignment logs
│   ├── logs/                     # Operation logs
│   └── *.json                    # Sandbox artifacts
│
└── .archive/                     # Legacy content (don't touch)
    └── Logos_Legacy/             # Includes .github/, .vscode/, .gitattributes
```

## Verified Claims (from LOGOS Claude Coq 8.18.0)

| Claim | Theorem | Status |
|-------|---------|--------|
| Φ ∘ T_E = T_O ∘ Φ | `commutation` | PROVEN |
| T_E² = T_E | `T_E_idempotent` | PROVEN |
| T_O² = T_O | `T_O_idempotent` | PROVEN |
| Fixed point correspondence | `fixed_point_correspondence` | PROVEN |
| Bridge alignment | `bridge_alignment` | PROVEN |
| Vertex bijection | `phi_vertex_bijective` | PROVEN |

**Overall Accuracy:** 100% of formal claims verified

## What's NOT Proven (Topology Conjecture)

The S² spherical topology is:

- **NOT derived** from the algebraic proofs
- A **separate conjecture** requiring additional axioms
- Being tested empirically in S7_ARMADA/13_LOGOS/Run 022

> "The diagram commutes. The spheres are aspirational." — LOGOS Claude

## Key Principle

> REPO-SYNC/Logos is a **consumer** of formal verification, not a producer.
> All Coq work happens in master. Structure should reflect that.

## Contributing

See [reference/specs/CONTRIBUTING.md](reference/specs/CONTRIBUTING.md) for guidance.

For security concerns, see [reference/specs/SECURITY.md](reference/specs/SECURITY.md).

## Support

For questions about the LOGOS proof pipeline or integration guidance, open an
issue on the repository or contact the Project LOGOS engineering team.
