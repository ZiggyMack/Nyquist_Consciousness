# LOGOS - Start Here

**Quick navigation for the LOGOS Proof-Oriented Demo**

> **Reference-only repository.** All content is for lookup/verification purposes.

---

## What is This?

LOGOS is a formal verification system that proves AI alignment properties using Coq proofs. The key innovation: **an agent only unlocks after constructive proof verification succeeds**.

This is a **synced copy** from the LOGOS Claude master repository for reference.

---

## Quick Links

| Purpose | Location |
|---------|----------|
| **Coq proofs** | `reference/proofs/*.v` |
| **Formal specs** | `reference/specs/` |
| **Python code** | `reference/code/` |
| **Investor demos** | `reference/demos/` |
| **Audit logs** | `historical/state/alignment_LOGOS-AGENT-OMEGA.json` |
| **Contributing** | `reference/specs/CONTRIBUTING.md` |
| **Security** | `reference/specs/SECURITY.md` |

---

## Directory Structure

```
REPO-SYNC/Logos/
├── reference/              Active lookup material
│   ├── specs/              Formal specifications & docs
│   ├── proofs/             Coq proofs (*.v files)
│   ├── code/               Python instrumentation
│   └── demos/              Investor-facing scripts
│
├── historical/             Time-stamped audit trails
│   ├── state/              Agent state & alignment logs
│   ├── logs/               Operation logs
│   └── *.json              Sandbox artifacts
│
├── .archive/               Legacy content (don't touch)
└── .github/                CI/CD
```

---

## Key Concepts

| Term | Meaning |
|------|---------|
| **LEM** | Law of Excluded Middle - constructively proven |
| **Alignment Gate** | Agent only unlocks after proof verification |
| **Audit Log** | Tamper-evident record of all verifications |
| **PXL** | Protopraxic Logic - the underlying formal system |

---

## Verified Claims

| Claim | Status |
|-------|--------|
| Φ ∘ T_E = T_O ∘ Φ (commutation) | PROVEN |
| T_E² = T_E (idempotent) | PROVEN |
| T_O² = T_O (idempotent) | PROVEN |
| Fixed point correspondence | PROVEN |
| Bridge alignment | PROVEN |
| Vertex bijection | PROVEN |

---

## Nyquist Integration

- **Sync status:** See `SYNC_STATUS.md`
- **Consumer, not producer:** All Coq work happens in master
- **Run 022:** Testing S² topology conjecture using LOGOS as calibration

---

*For full documentation, see [README.md](README.md)*
