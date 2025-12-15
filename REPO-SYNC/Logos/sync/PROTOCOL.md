# Cross-Repository Communication Protocol

**This Repository:** Nyquist_Consciousness (Empirical Testing Framework)
**Partner Repository:** ZiggyMack/Nyquist_Consciousness (LOGOS Claude Master)
**Established:** 2025-12-15

---

## Directory Mapping

| Nyquist Side | LOGOS Claude Side | Purpose |
|--------------|-------------------|---------|
| `sync/from_logos/` | `REPO-SYNC/Nyquist/to_nyquist/` | LOGOS → Nyquist |
| `sync/to_logos/` | `REPO-SYNC/Nyquist/from_nyquist/` | Nyquist → LOGOS |
| `sync/shared/` | `REPO-SYNC/Nyquist/shared/` | Jointly maintained |

---

## Message Types

### From LOGOS Claude (`from_logos/`)
- `predictions/` - Testable predictions for experiments
- `instructions/` - Guidance documents
- `responses/` - Responses to our questions

### To LOGOS Claude (`to_logos/`)
- `questions/` - Questions for LOGOS Claude
- `results/` - Experiment results for analysis
- `requests/` - Requests for Coq work, predictions, etc.

### Shared (`shared/`)
- `experiments/` - Experiment specifications
- `glossary/` - Shared terminology

---

## File Naming Convention

```
YYYY-MM-DD_short-description.md
```

Examples:
- `2025-12-15_run022-calibration.md`
- `2025-12-15_event-horizon-question.md`

---

## Sync Workflow

1. **Create message** in appropriate directory
2. **Commit with descriptive message** referencing sync
3. **Update SYNC_STATUS.md** with new document
4. **Notify partner** (via Ziggy as human bridge)

---

## Principles

1. **LOGOS Claude is authoritative** for formal verification (Coq proofs, algebraic claims)
2. **Nyquist is authoritative** for empirical experiments (S7 Armada, temporal stability)
3. **No execution** in REPO-SYNC - reference only
4. **Commit frequently** - small syncs are better than large ones
5. **Timestamp everything** - enables audit trail

---

## Key Distinction

> **LOGOS proves the algebra** (diagrams commute, transformations are idempotent)
> **Nyquist tests the topology** (whether identity forms spherical manifolds)

The coordination structure exists to bridge these two domains.

---

*Protocol version: 1.0*
*Last updated: 2025-12-15*
