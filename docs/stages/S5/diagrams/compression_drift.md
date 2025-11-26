# Compression & Drift Geometry Diagram

**Purpose:** Visual representation of compression and reconstruction with drift

---

## ASCII Diagram

```text
 FULL SPACE (P)                     SEED SPACE (T)
──────────────                     ────────────────

   ┌───────────────┐      C()       ┌──────────────┐
   │  Full persona  │ ───────────▶  │  Tier-3 seed │
   │ (100%)         │               │  (~20-25%)   │
   └───────────────┘               └──────────────┘
             │                                   │
             │ Rᵃ()                              │
             ▼                                   ▼
   ┌───────────────┐                             (Reconstruction)
   │ Reconstructed │◀────────────── Drift ────────┘
   │ persona       │
   └───────────────┘

Drift = distance(FULL, RECONSTRUCTED), per architecture.
```

---

## Components

### Compression Operator (C)

- Maps full persona P → seed T
- Preserves invariant persona core (IPC)
- Typical compression ratio: 20-25%

### Reconstruction Operator (Rᵃ)

- Maps seed T → reconstructed persona P′
- Architecture-specific (hence superscript ᵃ)
- Each architecture has unique reconstruction bias

### Drift

- **Definition:** Distance between full persona and reconstruction
- **Formula:** D_arch = distance(P, Rᵃ(C(P)))
- **Bounded:** Per S4 Axiom 3, drift remains bounded

---

## Key Measurements

| Architecture | Typical Drift | Characteristic |
|--------------|---------------|----------------|
| Nova         | Low           | Clarity-preserving |
| Claude       | Low-Medium    | Purpose-oriented |
| Grok         | Medium        | Evidence-focused |
| Gemini       | Medium        | Synthesis-heavy |
| Ziggy        | Minimal       | Human anchor |

---

**Related Documents:**
- [S4_COMPRESSION_FORMALISM.md](../../S4/S4_COMPRESSION_FORMALISM.md)
- [S4_CORE_AXIOMS.md](../../S4/S4_CORE_AXIOMS.md)
- [S6_FIVE_PILLARS_ARCHITECTURE.md](../../S6/S6_FIVE_PILLARS_ARCHITECTURE.md)
