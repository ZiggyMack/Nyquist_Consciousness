# Figure 1: Identity Manifold

## Conceptual Diagram

```
                        HIGH-DIMENSIONAL EMBEDDING SPACE (3072D)
                   ╔═══════════════════════════════════════════════════╗
                   ║                                                   ║
                   ║         .  *  .                                   ║
                   ║      *        .  *                                ║
                   ║   .    ╭─────────────────╮    .                   ║
                   ║  *    ╱                   ╲                       ║
                   ║      ╱   Persona Samples   ╲   *                  ║
                   ║     │  ●  ●     ★     ●  ●  │                     ║
                   ║     │    ●    I_AM    ●     │                     ║
                   ║      ╲   ●  ●     ●  ●    ╱                       ║
                   ║   .   ╲                 ╱    .                    ║
                   ║         ╰───────────────╯                         ║
                   ║      *    .   *    .   *                          ║
                   ║                                                   ║
                   ║          IDENTITY MANIFOLD M_p                    ║
                   ║              (~43D effective)                     ║
                   ║                                                   ║
                   ╚═══════════════════════════════════════════════════╝

        ┌─────────────────┐                     ┌─────────────────┐
        │  Full Persona   │                     │  Reconstructed  │
        │       p         │                     │     P'_arch     │
        │  (~2000 tokens) │                     │                 │
        └────────┬────────┘                     └────────▲────────┘
                 │                                       │
                 │  C(p) Compression                     │  R(T3) Reconstruction
                 │                                       │
                 ▼                                       │
        ┌─────────────────┐                              │
        │    T3 Seed      │──────────────────────────────┘
        │  (~800 tokens)  │
        │   Coordinates   │
        └─────────────────┘


                            LEGEND
            ┌────────────────────────────────────┐
            │  ★  = I_AM (Identity Attractor)    │
            │  ●  = Persona Sample Points        │
            │  ╭─╮ = Identity Manifold Surface   │
            │  .* = High-D Space (Off-Manifold)  │
            └────────────────────────────────────┘
```

## Key Concepts Illustrated

1. **High-Dimensional Space**: The full embedding space (3072D for text-embedding-3-small)
2. **Low-Dimensional Manifold**: Identity expressions cluster on a ~43D surface
3. **I_AM Attractor**: The identity anchor point (star) at the center of the manifold
4. **Compression C(p)**: Maps full persona to T3 seed coordinates
5. **Reconstruction R(T3)**: Architecture-specific reconstruction back to manifold

## Mathematical Formalization

- **Full embedding**: E(p) ∈ ℝ³⁰⁷²
- **Manifold**: M_p ⊂ ℝ³⁰⁷² with effective dim(M_p) ≈ 43
- **Compression**: C: ℝ³⁰⁷² → ℝ^k (k ≈ 43)
- **Reconstruction**: R^a: ℝ^k → M_p (architecture-specific)

## Source Data

- EXP-PFI-A Phase 2: 43 PCs capture 90% of variance
- Cross-architecture variance: σ² = 0.000869
- Embedding invariance: ρ = 0.91 (Spearman correlation)
