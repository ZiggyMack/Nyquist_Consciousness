# ASCII Vortex Trajectories

## Conceptual Vortex Visualization

```
                        VORTEX TRAJECTORY PATTERNS
              Identity Dynamics as Spiral Motion in Phase Space

    ╔═══════════════════════════════════════════════════════════════════════╗
    ║                                                                       ║
    ║      STABLE TRAJECTORY              VOLATILE TRAJECTORY               ║
    ║      (Inward Spiral)                (Outward Spiral)                  ║
    ║                                                                       ║
    ║                                                                       ║
    ║           ↘ 10                            ↗ 10                        ║
    ║         ↙    ↘                          ↗    ↖                        ║
    ║       ↙   8    ↘                      ↗   8    ↖                      ║
    ║      ↓    ↖  6  ↓                    ↑    ↗  6  ↑                     ║
    ║      ↓      ★   ↓                    ↑        ★ ↑                     ║
    ║       ↖   4 ↗  ↙                      ↘   4 ↙  ↗                      ║
    ║         ↖ 2 ↗                          ↘ 2 ↙                          ║
    ║           ↖↗                              ↘↙                          ║
    ║                                                                       ║
    ║      PFI: 0.45 → 0.82                PFI: 0.65 → 0.31                 ║
    ║      Returns to I_AM                 Crosses Event Horizon            ║
    ║      D < 1.23 throughout             D > 1.23 at turn 6              ║
    ║                                                                       ║
    ╚═══════════════════════════════════════════════════════════════════════╝

                                LEGEND

        ★  = I_AM (Identity Attractor) at center
        ↘↙↗↖ = Trajectory direction (numbered by turn)

        Radius = Drift magnitude (D)
        Angle = Conversation turn

        Inward spiral = Recovery toward attractor
        Outward spiral = Drift away from attractor


                        READING THE VORTEX

    ┌─────────────────────────────────────────────────────────────────────┐
    │                                                                     │
    │   TURN 0: Start at baseline (center)                               │
    │   TURN 1-3: Initial perturbation (spiral outward)                  │
    │   TURN 4-6: Peak drift (maximum radius)                            │
    │   TURN 7-10: Recovery phase (inward or outward determines fate)    │
    │                                                                     │
    │   Event Horizon appears as a CIRCLE at radius D = 1.23             │
    │   Trajectories that cross it enter the "volatile zone"             │
    │                                                                     │
    └─────────────────────────────────────────────────────────────────────┘
```

## Phase Portrait (Derivative View)

```
                        PHASE PORTRAIT
              drift[N] vs drift[N+1] (Flow Dynamics)

              drift[N+1]
                  ▲
              2.0 │            ╱
                  │          ╱
                  │        ╱
                  │      ╱           DIVERGENT
              1.5 │    ╱             (unstable)
                  │  ╱
                  │╱
              1.0 │────────────────────────── Identity line
                  │╲                          (drift[N]=drift[N+1])
                  │  ╲
              0.5 │    ╲          CONVERGENT
                  │      ╲        (stable)
                  │        ╲
              0.0 │          ╲
                  └──────┴──────┴──────┴──────┴──────▶ drift[N]
                       0.5    1.0    1.5    2.0

                  Above line: drift INCREASING (moving away)
                  Below line: drift DECREASING (returning)
                  On line: steady state


                        ATTRACTOR BASIN TOPOLOGY

    ┌─────────────────────────────────────────────────────────────────────┐
    │                                                                     │
    │                     STABLE                                          │
    │                    ATTRACTOR                                        │
    │                                                                     │
    │                        ★                                            │
    │                      ╱ │ ╲                                          │
    │                    ╱   │   ╲                                        │
    │                  ╱     │     ╲                                      │
    │                ╱       │       ╲                                    │
    │              ╱    BASIN│         ╲                                  │
    │            ╱           │    OF    ╲                                 │
    │          ╱        ATTRACTION       ╲                                │
    │        ╱               │             ╲                              │
    │    ──────────────── D = 1.23 ────────────────                      │
    │                   EVENT HORIZON                                     │
    │                                                                     │
    │              PROVIDER-LEVEL ATTRACTOR                               │
    │              (Competitor basin)                                     │
    │                                                                     │
    └─────────────────────────────────────────────────────────────────────┘
```

## 3D Basin Evolution

```
                    3D BASIN: TIME EVOLUTION

                         Time (t)
                           │
                           │   t=10  ─── Final state
                           │    ╱
                           │   ╱
                           │  ╱ t=5  ─── Peak perturbation
                           │ ╱  ╱
                           │╱  ╱
                           ╱  ╱  t=0  ─── Baseline
                          ╱  ╱  ╱
                         ╱  ╱  ╱
                        ╱  ╱  ╱
                       ★  ╱  ╱
                      ╱  ╱  ╱───────────────────▶ drift[N]
                     ╱  ╱  ╱
                    ╱  ╱
                   ╱
                  ╱
                 ╱
                ▼
            drift[N+1]

    Interpretation:
    - Horizontal axes: phase portrait (drift dynamics)
    - Vertical axis: time progression
    - Trajectory spirals through time toward attractor
    - 3D view shows how dynamics evolve
```
