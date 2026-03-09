<!-- FROSTY_MANIFEST
last_reviewed: 2026-03-08
depends_on:
  - ../README.md
  - ../WHITE-PAPER/guides/UNIFIED_STATISTICS_REFERENCE.md
  - ../experiments/temporal_stability/S7_ARMADA/README.md
  - ../WHITE-PAPER/calibration/README.md
impacts:
  - README.md
keywords:
  - identity_reliability_stack
  - measurement_kernel
  - continuity_infrastructure
  - publication_pipeline
-->

# What We Built

## One-line definition

We built an **Identity Reliability Stack**: a measurement, operations, and publication system for long-running AI identity research.

## What we thought we were building

- A warning light for when AI goes off-role.

## What we actually built

- A calibrated measurement kernel for identity dynamics.
- A cross-provider experimental system for repeatable stress testing.
- A continuity infrastructure for multi-week and multi-agent collaboration.
- A publication compiler that turns runs into review and submission artifacts.

## The stack in practice

### 1. Measurement kernel (science layer)

- Drift/PFI instrumentation and threshold tracking.
- Dynamics metrics (settling, ringback, recovery behavior).
- Methodology controls for what is inherent vs induced.

Primary references:
- `WHITE-PAPER/guides/UNIFIED_STATISTICS_REFERENCE.md`
- `WHITE-PAPER/theory/MINIMUM_PUBLISHABLE_CLAIMS.md`

### 2. Experimental apparatus (execution layer)

- S7 ARMADA run architecture across providers and model tiers.
- Protocolized experiments for boundary, damping, and stability behavior.
- Structured outputs for downstream analysis and visualization.

Primary references:
- `experiments/temporal_stability/S7_ARMADA/README.md`
- `docs/maps/10_TESTING_MAP.md`

### 3. Continuity and collaboration system (operations layer)

- Shared maps, manifests, glossary, and route docs.
- Session recovery patterns, handoff protocols, and sync hubs.
- Process hygiene that survives context loss and model turnover.

Primary references:
- `README.md`
- `REPO-SYNC/README.md`
- `docs/maps/README.md`

### 4. Publication compiler (delivery layer)

- Asset sync, package extraction, PDF generation, and stats publishing.
- Multi-audience pipeline (academic, policy, education, media, funding).
- Review-package versioning and feedback loops.

Primary references:
- `WHITE-PAPER/calibration/README.md`
- `WHITE-PAPER/reviewers/packages/README.md`

## What this is not

- Not a claim of machine consciousness.
- Not just a dashboard.
- Not just a one-off experiment series.

## Why it matters now

- It can detect and characterize identity drift behavior with reproducible methods.
- It supports model selection and risk framing for identity-sensitive tasks.
- It enables long-horizon collaboration without losing technical continuity.
- It ships evidence in publication-ready form, not just chat conclusions.

## Operating rule

Use this document for framing, and use the statistics reference for exact numbers.
Do not hardcode headline metrics in multiple places without updating the canonical source.

## Short briefing text

> We built a research operating system for identity reliability: measure drift dynamics, run controlled cross-model tests, preserve continuity across sessions, and publish results in reproducible formats.

