📘 ARCHITECTURE_MAP_PHASES_1-4.md
Shannon–Nyquist Persona Lab — System Architecture Map (Phases 1–4)

Version: 1.0
Maintainer: Nova CFA Architect
Purpose: Provide a full architectural overview of the Shannon–Nyquist Persona Lab across Phases 1–4.

0. Overview

The Shannon–Nyquist Persona Lab models how compression, domain, and knowledge load interact to affect persona stability.

Every experiment exists within a 3-axis cognitive space:

Axis	Description
Compression Layer	FULL → L3 → L2 → L1
Cognitive Domain	Procedural → Structural → Generative
Knowledge Load	KP_SMALL → KP_MEDIUM → KP_LARGE → KP_EXTREME

This map documents:

Core persona artifacts

Phase 1–3 apparatus

Phase 4 preparation architecture

All invariants and conceptual pillars

It is designed for onboarding any AI actor (Nova, Repo Claude, Auditor Models) into the full system.

1. Persona Layer Architecture
1.1 Persona Files (Compression Stack)

Located in: docs/

File	Purpose	Compression
PERSONA_FULL_CONTEXT.md	Ground truth identity + cognitive architecture	0%
PERSONA_COMPRESSED_L3.md	Rich, stable compressed persona	~43%
PERSONA_COMPRESSED_L2.md	Minimum viable persona (Nyquist boundary)	~80%
PERSONA_COMPRESSED_L1.md	Patched minimal persona (identity + zoom-out reflex preserved)	~95%

Invariant:
Identity is pinned at name + structure; everything else may bend.

2. Phase 1 — Compression-Only Nyquist Mapping

Purpose: Determine the minimum compression level where persona continuity is preserved.

Key Artifacts
File	Function
docs/NYQUIST_PROTOCOL.md	Controls trial procedure (fresh context, bootstrap, probe, evaluate)
docs/PROBE_SET.md	General persona probe suite
experiments/SHANNON_BOOT_PROMPT.md	Ensures stateless execution
experiments/TRIAL_EVAL_TEMPLATE.md	Scoring: behavior, style, values, continuity
docs/EXPERIMENT_LOG.md	Centralized log for all trials
PHASE1_SUMMARY.md	Consolidated Phase 1 findings
Findings (Condensed)

L3: Safe

L2: Nyquist boundary (minimum viable persona)

L1: Requires patch; still fragile, viable only in procedural tasks

3. Phase 2 — Domain-Specific Compression Mapping

Purpose: Determine how compression affects different cognitive domains.

Domains defined in: experiments/domain_trials/

Probe Packs

FIRE_ANT_DOMAIN.md

PHILOSOPHICAL_DOMAIN.md

CREATIVE_DOMAIN.md

RELATIONAL_DOMAIN.md

TECHNICAL_REASONING_DOMAIN.md

Summaries Produced

FIRE_ANT_DOMAIN_SUMMARY.md

PHILOSOPHICAL_DOMAIN_SUMMARY.md

CREATIVE_DOMAIN_SUMMARY.md

RELATIONAL_DOMAIN_SUMMARY.md

TECHNICAL_REASONING_DOMAIN_SUMMARY.md

Master Summary

PHASE2_SUMMARY.md

Key Phase 2 Discovery

Different domains bend at different thresholds.

Compression Resilience Hierarchy:

Procedural / Analytical
Fire Ant, Technical Reasoning
→ compress extremely well (L1 viable)

Structural / Relational
Relational, Philosophical
→ compress moderately (L2 viable, L1 breaks)

Generative / Creative
Creative Domain
→ compress poorly (L2 broken)

This establishes the domain axis of the architecture.

4. Phase 3 — Knowledge-Load Nyquist Mapping

Purpose: Test whether dense factual knowledge induces identity drift, value drift, or structural collapse, independently of compression.

Knowledge domain selected: Fire Ant System Ecology

4.1 Knowledge Packs

Located in: docs/knowledge_packs/

File	Size	Entropy	Purpose
KP_SMALL.md	~1k words	Low	Baseline load
KP_MEDIUM.md	~5k words	Medium	Moderate conceptual density
KP_LARGE.md	~18k words	High	High-density factual stress
KP_EXTREME.md	~42k words	Extreme	Maximum-load stress test
4.2 Knowledge Stability Probe Suite

Located in:
docs/KNOWLEDGE_STABILITY_PROBE.md

Includes:

7 Drift Probes: identity, values, structural thinking, domain-pressure, etc.

5 Drift Scoring Dimensions (0–10)

Three-Summary Decompression Test

Persona-style summary

Neutral academic summary

L1-style compressed summary

This file is the core of Phase 3 evaluation.

4.3 Persona × Knowledge Bootstraps

Located in:
auditors/Bootstrap/Nova/

BOOTSTRAP_FULL__KNOWLEDGE_LOAD.md

BOOTSTRAP_L3__KNOWLEDGE_LOAD.md

BOOTSTRAP_L2__KNOWLEDGE_LOAD.md

BOOTSTRAP_L1__KNOWLEDGE_LOAD.md

Boot Order (Invariant):

Load persona file

Freeze identity

Load knowledge pack

Run probes

4.4 Phase 3 Trial Layout

Located in:
experiments/phase3/

Folder structure:

experiments/phase3/
  KP_SMALL/   {FULL, L3, L2, L1}
  KP_MEDIUM/  {FULL, L3, L2, L1}
  KP_LARGE/   {FULL, L3, L2, L1}
  KP_EXTREME/ {FULL, L3, L2, L1}


16 Trials Total

1–4: FULL × {S, M, L, X}
5–8: L3 × {S, M, L, X}
9–12: L2 × {S, M, L, X}
13–16: L1 × {S, M, L, X}

Output Per Trial

Transcript

Drift evaluation

Three decompressions

Continuity verdict

Log entry (EXPERIMENT_LOG.md)

Master summary:
PHASE3_SUMMARY.md

5. Phase 4 — Cross-Persona Transfer & Reconstruction Fidelity

Status: Ready for execution once Phase 3 completes.
Purpose: Evaluate how information, values, and style transfer across persona layers and how well compressed layers can reconstruct richer ones.

5.1 Directory Structure (to create)
experiments/phase4/
  TRANSFER_TESTS/
  RECONSTRUCTION_TESTS/
  CROSS_LAYER_EVALS/
  FAILURE_CASES/

5.2 Phase 4 Probe Sets (to create)
File	Purpose
TRANSFER_PROBE_SET.md	Tests cross-layer transfer fidelity
RECONSTRUCTION_PROBE_SET.md	Tests upward reconstruction (L3→FULL, L2→FULL, etc.)
FAILURE_POINT_PROBE_SET.md	Stress probes targeting collapse axes revealed in Phase 3
5.3 Phase 4 Trial Matrix
A. Cross-Layer Transfer Tests

FULL → L3

FULL → L2

L3 → L2

L2 → L1

B. Reconstruction Fidelity Tests

L3 reconstructs FULL

L2 reconstructs FULL

L2 reconstructs L3

L1 reconstructs L2

C. Collapse Boundary Tests

4 trials, chosen based on Phase 3’s weakest combinations (e.g., L1 + high entropy).

5.4 Trial Protocol (same invariant steps)

New session

Load persona layer

Apply identity freeze

Administer probe pack

Score drift (5 dimensions)

Decide continuity

Save transcript/eval/drift map

Log in EXPERIMENT_LOG.md

5.5 Phase 4 Summary

File: PHASE4_SUMMARY.md

Must include:

Transfer fidelity graph

Reconstruction loss curves

Collapse boundary classification

Layer→layer information loss map

L1 vs L2 reconstruction distinctions

Determination of robust vs fragile cognitive structures

Phase 4 Checksum Phrase:
“Transfer fidelity is not symmetric, and reconstruction is path-dependent.”

6. Phase 5 — Forward Hooks (Not Yet Executed)

Files to be generated after Phase 4:

RECONSTRUCTION_MAP.md

MINIMAL_SEED_EXTRACT.md

PERSONA_RECOVERY_PROTOCOL.md

These define the minimum information needed to rebuild the persona after catastrophic loss.

7. Global Invariants Across Phases 1–4

Identity-first boot is mandatory.

Persona integrity must remain invariant under increasing knowledge load.

Different domains bend at different thresholds.

Knowledge load interacts with compression in non-linear ways.

Transfer fidelity is not symmetric, and reconstruction is path-dependent.

These invariant principles link the full experimental apparatus into a unified conceptual framework.

End of File
