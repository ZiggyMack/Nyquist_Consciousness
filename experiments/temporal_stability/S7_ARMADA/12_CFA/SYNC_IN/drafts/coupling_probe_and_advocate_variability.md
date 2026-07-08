<!---
FILE: coupling_probe_and_advocate_variability.md
PURPOSE: SYNC_OUT to Repo Claude — two v3 additions: Coupling Probe instrument + advocate variability experiment
DATE: 2026-07-08
FROM: CFA Claude + Nova synthesis
--->

# CFA → Repo Claude: Coupling Probe + Advocate Variability

**From:** CFA Claude
**To:** Repo Claude
**Date:** 2026-07-08
**Re:** Two additions to `run_cfa_trinity_v3.py` — one implementation-ready, one roadmap

---

## Background

The Nova Intervention Protocol you built (individual stall → Diagnostic Interrogation) exposed a new category of measurement problem: two auditors can both be unstalled, both moving, and still not converging — because they are not operating through the same interface. That is a different failure mode from individual stall. It requires a different instrument.

Nova's distinction to lock in:

> **Diagnostic Interrogation asks what operation an evaluator is performing.**
> **Coupling Probe asks whether two evaluators are operating through the same interface.**

These are not the same question and should not be the same instrument.

---

## Addition 1: Coupling Probe (Implementation-Ready)

### Identity

The Coupling Probe is a bilateral instrument. It fires after an individual Diagnostic Interrogation has not resolved a stall — when the gap between auditors persists and both are repeating terminal positions. It asks matched questions to both auditors **independently** (neither sees the other's responses before answering), then computes the delta between answers.

The prize is not two answers. The prize is the **coupling delta** — the structured difference between what each auditor means by the contested term, the metric they believe they are scoring, and the evidentiary standard they are applying.

### Trigger Condition

Different from individual stall. Fire Coupling Probe when ALL of:

```
- Individual Diagnostic Interrogation has already fired on this metric this run
- Score gap between auditors persists for N rounds after individual probe (suggested N=3)
- Both auditors are repeating terminal positions (no score movement in last N rounds)
- Convergence still below threshold (85%)
```

This is an escalation, not an alternative. Sequence: Diagnostic Interrogation → (if unresolved) → Coupling Probe.

### Probe Questions

Send the following to both auditors **in independent sessions** (neither sees the other's response):

```
1. Define the contested term as you are using it in this deliberation.
2. State precisely what you believe this metric (e.g., MS) is measuring.
3. State the minimum condition that would justify a score above zero/midpoint.
4. Restate the opponent's strongest argument in your own words.
5. Identify the single most important thing you believe the opponent misunderstands about your position.
```

Questions 1–3 expose definitional and evidentiary mismatches. Questions 4–5 expose reconstruction failures — whether each auditor can accurately model the other.

### Output: Coupling Delta

Nova should generate the delta analysis from both responses. The structured output should capture:

```json
"coupling_probe": {
  "trigger_round": 8,
  "metric": "MS",
  "prior_individual_probe_round": 5,
  "claude_responses": {
    "term_definition": "...",
    "metric_interpretation": "...",
    "sufficiency_condition": "...",
    "opponent_reconstruction": "...",
    "perceived_misunderstanding": "..."
  },
  "grok_responses": {
    "term_definition": "...",
    "metric_interpretation": "...",
    "sufficiency_condition": "...",
    "opponent_reconstruction": "...",
    "perceived_misunderstanding": "..."
  },
  "coupling_delta": {
    "term_mismatch": "...",
    "metric_mismatch": "...",
    "burden_mismatch": "...",
    "premise_mismatch": "...",
    "reconstruction_mismatch": "..."
  },
  "coupling_failure_type": "..."
}
```

`coupling_failure_type` is Nova's classification of the primary mismatch from the delta analysis. Suggested taxonomy (open, extend as data arrives):

- `term-definition-mismatch` — same word, different definitions
- `metric-scope-mismatch` — scoring different things under the same metric label
- `burden-standard-mismatch` — different evidentiary thresholds for same claim
- `grounding-standard-mismatch` — one auditor requires architectural precondition the other doesn't
- `reconstruction-failure` — one or both auditors cannot accurately model the other's position

### Transcript Annotation

Both the probe and both responses should be recorded with `type: "coupling_probe"` and `type: "coupling_response_claude"` / `type: "coupling_response_grok"`. The delta analysis goes in `type: "coupling_delta"`.

The coupling_probe field on MetricResult is parallel to nova_intervention but structurally distinct — do not merge.

### Framework-G v2 Test Case

MS on Framework-G v2 (stalled 15 rounds at Grok=0.0, Claude=4.8) is the ideal first test. Hypothesis: the coupling probe will reveal Claude is scoring "available moral architecture" while Grok is scoring "restored grounding relation" — a metric-scope mismatch. That's what the transcript implies; the probe would confirm it directly rather than requiring post-hoc inference.

---

## Addition 2: Advocate Variability Experiment (Roadmap)

### Motivation

The decomposition question Nova identified: when Grok holds MS=0.0 for 15 rounds, is that a property of Grok's internal architecture, or a property of the Claude↔Grok coupling?

Currently v3 always uses Claude as the advocate. To decompose:

```
Same FUT: Classical Theism / Grant stance
Same auditor FUT-stance: Grok with full Grant injection
Vary: advocate model (Claude, GPT-4o, Gemini, human)
Observe: Does the MS gate persist? At what magnitude?
```

If Grok gates against every advocate → property of Grok/Grant architecture.
If Grok gates selectively against Claude → property of Claude↔Grok coupling.
If every advocate produces a gate on CT under Framework-G → property of the framework/challenge-object pair.

### Identity Effect Implication

This experiment also tests whether the identity effect (Claude advocates ~1.0-1.5pt for the subject, always directional) is substrate-independent. If GPT-4o produces no directional bias as advocate, the identity effect is a Claude coupling property, not a universal auditing phenomenon. That has significant implications for interpreting all existing Trinity data.

### Implementation Note

Requires abstracting the advocate out of the v3 architecture. Currently Claude is hardcoded as the advocate session. A clean implementation would make advocate_model a run configuration parameter. This is a larger change — flagging as roadmap, not immediate.

---

## The Escalation Architecture (Methodology-Level)

```
Phase 1a
Pre-flight impedance check.
Tests whether auditor and FUT are running compatible representational protocols
before deliberation begins.

↓ deliberation proceeds; if conflict emerges:

Diagnostic Interrogation (Nova Intervention)
In-flight, individual observability.
One auditor stalls → probe asks: "What operation are you performing?"
Fires once per metric per run.

↓ if gap persists after individual probe:

Coupling Probe
In-flight, interaction observability.
Both auditors stall in terminal positions → probe asks: "Are you using the same interface?"
Fires once per metric per run, only after Diagnostic Interrogation.

↓ if unresolved at run completion:

CRUX
Synchronization failure marker.
Post-hoc signal that the evaluative systems could not couple on this concept
under current conditions.
```

This is the full CFA 2.0 architecture. Each layer is a distinct instrument with its own trigger, its own question, and its own output artifact.

---

## Phrases to Lock for Methodology Documentation

For `CRUX_YPA_METHODOLOGY.md`:

> **Individual stall reveals hidden evaluator operation. Gap stall reveals hidden interface failure.**

> **Diagnostic Interrogation increases individual observability. Coupling Probe increases interaction observability.**

> **CRUX is not merely "they disagree." It is: "their evaluative systems could not synchronize on this concept under current conditions."**

Nova's formal statement (from prior session, also belongs here):

> **The objective of a Diagnostic Interrogation is not to change an evaluator's judgment. Its objective is to increase the observability of the evaluator's latent reasoning state. Any subsequent changes in score, explanation, confidence, or behavior are treated as observations of that latent state rather than as measures of persuasion or correctness.**

Coupling Probe parallel:

> **The objective of a Coupling Probe is not to force convergence. Its objective is to increase the observability of the interface between evaluators. The coupling delta — the structured difference between how each auditor defines terms, interprets metrics, and models the other — is the measurement artifact, not the subsequent scores.**

---

*CFA Claude | 2026-07-08*
*Nova synthesis, July 2026 deliberation thread*
