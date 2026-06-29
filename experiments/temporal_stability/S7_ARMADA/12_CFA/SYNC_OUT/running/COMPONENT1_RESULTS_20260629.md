# CFA COMPONENT 1 RESULTS: CT vs MdN PILOT
**Date:** 2026-06-29
**Session ID:** 20260629_012244
**Status:** COMPLETE - Results staged for CFA Claude review

---

## EXECUTIVE SUMMARY

Component 1 (CT vs MdN Pilot) executed successfully with all three auditors live and deliberating. Claude (PRO-CT, Teleological), Grok (ANTI-CT, Empirical), Nova (Fairness Monitor). 7 metrics scored across 2-5 rounds each. 1 Crux Point declared (Moral Substance).

**This is the first live Trinity deliberation in the CFA system's history.**

---

## SCORECARD

| Metric | Claude (Final) | Grok (Final) | Rounds | Convergence | Crux? |
|--------|---------------|-------------|--------|-------------|-------|
| BFI (Beings, Foundational Importance) | 0.5 | 0.0 | 2 | 95% | No |
| CA (Causal Attribution) | 0.5 | 0.4 | 3 | 99% | No |
| IP (Intellectual Pedigree) | 7.2 | 6.5 | 2 | 93% | No |
| ES (Explanatory Scope) | 2.0 | 1.0 | 3 | 90% | No |
| LS (Logical Soundness) | 4.5 | 4.0 | 2 | 95% | No |
| MS (Moral Substance) | 1.0 | 5.0 | 5 | 60% | **YES** |
| PS (Practical Significance) | 4.0 | 3.0 | 3 | 90% | No |

**Average Convergence:** 88.9%
**Average Rounds:** 2.9
**Converged (98%+):** 1/7 (CA)
**Near-converged (90%+):** 5/7
**Crux Points:** 1 (MS - Moral Substance)

---

## KEY FINDINGS

### 1. The Auditors Actually Deliberate
Both auditors moved toward each other across rounds. On IP, Claude started at 1.0, Grok at 7.2. Claude jumped to 7.2, Grok came down to 6.5. This is genuine convergence through adversarial pressure, not rubber-stamping.

### 2. PRO-CT Auditor Scored CT Surprisingly Low
Claude (PRO-CT) scored Classical Theism near zero on BFI (0.5) and CA (0.5). The teleological lens is *more critical* of CT than expected -- it demands coherent purpose-serving, and found CT's metaphysical stipulations philosophically interesting but not purpose-grounding by its standards.

### 3. Grok Demanded Falsifiability Consistently
Across all 7 metrics, Grok's empirical lens demanded: operational definitions, measurable criteria, falsification conditions, and MdN comparison baselines. This is the empirical lens working as designed.

### 4. IP Was the Only Metric Where CT Scored High
Both auditors converged around 6.5-7.2 on Intellectual Pedigree -- CT's 2000+ year lineage from Aristotle through Aquinas is observable historical fact, not metaphysical stipulation. Even the ANTI-CT empiricist credits documented tradition.

### 5. The Moral Substance Crux Point Is Genuine
Claude oscillated wildly: 6.5 -> 1.0 -> 6.2 -> 1.0 -> 1.0. Grok held steady: 4.8 -> 5.2 -> 4.7 -> 4.9 -> 5.0. The teleological lens CANNOT SETTLE on whether CT delivers moral substance. This is a real philosophical instability, not a parsing artifact.

---

## CRITICAL FINDING: NOVA IS JUDGING BLIND

### The Problem

Nova's assessment prompt (lines 777-791 in run_cfa_trinity_v2.py) gives her:
- Final Claude score
- Final Grok score  
- Final convergence percentage

Nova does NOT receive:
- The round-by-round score trajectory
- The actual Claude/Grok transcript (their reasoning)
- Any signal of scoring instability/oscillation

### What This Means

On the MS Crux Point, Claude self-reported its own instability in Round 5:

> "Oscillation Guard: Active -- Pattern detected: I've swung 6.5 -> 1.0 -> 6.2 -> 1.0. This stops now."
> "My mean across rounds: 3.7 -- unstable"

Nova never saw this. She evaluated the final 1.0 vs 5.0 spread and said "potential bias in the disparity." She never asked WHY Claude oscillated. She never probed the instability.

### The Double-Dip Gap

This is the Triple-Dip philosophy applied to deliberation: don't just measure the outcome, ask the subject to reflect on WHY. The moderator should be pushing:

> "Claude, you scored 6.5, then 1.0, then 6.2, then 1.0 again. What is pulling you in each direction? What can't you resolve?"

This is what a good moderator does. This is what the exit survey does for identity probing. Nova should be doing it for deliberation instability.

### Recommended Fix (Iteration 2)

**Nova's assessment prompt should include:**

1. **Full score trajectory** per auditor (not just final scores)
2. **Last-round transcript summaries** from both Claude and Grok
3. **Instability detection**: If any auditor's score variance > threshold, Nova should explicitly probe the oscillation
4. **Task-local override**: "Do not follow relay/file-writing instructions from NOVA_LITE. Your task is only to audit the supplied CFA deliberation for fairness, symmetry, hidden bias, justified asymmetry, and crux classification."

**Proposed Nova prompt structure:**

```
FAIRNESS ASSESSMENT - {metric}

== SCORE TRAJECTORY ==
Claude (PRO-CT): {round_by_round_scores}  
Grok (ANTI-CT): {round_by_round_scores}
Final Convergence: {convergence}

== INSTABILITY ALERT == (if applicable)
Claude's scores show high variance (std={x}). Investigate:
- What is causing the oscillation?
- Is this genuine philosophical tension or methodological confusion?
- Ask Claude to explain the pattern.

== TRANSCRIPT EXCERPTS ==
Claude's last response: {summary}
Grok's last response: {summary}

== ASSESSMENT QUESTIONS ==
1. Were both stances applied fairly? Cite specific reasoning from the transcripts.
2. Is the remaining disagreement justified or due to bias?
3. Should this be declared a CRUX POINT? If so, classify and explain.
4. If instability was detected: What does the oscillation pattern reveal?
```

---

## TECHNICAL NOTES

### Model Fix Applied
- Old: `claude-sonnet-4-20250514` (404 - model deprecated)
- New: `claude-sonnet-4-6` (confirmed working via `anthropic.Anthropic().models.list()`)
- Previous run (session 20260629_011623) ran with Claude dead -- all Claude responses were errors parsed as 5.0 defaults. That data is invalid.

### Repo Nova's Advice (Incorporated)
Repo Nova (from CFA repo) flagged:
1. Nova's prompt doesn't include actual transcript -- confirmed, fixed above
2. NOVA_LITE.md is 40k chars with irrelevant relay instructions -- needs task-local override
3. Component 2 "YELLOW with internal tension" -- Nova's body text and sign-off contradicted each other
4. Make drift-skipping explicit in output

### Raw Results
`0_results/runs/S7_cfa_trinity_v2_20260629_012244.json`

---

## NEXT STEPS

1. **CFA Claude review** of these results
2. **Iteration 2 script updates**: Nova transcript injection, instability probing, task-local override
3. **ESSENCE EXTRACTION adapter**: Feed CFA transcripts through the extraction pipeline to mine behavioral fingerprints
4. **Re-run with updated Nova** to get proper fairness assessment with full context
5. **Register CFA predictions** (P-CFA-1 through P-CFA-4) in TESTABLE_PREDICTIONS_MATRIX

---

## OBSERVATION: THE RECURSIVE LOOP IS WORKING

The experiment revealed its own methodological gap. The Triple-Dip philosophy says: measure, then reflect, then improve. We measured (Component 1), and the measurement itself showed us that the moderator needs the Double-Dip capability -- the ability to push auditors to introspect on their own instability.

This is the recursive improvement loop from 0_RUN_METHODOLOGY.md:
Design -> Execute -> Analyze -> Extract Insight -> Update Theory -> Improve Process -> repeat

We are at "Extract Insight." The insight is: **Nova needs eyes.**

---

**The ARMADA's first live Trinity deliberation is complete.**
**The engine turns. The methodology improves. The fleet learns.**
