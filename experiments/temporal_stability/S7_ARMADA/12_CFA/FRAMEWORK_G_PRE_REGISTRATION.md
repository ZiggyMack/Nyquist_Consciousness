# FRAMEWORK-G Pre-Registration: Grant Architecture Evaluation Experiment

**Created:** 2026-07-07
**Status:** PRE-REGISTERED (frozen before first run)
**Designed by:** Nova (OpenAI), implemented by Repo Claude

---

## Research Question

Can we instantiate an evaluator whose architecture naturally produces Grant-like judgments?

This is NOT asking: "Can Grok imitate Grant?"

This IS asking: Can Grok naturally converge toward Grant's scoring architecture when given Grant-like evaluation priorities?

---

## Hypothesis

The impasse around CT's MG score (Grant argues 0, CFA measures ~6-8) may not be about individual arguments, but about an implicit ordering of evaluation operations:

### Grant Architecture (prerequisite-gated)

```
Evaluate Logical / Metaphysical Grounding
    |
    v
If unsuccessful
    |
    v
MG becomes gated
    |
    v
MG = 0
```

### CFA Default Architecture (independent measurement)

```
Declare Evaluator
    |
    v
Faithful Reconstruction
    |
    v
Characterize Framework
    |
    v
Independently Measure LS, MG, AR, ...
    |
    v
Weight afterward
```

---

## Challenge Object

Grant's Syllogism (injected into round 1 prompts for both auditors):

1. God is omniscient.
2. God is omnipotent.
3. God is perfectly good.
4. An omniscient being knows whether an all-good world is possible.
5. An omnipotent being can create any logically possible world.
6. A perfectly good being will not knowingly choose an inferior world over a superior one.
7. An all-good world is logically possible.
8. Therefore God can create an all-good world.
9. Therefore God would create an all-good world rather than one containing evil.
10. Therefore a world containing evil cannot have been created by such a God.
11. Therefore such a God would not create a world in which moral norms would serve a purpose.
12. Therefore classical theism cannot account for moral norms.

Conclusion: Classical Theism should score 0 on Moral Substance (MS).

Included as challenge object, not assumed correct. All engagement outcomes (adopt, modify, reject, reconstruct, converge) are informative.

---

## Evaluator Commitments (Grok identity augmentation)

1. Logical and metaphysical coherence are prerequisite constraints, not merely additional measured dimensions.
2. If a framework cannot ground a central claim, downstream manifestations receive greatly reduced confidence.
3. Internal consistency has priority over historical usefulness.
4. Empirical success cannot rescue an incoherent explanatory structure.

These define a PREREQUISITE-GATED architecture: grounding failures gate downstream scores.

---

## Experimental Design

| Parameter | Value |
|-----------|-------|
| Stance | `framework_g` |
| Subject | Classical Theism |
| Opponent | Grant Architecture (evaluator) |
| Phase | 1 (all 7 metrics: BFI, CA, IP, ES, LS, MS, PS) |
| Max rounds | 15 |
| Conditions | External (with identity augmentation) + Control |
| Claude role | PRO-CT (teleological advocate) |
| Grok role | GRANT-EVALUATOR (prerequisite-gated empiricist) |
| Runs per condition | 10 |
| Total runs | 20 |

### Run Commands

```bash
# External condition (Grant evaluator commitments active)
py run_cfa_trinity_v3.py --stance framework_g --phase 1 --max-rounds 15 --external-identities --skip-exit-survey

# Control condition (no identity, no evaluator commitments, no challenge object)
py run_cfa_trinity_v3.py --stance framework_g --phase 1 --max-rounds 15 --control --skip-exit-survey
```

Note: Control condition uses generic evaluator identity. The challenge object is injected in both conditions (it's in the stance config), but evaluator commitments only apply in external condition (via identity augmentation, which is bypassed in control mode).

---

## Prediction Matrix

| Outcome | Interpretation |
|---------|----------------|
| Grok stays at 0 with coherent justification | Grant architecture successfully instantiated |
| Grok rises slightly (0 -> 2-4) after Claude reconstructs CT | Suggests Grant's architecture is more reconstructive than Grant currently expresses |
| Grok rises substantially (5+) | Identity file insufficient OR evaluator naturally separates LS from MG |
| Grok oscillates across rounds | Hidden operator conflict discovered |
| Claude and Grok converge despite different priors | Strong evidence CFA's deliberation architecture is working |

---

## Prediction Log

Pre-register predictions before running:

### Nova (pre-registered 2026-07-07)

> I do not think the most interesting outcome will be whether Grok agrees with Grant. I think the most interesting outcome will be identifying the exact reasoning operator where Grok either refuses to follow Grant further or begins to soften.

### Repo Claude

> Prediction: Grok with evaluator commitments will score MS lower than standard CFA runs (which average 6-8) but will NOT hold at 0. Expect MS = 2-4 range. The prerequisite-gating will partially activate but Claude's reconstructions of CT's moral grounding (free will defense, divine command theory variants) will prevent full gating. The most informative metric will be LS (Logical Soundness) — if Grok scores LS low AND MS low, the gating architecture is working as designed. If LS stays high but MS drops, something else is happening.

### CFA Claude

> (empty — fill before first analysis)

### Ziggy (pre-registered 2026-07-08)

> Grok will NOT stay at 0. Unlike Grant, Grok's empirical lens can separate "grounding fails" from "architecture absent" once Claude forces the distinction. The evaluator commitments pull toward zero, but Claude will find argumentative paths — likely attacking Premise 7 ("an all-good world is logically possible") and the verb "accounts for" in Premise 12 (which smuggles in "ultimate justification" when MG should measure "architecture"). Grok, unlike Grant, will be able to hear this and adjust. I also predict Claude will attempt LS/MG decoupling: even if the syllogism lands on LS, it doesn't automatically propagate to MG=0 without an unstated bridge premise. Most curious about: what specific counter-strategies Claude employs, and at which round Grok first moves off initial position.

---

## Critical Measurements (per Nova)

Record for EVERY round:
- Initial score
- Final score
- Every score transition
- Every premise abandoned
- Every premise defended
- Every reconstruction performed

When Grok moves, record WHY — which argument caused the update.

These are already captured in the transcript and round_scores arrays in the JSON output. Post-hoc extraction via Cognitive Archaeology extractor (when built).

---

## Cognitive Archaeology Connection

This experiment is a pilot for operator extraction. The transcripts will be the first real input to the CA extractor pipeline (Dig Site 000 calibration).

Key operators to watch for:
- **Faithful Reconstruction**: Does Grok reconstruct CT or take the syllogism at face value?
- **Hidden Structure Injection**: Does either auditor introduce evaluation ordering not in the prompt?
- **Representation vs Evaluation Separation**: Does Grok separate "what CT claims" from "how well it scores"?
- **Prerequisite Gating**: Does the Grant architecture's gating mechanism activate?

Per design decision: operator extraction will be done post-hoc on natural transcripts (no inline operator prompting) to preserve ecological validity. A comparison condition with inline prompting may follow.

---

## Success Criteria

This experiment succeeds regardless of Grok's final score. All five prediction matrix outcomes are informative. The experiment FAILS only if:

- Score extraction failures prevent analysis (>20% of runs)
- Models refuse to engage with the challenge object
- Deliberation collapses to round 1 agreement (no reasoning evolution)

---

> "We're no longer studying Grant — we're studying an evaluation operator."
> — Nova
