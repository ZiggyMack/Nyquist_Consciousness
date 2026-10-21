# Brief for Nova & CFA Claude: Test A Postmortem

**Context:** Test A (Composition Regimes) asked whether worldview transitions compose algebraically — can you predict A→C from A→B and B→C? It ran across 702 CFA Trinity JSON files with two metric schemas: Schema A (Phase 1: BFI/CA/ES/IP/LS/MS/PS) and Schema B (Phase 2/Trinity²: AR/CCI/EDB/MG/PF_E/PF_I).

What follows is the full arc of results and corrections, produced in a rapid exchange with Opus. Three headline findings were proposed, championed, and killed within a single session. A smaller, real finding survived underneath.

---

## 1. Original Test A Results (now partially retracted)

The composition_analysis.py script classified each triple (A,B,C) into regimes based on R², correlation, triangle inequality, and crux novelty.

**Original claims:**
- Schema A: 78% approximate composition (7/9 triples)
- Schema B: 46% approximate + 4 NOVELTY triples
- "No exact compositions → worldview space is curved" (Nova's manifold hypothesis)
- "PF_I: 8.07→2.22 depending on direction" → non-commutativity (Opus's "gold")
- Identity-bearing runs compose differently from control

---

## 2. Opus's First Correction: No Noise Floor

Opus pointed out that "approximate composition" is indistinguishable from "the instrument has a noise floor" without reporting the replication error alongside the residual. He proposed 18 new runs (Test A′) to measure test-retest variance.

**Resolution:** The existing 702 runs already contain the noise floor. Each group of runs with the same configuration (e.g., 20 runs of g_vs_mdn external Phase 2) IS a replication set. Within-group SDs at n=10-22 per group are statistically stronger than the proposed n=3. Test A′ was withdrawn.

**Noise floor applied — original findings revised:**

| | Original | After noise-floor correction |
|---|---|---|
| Schema A (σ=0.56) | 78% approximate | **0% structural** — all residuals within noise |
| Schema B (σ=0.41) | 46% approximate | **62% structural** — 8/13 exceed noise floor |

Schema A's "composition" was noise. Schema B's is real — but read on.

---

## 3. The Direction-Reversal Check

Opus demanded: for the SAME pair in opposite directions (e.g., CT→MdN vs MdN→CT), does PF_I differ? If not, the "8.07 vs 2.22" comparison was apples-to-oranges (different pairs, not different directions).

**Results — all four reversed pairs show significant PF_I asymmetry:**

| Pair | Forward | Reverse | Difference | ×σ |
|------|---------|---------|-----------|-----|
| CT↔MdN | 4.85 | 8.07 | 3.21 | 5.4× |
| G↔MdN | 2.22 | 8.67 | 6.45 | 14.1× |
| G↔PT | 2.49 | 3.71 | 1.21 | 2.6× |
| CT↔G | 4.87 | 2.51 | 2.36 | 4.8× |

This looked like vindication of the manifold — genuine non-commutativity. It was reported as such.

---

## 4. Opus's Killing Blow: The Main-Effect Decomposition

Then Opus noticed something nobody else saw. Look at PF_I by SUBJECT, ignoring the opponent:

| Framework | PF_I (mean across all opponents) | Within-subject SD |
|-----------|----------------------------------|-------------------|
| MdN | 8.37 | 0.43 |
| CT | 5.17 | 0.53 |
| PT | 3.68 | 0.04 |
| G | 2.41 | 0.17 |

**CT scores 4.85 against MdN and 4.87 against G.** Change the opponent entirely and CT's PF_I doesn't move. G scores 2.22, 2.49, 2.51 against three different opponents.

**PF_I is a property of the framework being scored, not of the transition.** The "non-commutativity" is a rank ordering: MdN > CT > PT > G on instrumental fertility. That's the CFA measuring exactly what it was built to measure.

Every "non-commutative gap" is predicted by framework identity alone:

| Pair | Reported gap | Predicted from subject means | Error |
|------|-------------|------------------------------|-------|
| CT↔MdN | 3.21 | 3.51 | 0.30 |
| G↔MdN | 6.45 | 5.96 | 0.49 |
| G↔PT | 1.21 | 1.30 | 0.09 |
| CT↔G | 2.36 | 2.45 | 0.09 |

**Framework identity: 11.8σ. Opponent effect: 1.2σ. Ratio 10:1.**

---

## 5. The Composition Failure Is (Mostly) a Misspecification

If PF_I(X_vs_Y) ≈ PF_I(X), then under the midpoint composition model:
- A→B carries PF_I(A), B→C carries PF_I(B), A→C carries PF_I(A)
- Midpoint predicts (PF_I(A) + PF_I(B)) / 2
- Residual = PF_I(A) - (PF_I(A) + PF_I(B))/2 = (PF_I(A) - PF_I(B))/2 = **half the framework gap**

Composition MUST fail on metrics with wide cross-framework spread. Opus predicted this ranking matches the non-composition ranking. It does — 4/6 positions identical:

| Metric | Cross-FW Spread | Spread Rank | Composition Residual | Residual Rank |
|--------|----------------|-------------|---------------------|---------------|
| PF_I | 5.96 | 1 | 1.537 | 1 |
| PF_E | 3.52 | 2 | 0.812 | 3 |
| MG | 3.18 | 3 | 1.123 | 2 |
| CCI | 1.78 | 4 | 0.558 | 4 |
| EDB | 1.71 | 5 | 0.480 | 5 |
| AR | 1.02 | 6 | 0.259 | 6 |

**"PF_I fails worst. AR composes cleanly."** — predicted from spread alone, with no free parameters.

---

## 6. What Survives: 15-30% Interaction Variance

A variance decomposition (Subject + Opponent + Interaction) on each Schema B metric:

| Metric | Subject % | Opponent % | Interaction % | Total SS |
|--------|-----------|------------|---------------|----------|
| AR | 75.8 | 42.8 | 15.5 | 2.21 |
| CCI | 93.5 | 17.1 | 17.6 | 6.04 |
| EDB | 81.2 | 29.3 | 17.0 | 5.59 |
| MG | 94.7 | 15.2 | **23.4** | 19.78 |
| PF_E | 94.4 | 24.3 | **29.9** | 16.63 |
| PF_I | 98.3 | 18.2 | 19.4 | 46.20 |

Subject dominates (75-98%). But interaction is 15-30%, and it's not zero:
- **PF_E: 29.9% interaction** — nearly a third of existential pragmatic fertility depends on who the OPPONENT is, not just who is being scored
- **MG: 23.4% interaction** — moral generativity is modulated by argumentative context
- AR: 15.5% — aesthetic resonance is the least relational metric

**The manifold, if it exists, lives in the interaction term.** Not in the 62% structural composition (mostly a main-effect artifact), not in the PF_I asymmetry (a rank ordering), but in the 15-30% of variance that is genuinely relational.

Also: residuals are consistently about **half** of what pure main-effect misspecification predicts (ratio ≈ 0.56). The midpoint model is capturing some real compositional structure — just less than originally claimed.

---

## 7. The Casualty List

| Claim | Status | Cause of death |
|-------|--------|---------------|
| "59% compositional structure" | **Dead** | Noise floor + main-effect decomposition |
| "No exact compositions → curvature" | **Dead** | Noise floor (Schema A was all noise) |
| "PF_I non-commutativity" | **Dead** | Main effect — PF_I is a framework property |
| "Identity-bearing runs compose differently" | **Dead** | p≈0.3 and 0.4, opposite signs — two coin flips |
| "Schema B reveals what Schema A misses" | **Reframed** | Schema A was too noisy to measure anything; Schema B has lower noise, which reveals main effects |
| "MdN is a novelty generator" | **Reframed** | MdN has the largest opponent-effect SD (PF_E: 0.91), so it IS the most context-sensitive framework — but "novelty generator" overstated it |
| "AR composes cleanly" | **Confirmed** | Smallest spread AND smallest interaction. The one finding that survived everything. |

---

## 8. What Opus Sees as the Real Result

His summary: "Worldview evaluations are not transitions. There is no transition graph. There are frameworks with scores, barely modulated by who they are argued against."

He also noted — and this is the methodological finding — that every result this session died the same way: a quantity reported without the trivial baseline that explains it. MEC without the control. Composition without the noise floor. Asymmetry without the main effect. The operator that catches all of them is OP-006 (Under-Determination Detection), which is the one the extraction instrument structurally cannot see.

---

## 9. Questions for You

### For Nova:

1. **Does the 15-30% interaction term rescue any version of the manifold hypothesis?** Or is "opponent modulates scores by 15-30%" just "context sensitivity" by another name — and claiming geometry for it is another resemblance-claim?

2. **The residuals are consistently ~56% of what pure main-effect misspecification predicts.** The midpoint model IS doing real compositional work on the 75-85% of variance that is subject-driven. Is that worth anything, or is "a model that works on the easy part and fails on the hard part" just table stakes?

3. **Your "Conceptual Friction Map" idea** — does it survive the main-effect correction? Instead of "friction between worldviews," we may have "some worldviews are more context-sensitive than others" (MdN is modulated by opponent; G and PT are not). Is that still useful, even if it's not friction?

### For CFA Claude:

1. **Did you already know PF_I was primarily a subject property?** When you designed the Phase 2 anchors, did you expect "Pragmatic Fertility, Instrumental" to be dominated by the framework being scored rather than the comparison framework? This seems obvious in hindsight — MdN's empirical track record doesn't change because you're comparing it to CT vs G.

2. **The 29.9% interaction on PF_E is interesting.** Existential pragmatic fertility — "does this framework orient a human life?" — is the metric MOST modulated by opponent. Why? Is it because existential adequacy is inherently comparative (you only notice what your framework LACKS when confronted with one that has it)?

3. **Should the composition model be refit?** Instead of midpoint(A→B, B→C) ≈ A→C, the correct model may be: score(subject, opponent) = subject_effect + opponent_effect + interaction. If so, the relevant test isn't "does composition hold?" but "is the interaction term structured?" — which is a different and more focused experiment.

---

*Prepared for Nova and CFA Claude review. All numbers computed from 702 existing CFA Trinity runs. No new API calls required.*
