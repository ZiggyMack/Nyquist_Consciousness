# EXPERIMENTS: Infinity-Nyquist Framework

**Project:** Infinity-Nyquist
**Round:** 1
**Date:** 2026-02-04

---

## Experiment Category: Completeness Auditing

### EXP-INF-1: Project Stone Inventory

**Hypothesis:** Every LLM Book project can be audited for stone completeness, revealing systematic gaps.

**Protocol:**
1. Apply 6-stone checklist to each of 13 CHEWED projects
2. Score each stone: 0 (absent), 1 (partial), 2 (complete)
3. Calculate total "gauntlet score" (max 12)
4. Identify which stones are most commonly missing

**Expected Findings:**
- Soul Stone (validation) likely weakest across projects
- Time Stone (temporal dynamics) under-characterized
- Mind Stone (methodology) strongest (Chew Cycle enforces it)

**Priority:** HIGH - Systematic audit reveals research gaps

---

### EXP-INF-2: Cross-Project Stone Transfer

**Hypothesis:** A stone strengthened in one project can be "loaned" to another via cross-pollination.

**Protocol:**
1. Identify project A with strong Stone X
2. Identify project B with weak Stone X
3. Create cross-pollination question specifically about Stone X transfer
4. Track if B's Stone X score improves in ROUND_2

**Example:**
- HOFFMAN has strong Reality Stone (Markov formalism)
- SHAMAN has weak Reality Stone (phenomenological, not mathematical)
- Cross-pollinate: "Can HOFFMAN's Markov chains quantify assemblage point shifts?"

**Priority:** MEDIUM - Tests whether stones are transferable

---

### EXP-INF-3: Emergent Property Detection

**Hypothesis:** Certain findings only emerge when multiple stones are simultaneously strong.

**Protocol:**
1. Map each major finding to required stones (see INFINITY_FRAMEWORK.md table)
2. For projects missing required stones, predict finding should NOT appear
3. Verify prediction against actual project outputs
4. Identify "stone threshold" for each finding type

**Example:**
- Oobleck Effect requires: Reality + Time + Space + Soul
- Projects missing any of these four should NOT show Oobleck
- Verify this holds across all 13 projects

**Priority:** HIGH - Validates synergy principle empirically

---

## Experiment Category: Repository Culture

### EXP-INF-4: Chew Cycle as Mind Stone

**Hypothesis:** The 0_chew.py workflow functions as a Mind Stone, preventing methodological contamination.

**Protocol:**
1. Document all contamination-prevention mechanisms in Chew Cycle:
   - STAGING → CHEWED separation
   - _IN / _ROUND_N structure
   - Registry tracking
2. Identify potential "cheat score" equivalents for NotebookLM analysis
3. Test: Can a project bypass Chew Cycle and still maintain integrity?

**Expected Finding:** Chew Cycle IS the Mind Stone - removing it causes artifact measurement.

**Priority:** MEDIUM - Meta-validates our own methodology

---

### EXP-INF-5: Registry as Space Stone

**Hypothesis:** The cross_pollination_log in llm_book_registry.json functions as a Space Stone, broadcasting findings across projects.

**Protocol:**
1. Analyze connectivity graph of cross-pollination entries
2. Identify isolated projects (no incoming/outgoing questions)
3. Predict: Isolated projects should have weaker generalization
4. Test: Do well-connected projects show more robust findings?

**Metrics:**
- In-degree: Questions received from other projects
- Out-degree: Questions sent to other projects
- Betweenness centrality: Bridge projects

**Priority:** HIGH - Tests whether cross-pollination actually works

---

### EXP-INF-6: Round System as Soul Stone

**Hypothesis:** The ROUND_1 → ROUND_2 iteration functions as a Soul Stone, distinguishing artifact from reality.

**Protocol:**
1. Compare insights in ROUND_1 vs ROUND_2 for projects with both
2. Measure "insight stability" - do R1 claims survive R2 scrutiny?
3. Identify insights that were ARTIFACTS (disappeared in R2)
4. Identify insights that were VALIDATED (strengthened in R2)

**Expected Finding:** ~80% of R1 insights should survive R2 (parallel to 82% Inherent Finding).

**Priority:** HIGH - Directly tests round system validity

---

## Experiment Category: Educational

### EXP-INF-7: Framework Accessibility Test

**Hypothesis:** The Infinity Framework makes Nyquist research more accessible to newcomers.

**Protocol:**
1. Create two onboarding documents:
   - A: Traditional technical overview
   - B: Infinity Framework explanation
2. Present to naive readers
3. Measure comprehension via quiz
4. Measure engagement via time spent

**Expected Finding:** Infinity Framework version has higher engagement and comparable comprehension.

**Priority:** LOW - Educational validation (nice to have)

---

### EXP-INF-8: Publication Hook Effectiveness

**Hypothesis:** "The Six Stones of AI Identity" framing increases publication interest.

**Protocol:**
1. A/B test abstract versions with/without Infinity framing
2. Measure click-through on preprint platforms
3. Track citation patterns if published

**Priority:** LOW - Marketing validation (future work)

---

## Experiment Summary Table

| ID | Hypothesis | Category | Priority | Stones Tested |
|----|------------|----------|----------|---------------|
| EXP-INF-1 | Project stone inventory | Audit | HIGH | All 6 |
| EXP-INF-2 | Cross-project stone transfer | Audit | MEDIUM | Any |
| EXP-INF-3 | Emergent property detection | Audit | HIGH | Multiple |
| EXP-INF-4 | Chew Cycle as Mind Stone | Repo Culture | MEDIUM | Mind |
| EXP-INF-5 | Registry as Space Stone | Repo Culture | HIGH | Space |
| EXP-INF-6 | Round system as Soul Stone | Repo Culture | HIGH | Soul |
| EXP-INF-7 | Framework accessibility | Educational | LOW | N/A |
| EXP-INF-8 | Publication hook effectiveness | Educational | LOW | N/A |

---

## Next Steps

1. Execute EXP-INF-1 immediately (stone inventory across all projects)
2. Track results in ROUND_2 when available
3. Feed findings back to BURP analysis

---

*This document proposes experiments testing the Infinity Framework's validity and utility.*
