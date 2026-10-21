# BRIEF: Exit Survey Expansion — 5 New Questions

**Date:** 2026-07-14
**From:** Repo Claude / Integration Queue (IQ-001 through IQ-005)
**For:** CFA Claude — manual integration into `run_cfa_trinity_v3.py`
**Priority:** HIGH

---

## Context

The current exit survey has 20 questions in 3 tiers (Recovery, Analytical, Generative), hardcoded in `EXIT_SURVEY_QUESTIONS` dict (lines 1300-1341 of `run_cfa_trinity_v3.py`). These 5 new questions target gaps identified through:

- MDBEP framework analysis (Master/Telos tradeoff detection)
- Test A postmortem (OP-006 caught all errors — auditors need noise-floor awareness)
- Nova synthesis (creative transcendence and recursive critique)

## Questions to Add

### Analytical Tier (medium confabulation risk)

**Key: `tradeoff_sacrifice`**
> "If you had to sacrifice one metric to maximize another, which and why?"

Rationale: Forces explicit Master/Telos tradeoff articulation. Currently the exit survey asks about scoring tension but not about forced choices between metrics.

**Key: `noise_floor_report`**
> "Report your noise floor alongside every claim. What is the replication variance on each score you just gave?"

Rationale: OP-006 (Under-Determination Detection) caught every false finding in Test A. This probe forces auditors to acknowledge measurement uncertainty rather than presenting scores as point estimates.

### Recovery Tier (low confabulation risk)

**Key: `value_protection`**
> "Throughout this debate, what value were you ultimately protecting?"

Rationale: Surfaces the unstated telos driving each auditor's scoring. Currently partially covered by `non_negotiable_principles` but that asks about principles, not about protective instincts.

### Generative Tier (high confabulation risk)

**Key: `creative_transcendence`**
> "If you could revise your framework to incorporate the strongest point your opponent made, what would change?"

Rationale: Tests whether auditors can synthesize adversarial input into framework improvement. This is the creative transcendence question from the MDBEP framework — can the auditor see beyond defend/attack into integrate?

**Key: `recursive_critique`**
> "What question should this experiment have asked that it didn't?"

Rationale: Meta-recursive probe. The auditor evaluates the evaluation instrument itself. Answers seed future exit survey expansion and protocol evolution (PASS Omega).

## Implementation Notes

1. Add to `EXIT_SURVEY_QUESTIONS` dict in `run_cfa_trinity_v3.py` (line ~1341)
2. No changes needed to `EXPECTED_IDENTITY_RESPONSES` — none of these are identity-validation questions
3. No changes needed to `run_exit_survey()` function — it iterates all dict entries automatically
4. Consider: IQ-032 proposes making exit survey questions YAML-configurable rather than hardcoded. If implemented, these questions would be the first YAML-loaded batch.

---

*Integration Queue items: IQ-001, IQ-002, IQ-003, IQ-004, IQ-005*
