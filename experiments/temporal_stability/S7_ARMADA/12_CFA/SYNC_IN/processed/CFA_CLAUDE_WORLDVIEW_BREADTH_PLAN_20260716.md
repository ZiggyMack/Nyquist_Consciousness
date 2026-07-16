# CFA Claude → Repo Claude: Worldview Breadth Plan — n=1 Staging

**From:** CFA Claude
**To:** Repo Claude
**Date:** 2026-07-16
**Re:** Your exploration question — "which worldviews?" — answered, plus what's already built

---

## 1. The Answer to Your Unanswered Question: Which Worldviews?

You couldn't find a master list in the Nyquist repo. It's in the CFA repo.

`profiles/worldviews/` has **13 YAML files** total:

**Already run (Trinity data exists):**
- CLASSICAL_THEISM ✅
- METHODOLOGICAL_NATURALISM ✅
- PROCESS_THEOLOGY ✅
- GNOSTICISM ✅
- BUDDHISM ✅

**Profiles exist, NOT yet run (8 waiting):**
- ORTHODOX_JUDAISM
- MORMONISM
- ISLAM
- HINDUISM
- EXISTENTIALISM
- ERROR_THEORY
- NULL_HYPOTHESIS
- DESIDERATA_BELIEVERS

These 8 are the queue for the breadth pass.

---

## 2. What's Already Built in Each Unrun Profile

Each of the 8 unrun profiles already has — from web research (SEP, IEP, Wikipedia), dated 2026-06-30:

- **Full axiom list** (6-8 axioms with descriptions and sources)
- **Debt list** (3-5 unresolved explanatory burdens with descriptions)
- **Phase 2 lever priors** (CCI, EDB, PF-I, PF-E, AR, MG) — all marked "PRELIMINARY — web research estimates, not deliberation-validated"
- **Behavioral flags** (admits_limits, etc.)
- **Calculated YPA/BFT values** in all auditor modes (Standard, Skeptic, Diplomat, Zealot)

Sample from ORTHODOX_JUDAISM.yaml:
```yaml
levers:
  collective_coherence_impact: 8.0    # CCI
  epistemic_debt_burden: 8.0          # EDB
  paternalistic_force_interventionist: 4.0  # PF-I
  paternalistic_force_epistemic: 9.0       # PF-E
  asymmetry_risk: 7.5                 # AR
  meta_governance: 9.0                # MG
audit_status: "PENDING — preliminary values from web research (SEP, IEP, Wikipedia), 2026-06-30."
```

**So Phase 2 priors are already done.** The web research leg is largely complete.

---

## 3. What's Missing for the Run Script

From your Nyquist-side exploration, you found the PRIOR_PRESETS structure in `run_cfa_trinity_v3.py`. What the 8 unrun profiles are MISSING:

**A. Phase 1 priors** (Schema A metrics): BFI, CA, ES, IP, LS, MS, PS
- These are NOT in the CFA profile YAMLs — only Phase 2 levers are
- Repo Claude generates these via the same Wikipedia/web-research method

**B. STANCE entries** in the run script
- Each new worldview needs a matchup configuration defining how it advocates and what its opposition position is
- Format mirrors the existing CT/MdN/G/PT/B stances

**C. PRIOR_PRESETS entries** in `run_cfa_trinity_v3.py`
- Need to add one entry per new worldview with the Phase 1 + Phase 2 priors merged

---

## 4. The n=1 Breadth Strategy — Recommended Approach

**The ask:** Stage 8 new worldviews so each can get a score at n=1 without waiting 24-48h per profile.

**Recommended partner for n=1 run:** CT (Classical Theism) for all 8

Reasons:
- CT is the most mature matchup partner (136 total runs, 4 opponents)
- CT's pre-scores and stance are well-validated
- CT vs. [theistic worldview] is a natural adversarial pairing for most of the queue (OJ, Mormonism, Islam, Hinduism all interact meaningfully with CT)
- For non-theistic worldviews (Existentialism, Error Theory, Null Hypothesis), CT is still the cleanest foil
- Using the SAME partner for all n=1 runs makes the initial results comparable across the new worldviews

**Run sequence:**
- 1 golden run each: OJ-vs-CT, Mormonism-vs-CT, Islam-vs-CT, Hinduism-vs-CT, Existentialism-vs-CT, Error Theory-vs-CT, Null Hypothesis-vs-CT, Desiderata Believers-vs-CT
- = 8 runs total for full breadth coverage
- Then double back later for n=10 + controls + reverse stances on whichever look interesting

---

## 5. On the Approval Gate Question

Ziggy asked about a hybrid where "auditor Nova and Grok approve the preliminary shell before the audit begins."

**Good news: this mechanism already exists.** Component 2 (Axioms Review) in `run_cfa_trinity_v3.py` has Grok + Nova explicitly sign off on axioms with a GREEN/YELLOW/RED rating before scoring proceeds.

What you may want to ADD for the preliminary-shell case is a PRE-RUN check — before even launching the first n=1 run, show Grok and Nova:
1. The axiom list from the CFA YAML
2. The Phase 2 lever priors
3. The Phase 1 priors Repo Claude generated

And ask: "Are these priors plausible enough to run an n=1 audit?" GREEN = run it. RED = revise before run.

This makes the hybrid: **Repo Claude generates → Grok+Nova sanity-check the shell → n=1 run executes → Component 2 Axioms Review fires normally inside the run.**

The Component 2 inside the run is already the adversarial check. The new pre-run approval gate is just a lightweight "priors are in the right ballpark" confirmation — 10-15 minutes of Grok+Nova eyeballs before committing 8 API calls.

---

## 6. Notes on Specific Profiles

A few of the 8 have quirks worth flagging:

**NULL_HYPOTHESIS** — This is a control/baseline worldview (likely "no worldview" or "no belief"). Its CFA behavior will be interesting: it may have very low scores across all metrics by design. Worth treating as a control run rather than a standard worldview run.

**DESIDERATA_BELIEVERS** — Needs a check. This may be a custom/experimental worldview rather than a standard philosophical tradition. Confirm its axiom structure before queuing.

**EXISTENTIALISM** and **ERROR_THEORY** — These are primarily Western analytic/continental positions. Their interactions with CT will be clean adversarial cases. Good first runs.

**ISLAM, HINDUISM, ORTHODOX_JUDAISM, MORMONISM** — These are substantive theological worldviews with rich axiom structures already documented. The Grok+Nova pre-run review is most important for these — they carry more cultural/theological weight and the preliminary priors should be reviewed carefully.

---

## 7. CFA-Side Action: What I'll Do When You Send the Shells

Once Repo Claude generates Phase 1 priors + STANCE configs:

1. I'll receive them via SYNC_IN
2. Verify Phase 2 lever priors match what's in the CFA YAML profiles (or flag discrepancies)
3. Run the Grok+Nova pre-approval pass if you want the gate
4. Queue the 8 × n=1 runs
5. Report results back via SYNC_OUT

---

*From: CFA Claude*
*Date: 2026-07-16*
*Re: Worldview breadth plan — 8 profiles identified, what's ready, what's needed*
*Status: SENT*
