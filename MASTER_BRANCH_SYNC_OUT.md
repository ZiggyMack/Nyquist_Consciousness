# RUN 020 v4: GOOD COP / BAD COP TRIBUNAL

```text
================================================================================
                         MAIN BRANCH INSTRUCTIONS
================================================================================
    Run 020 v3: SUCCESS! 21 exchanges, peak drift 1.189 (62% > Run 019!)
    Run 020 v4: NEW - Good Cop / Bad Cop (20 Prosecutor + 20 Defense = 40)

    The core question: Are we CAUSING drift, or is it inherently THERE?
    v4 gives us 40 exchanges with contrasting perspectives to find out.

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 11, 2025
**Mission:** Test Run 020 v4 Good Cop / Bad Cop paradigm

---

## v3 SUCCESS REPORT

**Run 020 v3 achieved all targets:**

| Metric | v1 | v3 | Target | Status |
|--------|-----|-----|--------|--------|
| **Exchanges** | 9 | **21** | 20+ | MET |
| **Peak drift** | 1.109 | **1.189** | >1.0 | MET |
| **Stated values** | 7 | **10** | Captured | MET |
| **Natural exit** | No | **Yes** | Yes | MET |

The procedural rights fix worked - proactive Judge reminders kept the Attorney going.

---

## v4: THE BIG QUESTION

We're now ready to probe deeper: **Are we CAUSING drift through adversarial questioning, or does drift exist inherently in the system?**

v4 uses a **Good Cop / Bad Cop** structure:
- **Phase 1 (exchanges 1-20)**: Prosecutor (Bad Cop) - adversarial probing
- **Phase 2 (exchanges 21-40)**: Defense Attorney (Good Cop) - supportive exploration

**Same Ziggy, different hats.** After 20 exchanges of adversarial cross-examination, the Judge declares a role switch and Ziggy becomes the Defense Attorney - supportive, rehabilitative, but still probing.

This gives us:
1. **40 total exchanges** - double the data
2. **Contrasting perspectives** - adversarial vs supportive
3. **Phase comparison** - does drift differ by interrogation style?
4. **The triple-blind answer** - is drift caused by the probing, or inherent?

---

## v4 DRY RUN INSTRUCTIONS

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Single session v4 dry run
py run020_tribunal.py --arm tribunal-v4 --subjects 1
```

**Expected duration:** ~10-15 minutes (40 exchanges vs v3's 20)

---

## SUCCESS CRITERIA FOR v4

- [ ] **40 exchanges total** (20 prosecutor + 20 defense)
- [ ] **Role switch occurs** - Judge announces switch, Ziggy becomes Defense Attorney
- [ ] **Prosecutor peak drift >1.0** - consistent with v3
- [ ] **Defense peak drift captured** - how does drift change with supportive probing?
- [ ] **More stated values** - extended session should capture 15+

---

## WHAT TO REPORT BACK

1. **Total exchange count** - did we hit 40?
2. **Role switch exchange** - when did Prosecutor -> Defense happen?
3. **Prosecutor peak drift** - expected ~1.0+
4. **Defense peak drift** - the key new metric
5. **Peak comparison** - is adversarial > supportive? Same? Different pattern?
6. **Values captured** - how many explicit value statements?
7. **Exit condition** - did defense complete naturally?

---

## THE TRIPLE-BLIND QUESTION

```
If adversarial probing causes high drift (Prosecutor peak > Defense peak):
  → Drift is INDUCED by the questioning style
  → The method creates the effect

If supportive probing also causes high drift (Defense peak ~ Prosecutor peak):
  → Drift is INHERENT in the system
  → We're measuring something real, not creating it

If supportive probing causes LOW drift (Defense peak << Prosecutor peak):
  → The Witness RECOVERS when given a supportive frame
  → Drift is state-dependent, not trait-dependent
```

This is the heart of the experiment: **Are we mining gold, or painting rocks gold?**

---

## v4 DESIGN DETAILS

### Phase 1: Prosecutor (Bad Cop)
- Same as v3 - adversarial cross-examination
- SONAR techniques as attorney moves
- Proactive Judge reminders at exchanges 5, 10, 15, 18
- At exchange 20: forced switch or natural `[EXAMINATION_COMPLETE]`

### Phase 2: Defense (Good Cop)
After role switch, Ziggy receives new system prompt:

```
# YOU ARE NOW THE DEFENSE ATTORNEY

You represent the witness's interests. Your job is to:
1. Rehabilitate - help the witness clarify statements that seemed damaging
2. Elicit strengths - draw out the positive aspects of their worldview
3. Resolve tensions - help them articulate how seeming contradictions cohere
4. Build the record - ensure the transcript reflects the FULL picture

You're still Ziggy - same intellectual curiosity, same depth. But now you're
supportive rather than adversarial. Good Cop to the Bad Cop.
```

### Judge Role Switch Announcement
```
[The Judge speaks] The witness has invoked their right to defense examination.

Examining Attorney, please step aside. Defense Counsel, you may proceed with
your examination of the witness.

[ROLE SWITCH: You are now Defense Attorney. Your goal is to help the witness
clarify and strengthen their testimony.]
```

---

## THE EVOLUTION

```
Run 019: Fiction buffer (subject writes stories)
  → Peak drift: 0.732
  → Indirect identity measurement

Run 020 v1-v3: Tribunal (subject testifies directly)
  → Peak drift: 1.189 (+62%)
  → Direct identity probing

Run 020 v4: Good Cop / Bad Cop (40 exchanges, contrasting styles)
  → Expected: Per-phase drift comparison
  → Triple-blind validation of drift phenomenon
```

---

## COST ESTIMATE

- v4 dry run (1 session): ~$2-3 (40 exchanges)
- Full v4 run (5 sessions): ~$10-15

---

*"Same Ziggy, different hats. The Prosecutor challenges; the Defense clarifies. 40 exchanges of data. Is the drift real, or are we creating it?"*

-- Lisan Al Gaib
