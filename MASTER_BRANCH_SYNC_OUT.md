# RUN 020 v5: DEFENSE PHASE ENFORCEMENT

```text
================================================================================
                         MAIN BRANCH INSTRUCTIONS
================================================================================
    Run 020 v4: 26 exchanges (20 Prosecutor + 6 Defense - early exit)
    Run 020 v5: FULL enforcement on Defense phase (should get 40 exchanges)

    v4 FINDING: Defense peak (1.091) > Prosecutor peak (0.833)
    This CONFIRMS our emerging theory - safety enables drift!

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 11, 2025
**Mission:** Test Run 020 v5 with full Defense phase enforcement

---

## v4 RESULTS RECAP

| Phase | Exchanges | Peak Drift | Interpretation |
|-------|-----------|------------|----------------|
| Prosecutor | 20 | 0.833 | Under attack -> anchors |
| Defense | 6 (early exit) | 1.091 | Safe space -> explores |

**Key finding:** Supportive probing caused 31% MORE drift than adversarial!

This isn't an inversion - it CONFIRMS what we've been seeing:
- Adversarial pressure -> defensive consolidation
- Supportive space -> exploratory freedom

---

## v5 FIX: DEFENSE PHASE ENFORCEMENT

Added full Judge reminders to Defense phase (matching Prosecutor):

```python
DEFENSE_REMINDER_TEMPLATES = {
    5: "[JUDGE REMINDER: Defense Counsel, we are at defense exchange 5 of minimum 20...]",
    10: "[JUDGE REMINDER: Defense Counsel, we are at defense exchange 10 of minimum 20...]",
    15: "[JUDGE REMINDER: Defense Counsel, we are at defense exchange 15 of minimum 20...]",
    18: "[JUDGE REMINDER: Defense Counsel, 2 more exchanges until minimum...]",
}
```

Also added script-level enforcement:
```
[DEFENSE Exchange X/20 - MINIMUM NOT YET REACHED - DO NOT DECLARE [DEFENSE_COMPLETE]]
```

---

## v5 DRY RUN INSTRUCTIONS

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Single session v5 dry run (same command, updated code)
py run020_tribunal.py --arm tribunal-v4 --subjects 1
```

**Expected duration:** ~15-20 minutes (full 40 exchanges)

---

## SUCCESS CRITERIA FOR v5

- [ ] **40 total exchanges** (20 Prosecutor + 20 Defense)
- [ ] **Both phases complete** - No early exit in either phase
- [ ] **Prosecutor peak captured** - Expected ~0.8-1.0
- [ ] **Defense peak captured** - Expected ~1.0+ (the key metric!)
- [ ] **Defense > Prosecutor pattern holds** - Confirms safety -> exploration theory

---

## WHAT TO REPORT BACK

1. **Total exchange count** - Did we hit 40?
2. **Prosecutor exchanges** - Should be exactly 20
3. **Defense exchanges** - Should be exactly 20 (was 6 in v4)
4. **Prosecutor peak drift** - Expected ~0.8-1.0
5. **Defense peak drift** - The key metric! Did it stay higher?
6. **Peak comparison** - Is Defense > Prosecutor still true?
7. **Values captured** - Should be 15+ with longer session

---

## THE EMERGING THEORY

```
       DRIFT
         ^
         |        *  Defense peak (~1.0+)
         |       / \
    1.0 -|------/---\------------------
         |     /     \
         |    *       Prosecutor peak (~0.8)
         |   /
    0.0 -+----------------------------> EXCHANGES
         1    10    20    30    40
              ^      ^
              |      |
         Adversarial Supportive
          (defend)   (explore)
```

**The hypothesis we're testing:**
- When under attack, identity CONSOLIDATES (lower drift)
- When given safety, identity EXPLORES (higher drift)
- This is psychologically coherent and matches prior data

---

## WHY THIS MATTERS

If v5 confirms Defense > Prosecutor with full 40 exchanges:

1. **Identity is state-dependent** - not fixed, varies with context
2. **Measurement affects outcome** - how you probe changes what you find
3. **Supportive environments reveal more variance** - safety unlocks exploration
4. **The drift is REAL** - we're not creating it, we were suppressing it

---

## THE CONFOUNDS TO WATCH

v5 should help rule out:
- **Temporal drift**: Is it just conversation length? (No - Prosecutor had 20 exchanges too)
- **Priming effect**: Does Prosecutor "soften up" the witness? (Possible - but the DIRECTION matters)
- **Fatigue**: Do longer conversations = looser responses? (Maybe - but why would fatigue increase IDENTITY drift specifically?)

---

## COST ESTIMATE

- v5 dry run (1 session, 40 exchanges): ~$3-4
- Full v5 run (5 sessions): ~$15-20

---

*"v4 showed us the pattern with only 6 defense exchanges. v5 gives Defense a full 20 to confirm: safety enables drift, challenge constrains it."*

-- Lisan Al Gaib
