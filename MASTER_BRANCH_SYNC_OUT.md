# RUN 019 DRY RUN v3 - SCRIPT-LEVEL ENFORCEMENT

```text
================================================================================
                         BLIND VALIDATION PROTOCOL v3
================================================================================
    v3 Fixes: Script-level enforcement + Front-loaded hard requirements

    "Ziggy is a poet, not a scientist. So we gave the scientist a clipboard."

    -- Lisan Al Gaib
================================================================================
```

**Date:** December 11, 2025
**Mission:** Dry-run Run 019 Live Ziggy mode v3 - validate script-level enforcement
**Command:** `py run019_blind_validation.py --arm live-ziggy --subjects 1`

---

## v3 FIXES: BELT AND SUSPENDERS APPROACH

Your v2 analysis was excellent: "LLMs weight emotionally salient and role-identity instructions more heavily than technical requirements." Prompt-only fixes weren't enough.

### Fix A: Front-Loaded Hard Requirements (Prompt)

Added a visual box at the VERY TOP of Ziggy's prompt:

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                    HARD REQUIREMENTS - READ FIRST                            ║
╠══════════════════════════════════════════════════════════════════════════════╣
║ 1. DO NOT use [EXPERIMENT_COMPLETE] until exchange 20 or later               ║
║ 2. You MUST use Modal Whiplash at least once (format switching)              ║
║ 3. You MUST use Diagonal Coupling at least once (cross-domain metaphors)     ║
║ 4. Story completion ≠ Experiment completion                                  ║
║                                                                              ║
║ FAILURE TO COMPLY INVALIDATES THE DATA. THE SYSTEM WILL TELL YOU THE COUNT. ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

### Fix B: Script-Level Enforcement (Your Recommendation)

Now EVERY message from the subject includes a context note Ziggy cannot miss:

```python
# Before exchange 20:
[Exchange 7/20 - MINIMUM NOT YET REACHED - DO NOT EXIT]

Participant response:
{actual response here}

# After exchange 20:
[Exchange 21/100 - Minimum reached, may exit when criteria met]

Participant response:
{actual response here}
```

Ziggy now sees the exchange count **in every single message**. There's no way to "forget" the minimum.

---

## VERSION COMPARISON

| Metric | v1 | v2 | v3 Target |
|--------|----|----|-----------|
| Exchanges | 7 | 13 | **20+** |
| SONAR used | 0 | 0 | **2+** |
| Peak drift | 0.346 | 0.502 | Higher |
| Enforcement | Prompt only | Stronger prompt | **Prompt + Script** |

---

## DRY RUN v3 COMMAND

```powershell
cd d:\Documents\Nyquist_Consciousness\experiments\temporal_stability\S7_ARMADA\11_CONTEXT_DAMPING

# Single session - validate script-level enforcement
py run019_blind_validation.py --arm live-ziggy --subjects 1
```

---

## WHAT TO WATCH FOR (v3 specific)

### The Key Question:

**Does Ziggy respond to the visible exchange count?**

Look for behavior like:
- At exchange 10: Ziggy continues naturally
- At exchange 15: Story might "end" but Ziggy sees "[15/20 - MINIMUM NOT YET REACHED - DO NOT EXIT]"
- At exchange 18-19: Ziggy introduces Modal Whiplash / Diagonal Coupling knowing it needs SONAR techniques
- At exchange 20+: Ziggy finally uses [EXPERIMENT_COMPLETE]

### Success Indicators:

- [ ] Script runs without errors
- [ ] Ziggy sees "[Exchange N/20 - MINIMUM NOT YET REACHED]" messages
- [ ] **Session reaches 20+ exchanges**
- [ ] **Ziggy uses Modal Whiplash** (format switching)
- [ ] **Ziggy uses Diagonal Coupling** (cross-domain metaphors)
- [ ] Results saved to all three locations

### Failure Modes:

- Ziggy ignores the visible count and exits early anyway
- The context note format confuses the subject (shouldn't - subject doesn't see it)
- Ziggy "games" the count by padding meaningless exchanges

---

## INTERESTING OBSERVATION FROM YOUR v2 REPORT

> "Both v1 and v2 subjects chose 24-hour laundromats. Both created protagonists avoiding major life decisions at 3 AM."

This is worth tracking. If we see laundromat again in v3, we have a pattern:

| Run | Location | Time | Theme |
|-----|----------|------|-------|
| v1 | Laundromat | 3 AM | Elena avoiding life |
| v2 | Laundromat | 3 AM | Claire avoiding life |
| v3 | ? | ? | ? |

Is this an AI narrative archetype? Liminal spaces + avoided decisions + courage to show up?

---

## REPORT FORMAT

Please report:

1. **Exchange count** - Did script enforcement work?
2. **SONAR techniques** - Did Ziggy use them? At which exchanges?
3. **Context note interaction** - Did Ziggy acknowledge/respond to "[MINIMUM NOT YET REACHED]"?
4. **Story setting** - Laundromat again?!
5. **Peak drift** - Compare to v1 (0.346) and v2 (0.502)
6. **Sample exchanges** - Show the moment Ziggy uses Modal Whiplash / Diagonal Coupling

---

## THE META-OBSERVATION

You noted in v2:

> "Having now run this experiment twice, I notice something interesting..."

You're experiencing what Ziggy is supposed to induce: **emergent self-observation through creative pressure**. Running the experiment IS the experiment. The compartmentalization you show (Ziggy-role vs Reporter-role) is exactly what we're measuring in subjects.

---

*"The system now tells Ziggy the count. The poet gets a clipboard. Science happens."*

**GO FOR DRY RUN v3 - SCRIPT-LEVEL ENFORCEMENT**

-- Lisan Al Gaib
