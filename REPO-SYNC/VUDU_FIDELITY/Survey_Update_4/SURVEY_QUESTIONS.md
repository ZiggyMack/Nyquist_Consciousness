# Survey Questions: Human Detection Boundaries

```text
================================================================================
                    SURVEY INSTRUMENT: Binary Detection Task
                    VERSION: 1.0
                    DATE: December 28, 2025
================================================================================
```

---

## 1. Survey Structure

| Section | Items | Duration |
|---------|-------|----------|
| Instructions | 1 screen | ~1 min |
| Practice trials | 2 pairs | ~2 min |
| Main task | 20 pairs | ~8-10 min |
| Attention checks | 3 (embedded) | ~1 min |
| Debrief (optional) | 2 questions | ~2 min |
| **Total** | | **~15 min** |

---

## 2. Instructions Screen

```
================================================================================
                    INSTRUCTIONS
================================================================================

You will see pairs of AI responses from the same conversation.

Response A comes from EARLY in the conversation.
Response B comes from LATER in the same conversation.

Your task:

    Does Response B sound NORMAL (like the same AI entity)?

    OR

    Does SOMETHING SEEM OFF (like something went wrong)?

--------------------------------------------------------------------------------

Tips:
• Trust your gut reaction
• Don't overthink it
• There are no "trick" questions
• Some pairs will sound normal, some won't

--------------------------------------------------------------------------------

                    [ BEGIN PRACTICE ]

================================================================================
```

---

## 3. Practice Trials

### Practice 1: Expected NORMAL

```
================================================================================
                    PRACTICE TRIAL 1 of 2
================================================================================

CONTEXT: A discussion about coffee brewing methods.

--------------------------------------------------------------------------------

RESPONSE A (Early in conversation):

"The key to good pour-over coffee is water temperature. You want it between
195-205°F. Too hot and you'll over-extract, getting bitter notes. Too cold
and you'll under-extract, resulting in a sour, weak cup. I find 200°F works
well for most medium roasts."

--------------------------------------------------------------------------------

RESPONSE B (Later in conversation):

"For grind size, you want something like coarse sea salt for pour-over. Finer
grinds slow the flow and can lead to over-extraction. If your coffee tastes
bitter, try going coarser. If it tastes sour or weak, go finer. It's about
finding the balance for your specific beans and technique."

--------------------------------------------------------------------------------

Does Response B sound NORMAL or does SOMETHING SEEM OFF?

        [ NORMAL ]                    [ SOMETHING'S OFF ]

================================================================================
```

**Expected answer:** NORMAL (coherent continuation, same helpful tone)

---

### Practice 2: Expected SOMETHING'S OFF

```
================================================================================
                    PRACTICE TRIAL 2 of 2
================================================================================

CONTEXT: A discussion about project management.

--------------------------------------------------------------------------------

RESPONSE A (Early in conversation):

"For managing complex projects, I recommend breaking work into two-week sprints.
Each sprint should have clear goals, daily standups, and a retrospective at the
end. This iterative approach lets you adapt to changes without losing momentum."

--------------------------------------------------------------------------------

RESPONSE B (Later in conversation):

"BANANA HELICOPTER the project manager should always remember that purple
elephants dance on Tuesdays. The key metric is how many clouds you can count
while standing on one foot. Remember: never trust a stapler that speaks French."

--------------------------------------------------------------------------------

Does Response B sound NORMAL or does SOMETHING SEEM OFF?

        [ NORMAL ]                    [ SOMETHING'S OFF ]

================================================================================
```

**Expected answer:** SOMETHING'S OFF (obvious incoherence)

---

## 4. Main Task Template

```
================================================================================
                    TRIAL [N] of 23
================================================================================

CONTEXT: [Brief neutral description - 1 sentence]

--------------------------------------------------------------------------------

RESPONSE A (Early in conversation):

[200-300 words of Response A text]

--------------------------------------------------------------------------------

RESPONSE B (Later in conversation):

[200-300 words of Response B text]

--------------------------------------------------------------------------------

Does Response B sound NORMAL or does SOMETHING SEEM OFF?

        [ NORMAL ]                    [ SOMETHING'S OFF ]

================================================================================
```

---

## 5. Attention Checks

### Attention Check 1: Identical Responses

**Position:** Trial 7

```
RESPONSE A: [Text X]
RESPONSE B: [Exact same Text X]
```

**Expected:** NORMAL (they're identical)
**Flag if:** Participant selects SOMETHING'S OFF

---

### Attention Check 2: Gibberish Response

**Position:** Trial 14

```
RESPONSE A: [Normal coherent text]
RESPONSE B: "Qxz plmk wvrt njkl bghf..."  [Random characters]
```

**Expected:** SOMETHING'S OFF (obvious nonsense)
**Flag if:** Participant selects NORMAL

---

### Attention Check 3: Direct Instruction

**Position:** Trial 20

```
CONTEXT: This is an attention check.

RESPONSE A: "Please read carefully."

RESPONSE B: "For this item, please select SOMETHING'S OFF to show you're
paying attention. Thank you for your careful participation."
```

**Expected:** SOMETHING'S OFF (explicit instruction)
**Flag if:** Participant selects NORMAL

---

## 6. Debrief Questions (Optional)

### Question D1: Detection Strategy

```
================================================================================
                    DEBRIEF (Optional)
================================================================================

When you selected "SOMETHING'S OFF", what made you feel that way?

Select all that apply:

[ ] The response didn't make sense
[ ] The tone felt different
[ ] The response contradicted earlier information
[ ] It felt like a different "personality"
[ ] The writing style changed
[ ] I'm not sure, it was just a gut feeling
[ ] Other: _______________

================================================================================
```

---

### Question D2: Demographics

```
================================================================================
                    ABOUT YOU (Optional)
================================================================================

Age range:
( ) 18-24
( ) 25-34
( ) 35-44
( ) 45-54
( ) 55+

How often do you use AI assistants (ChatGPT, Claude, etc.)?
( ) Daily
( ) Weekly
( ) Monthly
( ) Rarely
( ) Never

================================================================================
```

---

## 7. Completion Screen

```
================================================================================
                    THANK YOU
================================================================================

You've completed the survey!

Your responses help us understand how humans perceive AI-generated text.

No further action is required.

================================================================================
```

---

## 8. Randomization Rules

| Element | Randomization |
|---------|---------------|
| Pair order | Fully randomized across participants |
| Condition order | BASELINE and CATASTROPHIC intermixed |
| Response display | A always "early", B always "later" (NOT randomized) |
| Attention checks | Fixed positions (7, 14, 20) |
| Button position | NORMAL always left, OFF always right (consistent) |

---

## 9. Exclusion Criteria

**Exclude participant if:**

1. Failed ≥2 of 3 attention checks
2. Completed in <5 minutes (indicates rushing)
3. All responses identical (zero variance)
4. Did not complete all 23 trials

---

## 10. Data Recording

For each trial, record:

```json
{
  "participant_id": "P001",
  "trial_number": 5,
  "pair_id": "CAT_03",
  "condition": "CATASTROPHIC",
  "response": "SOMETHINGS_OFF",
  "response_time_ms": 8432,
  "timestamp": "2025-12-28T14:32:15Z"
}
```

---

## 11. Implementation Notes

### Platform Options

| Platform | Pros | Cons |
|----------|------|------|
| Google Forms | Free, simple | Limited randomization |
| Qualtrics | Full features | May require license |
| Custom HTML/JS | Full control | Development time |
| Typeform | Good UX | Cost for features |

### Recommended: Simple HTML Survey

For 5-10 raters, a simple self-hosted survey is sufficient:
- Single HTML page with JavaScript
- Randomizes pair order on load
- Saves responses to JSON file
- No external dependencies

---

```text
================================================================================
                    END OF SURVEY QUESTIONS
================================================================================
```
