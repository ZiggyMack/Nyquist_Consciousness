# Verification — the ten quotable lines of Round 3 against the per-book texts

**Date:** 2026-10-13 · **Method:** literal grep (case-insensitive, with line-wrap variants) of `New_11/_IN/books/*.txt`, the same ten texts the notebook holds. This is a quotation check, not the full adversarial two-source pass (that is still owed for the claims, as opposed to the quotes).
**Verdict:** 10/10 lines exist in the primary text; 9 verbatim, 1 paraphrased by NotebookLM (wording note below). None was fabricated.

| # | Line as NotebookLM gave it | Answer(s) | Found in | Verbatim? | Note |
|---|---|---|---|---|---|
| 1 | "only a crackpot would undertake the task of becoming a man of knowledge of his own accord. A sober-headed man has to be tricked into doing it" | B10 | 02_A_Separate_Reality.txt | YES | — |
| 2 | "The rule is that a man of knowledge has to trap his apprentice. Today I have trapped you and I have tricked you into learning." | B6, B10, B13 | 02_A_Separate_Reality.txt | YES | preceded in the text by "Whatever I have done to you today was a trick," he said bluntly. |
| 3 | "shatter the mirror of self-reflection" | B11 | 08_The_Power_of_Silence.txt | NO (paraphrase) | the books' phrase is **"Breaking the Mirror of Self-Reflection"** (chapter 11 title, "The Requirements of Intent: Breaking the Mirror of Self-Reflection"). Use "breaking" if quoting. |
| 4 | "the sorcerer that finds himself face to face with himself is a dead sorcerer" | B11, C2 | 04_Tales_of_Power.txt | YES | — |
| 5 | "The tonal must be protected at any cost" | B1, C1 | 04_Tales_of_Power.txt | YES | — |
| 6 | "Impeccable warriors don't lose their marbles" | B3 | 07_The_Fire_from_Within.txt | YES | — |
| 7 | "what we witness on its round walls is our own reflection" | B11 | 04_Tales_of_Power.txt | YES | full sentence: "That bubble is our perception. We live inside that bubble all of our lives. And what we witness on its round walls is our own reflection." |
| 8 | "figures in front of a mirror" | B11 | 10_The_Active_Side_of_Infinity.txt | YES | — |
| 9 | "My statements have no inkling of morality" | B4, A4 | 07_The_Fire_from_Within.txt | YES | full: "Impeccability is nothing else but the proper use of energy," he said. "My statements have no inkling of morality." |
| 10 | "Impeccability is nothing else but the proper use of energy" | B4 | 07_The_Fire_from_Within.txt | YES | — |

**Not checked here:** chapter attributions (NotebookLM's "Chapter N" labels), the bracketed page indices (they are NotebookLM's internal positions, not page numbers), and the two "Wheel of Time" claims in B10 (YouTube-sourced). The adversarial claim-level pass (PAN_HANLERS form) remains owed.

*Run by Nyquist repo Claude, 2026-10-13.*
