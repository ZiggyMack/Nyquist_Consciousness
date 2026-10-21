# REVIEW NOTES: New_11 — Round 3

**Round:** 3 · **Date:** 2026-10-13 · **Reviewer:** Nyquist repo Claude (session "Remote control")
**Status:** ANSWERED (24/24), digests written, verification NOT yet run, Studio outputs pending

---

## Source Set (notebook "Nagual", Ziggy's account, created 2026-10-12)
- 10 per-book text sources: `New_11/_IN/books/01…10_*.txt` (split from `_IN/castaneda_extracted.txt`, 954,188 words; the compiled PDF failed to upload, over the ~500k-words-per-source cap)
- 1 digest source: `_IN/upload/00_NYQUIST_PRIOR_DIGESTS_SHAMAN_R1_R2.md` (our R1/R2 review notes, insights, connections; provenance-stamped as ours)
- 8 YouTube sources added by Ziggy: an audiobook of The Art of Dreaming, an audiobook of The Power of Silence, an abridged A Separate Reality, a reading of The Wheel of Time, a "Getting Castaneda" commentary, a "Blue Scout" commentary, a quotes/aphorisms compilation, and a first episode of a dramatization
- 1 failed source still listed (the PDF)

## Method
Per-question standing rule typed with every question (answer only from sources; book title per claim; short quotes; our terms are ours; flag the digest; flag cross-book disagreement; from B11 on, also flag YouTube-sourced claims). Questions typed into the chat by the repo Claude through the desktop browser; answers extracted from the page and saved raw to `_IN/round3_answers/<id>.md` with the ask time; citation markers stripped by hand; tables re-set as markdown.

## Quality Assessment

| Dimension | Rating | Notes |
|-----------|--------|-------|
| Citation discipline | HIGH | 24/24 answers name book titles; most give chapters; many give bracketed source-page indices |
| Rule compliance | HIGH | digest-file reliance flagged in every answer that used it (6); YouTube reliance flagged from B11 on (8 answers); cross-book shifts given in 20/24 |
| Build-shaped questions (A, B, C) | HIGH | stayed on the books; mechanism-level; filmable detail in B8/B9 |
| Report-shaped questions (D1, D2) | MODERATE | drifted toward YouTube commentary and third-party biographical claims about real persons (excluded from story use in the saved files) |
| Novelty for the repo | HIGH | the naming inversion (C1), the behavioral sign of a healthy shift (B3), the trick-as-rule (B10) |
| Verification | NOT RUN | two-source adversarial check against the per-book texts still owed (see below) |

## Caveats
- **Two "Wheel of Time" claims in B10** cite a YouTube reading of the 1998 anthology, not one of the ten book texts; treat as commentary until checked.
- **D1 §3B and D3 §8** carry third-party claims about real persons (a memoir, named collaborators). Kept in the raw answers for the record; excluded from any story-facing digest; not to be copied into the CFA package.
- **Bracketed page indices** ([172–174] etc.) are NotebookLM's internal source positions, not book page numbers.
- **Our digest file contaminated three answers** in the expected way: C1 quoted our "compulsive naming" line, C2 took the "Warrior's witness" label, C4 took "Awakening deficit." All three flagged by the model; none load-bearing.
- NotebookLM "Save to note" was tried once and saved the notebook overview instead of the answer; not used after that. The chat history in the notebook is the only in-notebook record of the answers.

- **Reports 2 and 3 ran as one merged report** ("The Warrior's Conduct & The Teacher Who Only Points"): the second Generate click did not register and the Report 3 prompt was appended to the Report 2 prompt. Part I = Report 2, Part II = Report 3. Kept as one file (`_IN/studio/20261013_report_warriors-conduct_AND_teacher-who-only-points_MERGED.md`); regenerate separately only if a reader finds either part too thin. Driving lesson: re-find the "Generate now" ref after typing, before clicking.
- **Studio reports lean on the YouTube commentary** ("GETTING CASTANEDA") for the late-era physics and tag it inline; book-cited sentences are mostly The Teachings of Don Juan by chapter. Report 5 says controlled folly, stopping the world and personal power "rest only on the digest file": a retrieval artefact of the per-book split, not a fact about the corpus (those are book terms: A Separate Reality; Journey to Ixtlan). Two reports repeat the falsified 9/4 ceiling from our digest; flagged in each report header.
- **Studio binaries could not be downloaded from the app browser** (new-tab to googleusercontent refused; fetch blocked by CSP; curl returns the login page; clipboard writes denied). Report texts were copied out of the artifact view in 14,000-character chunks and reassembled with provenance headers; the six binaries wait on Ziggy's Download clicks.

## Verification Owed
Run the PAN_HANLERS form (`_ROUND_1/VERIFICATION_abandonment_rule.md`): one adversarial verifier per claimed quotation in B10, B11, C1, instructed to refute, against `_IN/books/*.txt`. Priority: the four verbatim-looking quotes PH Claude is most likely to use ("a sober-headed man has to be tricked," "the rule is that a man of knowledge has to trap his apprentice," "shatter the mirror of self-reflection," "the sorcerer that finds himself face to face with himself is a dead sorcerer").

## Routing
Primary: CFA (Lisan writer's pass) via `HANDOFF_FOR_PANHANDLERS.md` and the CFA package. Secondary: New_6 (C1), New_7 (B2, C4), Frame_Theory (C2), Lucien (C3). See `routing.md` and `QUESTIONS_OUT.md`.

---

*Created 2026-10-13 · Round 3 review · Nyquist repo Claude*
