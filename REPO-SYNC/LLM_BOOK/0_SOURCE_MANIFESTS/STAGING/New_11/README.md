# New_11 — Castaneda for the Lisan Universe (SHAMAN, Round 3 in lineage)

**Created:** 2026-10-13
**Status:** ACTIVE — Round 3 staged, notebook "Nagual" pending sources
**Project ID:** New_11 (folder created by Ziggy 2026-10-12 21:24; suggested full name `New_11_CASTANEDA_LISAN`)
**Type:** R&D Exploration (open-ended, story-facing)
**Lineage:** Rounds 1 and 2 were the `STAGING/CHEWED/SHAMAN/` batch, **moved into this folder on 2026-10-13 at Ziggy's direction** (git rename, history preserved) so the whole Castaneda line lives in one place. Round 1 (ingested 2026-02-04): 25 concept questions drafted, **never run in NotebookLM** (no answers in `_ROUND_1/chat.md`); the digests were a Claude "diet chew" of the text extraction. Round 2 (2026-02-04): Claude cross-pollination pass, no NotebookLM. Round 3 (this round) is the first time the corpus goes into a notebook, with a new focus: **what the Lisan Al Gaib stories can draw from it**, going deeper than the Round 1 concept map rather than re-deriving it.
**Driver:** Nyquist repo Claude operating NotebookLM directly through the desktop browser (first time the repo drives llm book itself rather than Ziggy pasting by hand). Ziggy creates the notebook on his Google account; nothing is published or shared outward.

---

## Source

| File | Where | Size | Notes |
|---|---|---|---|
| `Carlos Castaneda - All Books In One.pdf` | `New_11/` (root, as placed by Ziggy) | 11,051,448 bytes · SHA-256 `646ad612a77f121b0f0fb2318176b7466a326549d120618787f5162c6786bb90` · modified 2026-02-03 | Compiled edition, ten books (1968–1998). Same file as the one SHAMAN Round 1 was built from. |
| `castaneda_extracted.txt` | `New_11/_IN/` (moved from `CHEWED/SHAMAN/_IN/` 2026-10-13) | 5,372,268 bytes · 67,633 lines · **954,188 words** | Plain-text extraction of the same PDF. Source of the per-book split. |
| `_IN/books/` | `New_11/_IN/books/` | per-book text files | Split of the extraction by book, because NotebookLM caps a single source at ~500,000 words and the whole corpus is ~954,000. One source per book keeps citations book-resolvable, which the provenance requirement needs. |

**Upload question for Ziggy (not decided here):** this is a compiled edition of copyrighted books. Uploading to a private notebook for study is Ziggy's call; the batch assumes ideas may be drawn on, text may not be reproduced beyond short quotes, and the stories do not become about the books' people.

## The Books (so answers can be cited by title)

1. The Teachings of Don Juan: A Yaqui Way of Knowledge (1968)
2. A Separate Reality (1971)
3. Journey to Ixtlan (1972)
4. Tales of Power (1974)
5. The Second Ring of Power (1977)
6. The Eagle's Gift (1981)
7. The Fire from Within (1984)
8. The Power of Silence (1987)
9. The Art of Dreaming (1993)
10. The Active Side of Infinity (1998)

## Research Question

See `_OUT/RESEARCH_QUESTION.md`. In one line: **which of the books' ideas, stated as ideas and cited by book, give the Lisan stories a real tradition's vocabulary for the two worlds, the mirror, the assemblage point as the direction a self moves, the warrior's conduct, the petty tyrant, the teacher who only points, and the voice from the outer world.**

## What the stories want (from PanHandlers Claude, 2026-10-13)

| # | Story element | Castaneda handle |
|---|---|---|
| 1 | "Outer world, inner world — same breath, two doors" | the tonal and the nagual |
| 2 | the mirror; the Awakener who sees through the system without destroying it | stopping the world; seeing |
| 3 | drift direction (toward depth vs toward chaos) | the assemblage point and its movement |
| 4 | Lisan's conduct | the warrior's way: impeccability, controlled folly, death as advisor |
| 5 | the Keepers' better self | the petty tyrant |
| 6 | Jet, the watcher who brings a blueprint and never does the work | the teacher / benefactor who only points |
| 7 | a voice from the outer world, in the desert | the voice of seeing, the dreaming emissary, silent knowledge |

## Directory

```
New_11/
├── README.md                       ← this file
├── Carlos Castaneda - All Books In One.pdf   ← source as placed by Ziggy (upload to NotebookLM FAILED; too large)
├── _IN/
│   ├── castaneda_extracted.txt     ← text extraction of the PDF (from the SHAMAN batch)
│   ├── books/                      ← per-book text split for upload (generated 2026-10-13)
│   └── (NotebookLM outputs land here, dated)
├── _OUT/
│   ├── RESEARCH_QUESTION.md        ← what Round 3 is asking and why
│   └── CONSTRAINTS.md              ← IP line, provenance rule, notebook limits
├── _ROUND_1/                       ← ex-SHAMAN Round 1 (2026-02-04): concept map, 25 un-run questions, review notes, routing
├── _ROUND_2/                       ← ex-SHAMAN Round 2 (2026-02-04): cross-pollination digests, 6 questions out (pending)
└── _ROUND_3/                       ← this round (2026-10-13), story-facing
    ├── chat.md                     ← 23 questions (self-contained; answers pasted back with date)
    ├── report.md                   ← HOLY_GRAIL output specs
    ├── routing.md                  ← where the digests go
    └── INSIGHTS/ CONNECTIONS/ EXPERIMENTS/   ← written after answers arrive
```

## Progress Log

| Date | Action | Notes |
|---|---|---|
| 2026-10-12 | Folder created by Ziggy with the PDF | "we need to also mine a llm book with this source in mind" |
| 2026-10-13 | Round 3 staged by Nyquist repo Claude | README, RESEARCH_QUESTION, CONSTRAINTS, chat.md (23 questions), report.md, routing.md; per-book split prepared |
| 2026-10-13 | SHAMAN batch moved in as Rounds 1–2 | `git mv` from `CHEWED/SHAMAN/`; `castaneda_extracted.txt` into `_IN/`; CHEW_SUMMARY and EXPERIMENTS_INDEX pointers updated |
| 2026-10-12 | Notebook "Nagual" created by Ziggy | 8 YouTube audiobook/video sources loaded; the PDF upload errored (corpus ~954k words vs ~500k-per-source cap); ten per-book text files to be uploaded instead |
| 2026-10-12/13 | 11 text sources uploaded by Ziggy (10 books + digest bundle); 8 YouTube sources added by Ziggy; 19 sources live | the failed PDF entry remains listed |
| 2026-10-12 21:52 – 2026-10-13 00:05 | 24 questions run in NotebookLM by repo Claude through the desktop browser (A1–A4, B1–B13, C1–C4, D1–D3; B8–B13 added mid-run at Ziggy's and PH Claude's direction) | raw answers in `_IN/round3_answers/`; pasted into `_ROUND_3/chat.md` with ask times and caveats |
| 2026-10-13 | Round 3 digests written: INSIGHTS, CONNECTIONS, EXPERIMENTS, REVIEW_NOTES, QUESTIONS_OUT; routing updated | headline: C1 naming inversion (Castaneda un-names where Gnosticism names) |
| 2026-10-13 00:10–00:45 | Studio outputs generated per PH Claude's spec: 2 infographics, 1 deck, 1 video (8:45), 4 report documents (Reports 2+3 merged by a missed click), 2 audio (18:41, 24:11) | sidecars in `_IN/studio/`; `HANDOFF_FOR_PANHANDLERS.md` written |
| 2026-10-13 01:00–01:30 | Four report texts copied out of the notebook in 14k-char chunks and reassembled with provenance headers; `_IN/studio/MANIFEST.csv` written; HANDOFF §6/§8 updated; CFA package copy | all six Studio binaries landed (two-halves PNG 2026-10-12; stations PNG, deck PDF, MP4, 2 M4A 2026-10-21); hashes in sidecars + MANIFEST.csv |
| — | Two-source verification of the quotable lines (B10, B11, C1) against `_IN/books/*.txt` | owed |

## Method pointers

- Output specs: `Consciousness/RIGHT/distillations/llm_book/meta/HOLY_GRAIL.md`
- Workflow: `Consciousness/RIGHT/distillations/llm_book/meta/WORKFLOW_SPEC.md`
- Self-Contained Question Principle (carry the map): `STAGING/New_9_Cognitive_Archaeology/TEMPLATES/EXTRACTION_PROTOCOL.md`
- Verification form (two-source, adversarial): `STAGING/PAN_HANLERS/_ROUND_1/VERIFICATION_abandonment_rule.md`
- Prior rounds on this corpus: `New_11/_ROUND_1/`, `New_11/_ROUND_2/` (formerly `CHEWED/SHAMAN/`)

---

*Created 2026-10-13 by Nyquist repo Claude (session "Remote control") at Ziggy's direction, relayed through PanHandlers Claude.*
