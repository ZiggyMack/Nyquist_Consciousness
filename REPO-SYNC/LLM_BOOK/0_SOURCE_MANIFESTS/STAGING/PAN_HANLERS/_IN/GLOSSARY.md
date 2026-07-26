# 📖 Glossary — Self-Contained Definitions

> Written for the **Self-Contained Question Principle**: NotebookLM (and
> any model working only from an uploaded source set) answers *only* from
> what's in its notebook. It cannot see this repo, our other documents, or
> any convention explained only in a doc that wasn't uploaded. Any chat
> question or report prompt that names one of these terms should either
> (a) inline the one-line definition below directly into the prompt, or
> (b) make sure this file is one of the uploaded sources.
>
> Each entry is written to be copy-pasted as-is into a prompt.

---

## People

- **Ziggy** — the human who runs the extraction and debates the people
  below. Also profiled in this archive, as a symmetry control.
- **Grant, Angles, Tale Recursion, Tom, Sorta, Kee, Tapioca** — real
  people Ziggy debates philosophy with, each profiled from real
  conversation transcripts under the discipline below.
- **Nova** — a separate AI collaborator (not part of this upload) who
  co-designed the extraction method and reviews its outputs. Nova's own
  interpretations are tracked as a distinct source type (see below), never
  credited to a human.

## The method

- **A "dig"** — a bounded extraction pass over one source conversation:
  what was actually said, by whom, and what it might mean, done in
  staged steps so each step can be checked before the next one runs.
- **"Plow-through mode" / zero-promotion** — a rule that wholesale,
  fast-pass data collection may surface leads (candidate ideas, candidate
  patterns) but may never be treated as a confirmed, citable fact about a
  person until a separate, narrower follow-up pass confirms it
  independently.
- **"Promotion"** — the act of a claim advancing from a tentative,
  packet-local note to something citable as archive fact. Most claims in
  this material have **not** been promoted — they're candidates.
- **Source-confidence labels** (attached to nearly every claim in the
  underlying archive, though stripped out of the index files in this
  upload for readability):
  - *Direct* — the person's own exact words, verified.
  - *Quoted* — exact wording, but via typed transcription rather than a
    verified image/screenshot.
  - *Reported* — Ziggy's paraphrase of what someone said, not their exact
    words.
  - *Interpretation* — an AI's own reading, explicitly never attributed
    to the human it's about.
  - *Co-constructed* — built jointly in the conversation, not
    attributable to one party.
- **Availability tiers (A3/A2/A1/A0)** — how confidently an *omission*
  (something a person could have said but didn't) can be treated as
  meaningful: A3 = they demonstrably had and used the relevant tool
  elsewhere, so its absence here is informative; A2 = it was explicitly
  requested or offered and then not delivered; A1 = plausible but
  unconfirmed; A0 = genuinely unknown, never treated as an omission at
  all.
- **"IT-###"** — an *idea trail* number: a tracked lineage of one
  recurring idea across multiple conversations, distinct from any single
  conversation.
- **The "detector-vs-disease" pattern** — a named recurring analysis
  error: mistaking a person's *corrective* move (auditing, catching,
  critiquing a flaw) for an *instance* of the very flaw they're
  correcting. A method that detects a pathology is not thereby an example
  of it.
- **"Anti-collapse distinction"** — this project's own term (not a
  standard philosophical one) for its most common finding: a case where
  one legitimate concept is being allowed to stand in for a stronger,
  different claim than the evidence supports (e.g., treating
  "foundational" as though it meant "infallible").

## Terms inside the dig files (only needed once the cleaned dig workbooks are uploaded)

The definitions above cover the two index files. The dig workbooks (`DIG_*`)
use a finer-grained vocabulary. If a cleaned, de-protocoled copy of a dig is
uploaded as source material, inline these too — or upload this glossary
alongside them.

- **Attribution codes (person-prefixed)** — every claim in a dig is tagged
  by *who* said it and *how directly*:
  - *Z-DIRECT* — Ziggy's own words in the bounded thread.
  - *G-DIRECT* — the debated person's own words, image-verified (screenshots).
  - *G-QUOTED* — the debated person's exact wording via typed transcription,
    not image-verified.
  - *G-REPORTED* — Ziggy's paraphrase of the debated person, not their words.
  - *G-ANTICIPATED* — a predicted move the debated person has not actually made.
  - *CO-CONSTRUCTED* — built jointly in the Ziggy–Nova conversation,
    attributable to neither alone.
  - *NOVA-INTERPRETATION / NOVA-RECONSTRUCTED* — the AI's own reading or
    reconstruction, never attributed to a human. ("G-" is the prefix for
    Grant, the most-profiled debated person; other members get their own.)
- **NON-SITE** — a dig that produced no promotable evidence about its intended
  target (e.g., "Grant: G-REPORTED NON-SITE" = the thread mentioned Grant but
  yielded nothing citable *about him*). The idea content is still kept.
- **CO-### / Z-### / G-###** — stable ID numbers: `CO-###` = a cognitive
  operator (a named reasoning move); `Z-###` / `G-###` = a numbered
  source-index entry for that person. (`IT-###`, an idea trail, is above.)
- **Field-desk review** — Nova's verdict on a stage's output, filed inside the
  workbook (run next stage / repurpose / quarantine). A decision log *about the
  extraction*, never itself evidence about a person.
- **Fifth-artifact rule** — the four stage outputs are immutable once pasted;
  the clean synthesis packet is a separate, fifth, *derived* artifact, so
  audits can catch "synthesis drift." If packet and workbook disagree, the
  workbook wins.
- **Synthesis packet** — a short (3–5 KB) clean summary assembled from a
  *completed* workbook (Promoted Claims / Explicitly NOT Promoted / Operator
  Outcomes / Trail & Leads). Only a few digs have one; most exist only as raw
  workbooks.
- **Stage 1–4** — the four extraction passes each workbook runs: (1) source
  survey — who said what, position ladders; (2) candidate harvest — the
  reasoning moves/operators surfaced; (3) pressure-test — challenges to the
  candidates; (4) provisional mapping into operators and trails.
- **Compound sweep** — a workbook that ran Stages 2–4 wholesale over a
  multi-topic thread as fast data collection (see "plow-through" above).
  Generates leads; promotes nothing without a later bounded sub-dig.
- **QUARANTINED** — a claim held inside its packet, not profile-grade, until a
  second independent packet corroborates it. Quarantined ≠ hidden — it's
  written to publication standard, just not yet citable.
- **Operator maturity (RED)** — a newly-registered operator flagged RED =
  tentative, observed once, recurrence untested.

## Reading the two included indices

- **`DIG_MAP.md`** — one row per source conversation: topic, approximate
  date, which of the people above appear.
- **`IDEA_TRAILS_INDEX.md`** — one row per tracked idea (`IT-###`), each
  with a short note on what was actually found or left unresolved.
- **`CONSTITUTIONAL_BACKBONE.md`** — the compression pass: the six
  recurring structural questions underneath all of the above, with the
  anti-collapse distinctions each one produced.

---

**Filed:** `circle/SYNC_OUT/GLOSSARY.md`
**Last updated:** 2026-07-22
**Beefed up 2026-07-22** by Repo (Nyquist) Claude — added the "Terms inside
the dig files" section so the Self-Contained Question Principle holds once
cleaned dig workbooks are uploaded, not just the two index files. Relay to
the `circle/` master if one exists.
