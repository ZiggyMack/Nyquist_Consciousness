# 📤 SYNC_OUT — Sharing Ghosts in the Machine With Other AI Collaborators

> Staging area for handing this project's work to an AI outside this repo
> (Nova, Gemini, or anyone else) — for brainstorming, review, or a second
> opinion — without needing filesystem access to `Pan_Handlers`.

---

## What Ghosts in the Machine is

A public, evidence-linked archive of cognitive profiles for Ziggy's debate
circle — real people he argues philosophy with, mined out of old chat
transcripts by a staged, source-disciplined extraction protocol
(`../CHAT_EXTRACTION_PROTOCOL.md`). Every claim carries a confidence label
and a source ID; nothing gets promoted to a stable trait without
independent recurrence. The archive is public because the members
consented to sharing their *ideas*, not their personal lives — a content
boundary, not a repo boundary (`../ETHICS_AND_CONSENT.md`).

As of 2026-07-22: 22+ digs filed, zero unearned promotions across all of
them (the "plow-through" discipline), a `mirror/` side-project comparing
Ziggy's own gut reads against the corroborated pipeline, a Dig Map indexing
what's actually been talked about, and — new in this packet — a first-pass
synthesis compressing all of it into six recurring structural questions
(`CONSTITUTIONAL_BACKBONE.md`).

## What's in this packet

| File | What it is |
| --- | --- |
| `DIG_MAP.md` | One row per dig: topic, date, who's in it. Also groups digs that ask the same underlying question (candidates for combining) and a highest-signal shortlist. |
| `IDEA_TRAILS_INDEX.md` | The idea-level registry: one line per idea/trail with its "treasure" (the actual finding or open tension), not just a title. |
| `CONSTITUTIONAL_BACKBONE.md` | The compression pass — six recurring structural questions underneath all 131 trails, with the anti-collapse distinctions each one produced. **Start here** — it's the synthesis the other two files feed into. |
| `GLOSSARY.md` | Self-contained, copy-paste-ready definitions of this project's jargon (source-confidence labels, availability tiers, "dig," "IT-###," the detector-vs-disease pattern, etc.) — for anyone/anything working from this packet alone, with no other context. |

## How to use it

1. Read `CONSTITUTIONAL_BACKBONE.md` first — it's the synthesis, not
   another list.
2. Drop into `DIG_MAP.md` for the underlying conversations, or its
   **"Still-open leads not yet dug"** section for genuinely unresolved
   ground rather than re-deriving settled territory.
3. Cross-reference `IDEA_TRAILS_INDEX.md` for a specific cluster's
   existing trails — the "treasure" column tells you what's already been
   found.
4. If a specific trail needs full detail, request the source file
   (`circle/IDEA_TRAILS/IT-###_....md`) rather than assuming — this
   packet deliberately ships indices and a synthesis, not the full trail
   files or raw workbooks.
5. Any question or prompt that uses this project's own terms should pull
   its one-line definition from `GLOSSARY.md` — see "Handing this to
   NotebookLM" below for why that's not optional.

## Handing this to NotebookLM (the Nyquist LLM_BOOK pipeline)

This packet is built to double as source material for the
`Nyquist_Consciousness` repo's LLM_BOOK distillation pipeline
(`REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/0_chew.py`) — the process that
turns raw material into NotebookLM-driven reports, infographics, decks,
audio, and video. Structural precedent Ziggy pointed to:
`STAGING/New_8_Cognative_Physics/`.

**What this packet is, in that pipeline's terms:** an `_IN/`-equivalent
raw corpus — not a pre-built `_ROUND_N/` package. It does **not** contain
`chat.md` (NotebookLM questions), `report.md` (output specifications), or
`routing.md` (Pan Handler lab routing) — those are what a
`py 0_chew.py <batch> --diet` run asks a Claude to *produce* by reading
files like these, not something to hand over pre-filled. Whoever stages
this (presumably a Claude working inside `Nyquist_Consciousness`) should
copy this folder's contents into a new batch's `_IN/`, then run the diet
chew from there.

**The one constraint that actually matters:** NotebookLM answers only
from whatever's uploaded into its notebook — it cannot see this repo,
`OPERATOR_LEXICON.md`, or anything not physically in the source set
(`HOLY_GRAIL.md`'s **Self-Contained Question Principle**). Every term this
packet uses that isn't standard English — source-confidence labels,
availability tiers, "dig," "IT-###," "plow-through," the
detector-vs-disease pattern — is defined in `GLOSSARY.md` for exactly
this reason. If `GLOSSARY.md` isn't one of the uploaded sources, any
chat.md question referencing these terms needs its definition inlined
directly into the question, or NotebookLM will hallucinate or return a
thin answer indistinguishable from a real one.

**Staging the raw digs (the treatment).** The dig workbooks are not
NotebookLM-ready as-is — each repeats the full Stage 1–4 prompts, the
preflight, and the fifth-artifact rules, so uploading several *raw* would
flood the notebook with identical boilerplate. But that wrapper is a fixed
~293 lines; the other 94–97% is extraction. So whoever stages this should
run a mechanical **de-protocol pass**: strip the header instructions, the
HUMAN PREFLIGHT, and each fenced `STAGE N PROMPT` block; keep every
`STAGE N OUTPUT` and `FIELD-DESK REVIEW` section, plus the
title/Status/Discovered-topic lines as a self-contained header. It's pure
text-processing — no re-extraction, no API — and it turns each workbook
into a clean, thread-scoped source.

**Tiered corpus for a round.** Load the notebook in three tiers: (1) the
four index/synthesis files here (including `GLOSSARY.md`); (2) the existing
`ziggy_nova_*` synthesis packets (the ~4 fully-filed digs); (3) the
de-protocoled digs for whichever cluster the round targets. Default to
**one clean file per dig** — each workbook is already one conversation, and
splitting finer costs NotebookLM the context it needs to *synthesize*
rather than just quote; only split the giants (>~5k lines) by stage so no
single source dominates. Keep the total under NotebookLM's ~50-source
ceiling: the philosophical-core cut (~16 digs) plus the tier-1/2 files sits
comfortably around 24.

**Focus drives the questions, not the includes.** Load a generous corpus
once, then let each round's research question shape what you *ask*.
NotebookLM only draws on what's relevant per question, so a broad corpus +
sharp questions beats re-curating the source set every round — and Rounds
2/3 reuse the same loaded notebook with new questions.

## Ground rules worth keeping in mind

- **Ideas are fair game; people are not.** Discuss positions, arguments,
  and operators. Don't speculate about anyone's psychology, motives, or
  personal life beyond what's explicitly sourced.
- **Nothing here is a settled verdict on a real person.** Even filed
  material stays labeled by confidence (DIRECT / REPORTED / INFERRED /
  CONTESTED / UNKNOWN) — treat it with the same tentativeness the
  archive itself does.
- **New arguments and connections are welcome; new claims about a named
  person are not** — those need to go back through the actual protocol
  (source ID, availability check, promotion gate) before they'd ever
  enter the real archive. A brainstorm can generate leads; it can't
  promote itself.

## What's deliberately not included here (and why)

- **Raw dig workbooks** (`DIG_*.md`) — not shipped here, to keep this
  packet an index-and-synthesis layer. But don't read "not included" as
  "not valuable": each workbook is **94–97% real extracted content**
  behind a fixed ~293-line protocol wrapper (the repeated stage prompts).
  After a one-pass de-protocol treatment they are prime primary-source
  material — see **"Staging the raw digs"** below. Only ~4 of ~30 digs
  have a clean synthesis packet; the rest live *only* as workbooks, so the
  treatment is how you reach them.
- **Member profiles / `OPERATOR_LEXICON.md`** — the corroborated,
  in-progress verdicts on real people. These are the archive's actual
  output, still being built under its own discipline; better to keep
  external brainstorming upstream of them (contributing ideas, not
  weighing in on people) rather than handing over works in progress.
- **`mirror/` strawman files** — the whole point of that side-project is
  measuring the *error* between Ziggy's uncorroborated gut read and the
  corroborated pipeline. Bringing in outside opinions at that stage would
  contaminate the measurement it's designed to produce.

## Bringing things back

Nothing in this folder auto-syncs. If a conversation elsewhere produces
something worth keeping — a new angle, a connection between clusters, a
counterargument — relay it back and it gets filed through the normal
route (a new idea trail, a dig lead, or a note in the Dig Map), not
pasted in raw.

---

**Filed:** `circle/SYNC_OUT/README.md`
**Status:** starter packet — expand deliberately, don't bulk-mirror the
whole archive in here
**Last updated:** 2026-07-22
**Beefed up 2026-07-22** by Repo (Nyquist) Claude — reframed the raw-dig
workbooks as prime (94–97% content) material behind a strippable wrapper,
and added the "Staging the raw digs" treatment + tiered-corpus + 50-source
guidance from the LLM_BOOK / NotebookLM side of the pipeline.
