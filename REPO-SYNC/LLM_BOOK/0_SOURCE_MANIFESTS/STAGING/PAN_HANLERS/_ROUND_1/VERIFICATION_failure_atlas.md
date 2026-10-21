# Two-Source Verification — The Failure Atlas (Round 1, Q5)

**Date:** 2026-10-03
**Method:** same discipline as `VERIFICATION_abandonment_rule.md` — cross-check
NotebookLM's Q5 synthesis against the *raw dig* OUTPUT (SW17, SW18, SW19,
SW20, AUX_02 workbooks in `Pan_Handlers/circle/evidence/chat_extractions/`),
one adversarial verifier per claimed incident, instructed to refute.
**Verdict: PARTIAL PASS — all four incidents are REAL (zero event
fabrication), but the prose carries systematic distortions and must not be
cited as-written.** The four patterns are better grounded in the primary
record than in Q5's retelling. Build the atlas from the workbooks; use Q5
as a finding aid only.

## Scope note

The four-pattern taxonomy (detector-vs-disease, formal-authority leakage,
self-sealing, bracketing-to-privilege drift) was supplied by the *question*,
not the model. What NotebookLM contributed — and what was verified — are the
four concrete incidents.

## Incident-by-incident

### 1. Detector-vs-disease (claimed site: SW20) — PARTIAL

- **Real but stitched from two digs.** The Evaluative-Premise Audit →
  Baseline Exemption mismapping happened in **SW19**, not SW20 (the string
  "Evaluative-Premise Audit" never occurs in the SW20 workbook). SW19 line
  8104 has the original error ("MATCHES Baseline Exemption"); lines 8144–8148
  the correction ("DETECTOR / CORRECTIVE RELATION … asking whether an
  exemption exists is not itself the exemption").
- **The PTDS claim overstates.** SW20's superseded Stage 4 never mapped
  Prediction–Truth Direction Separation *as* Prediction Sovereignty — it said
  "It is not itself Prediction Sovereignty" (line 7785). The corrected error
  was subtler: describing a counter-operation as "partially overlap[ping]
  Universalized Evaluative Jurisdiction" (line 7788 → corrected 8943–8948).
- **"Repeatedly" is wrong per-operation.** Each operation was mischaracterized
  exactly once. What repeated: five registry-direction errors across five
  *different* operations in SW20's one Stage-4 output (line 8943), and the
  cross-dig chain ("eighth consecutive dig," lines 8925–8929, IT-126).
- **One parenthetical contradicts the source.** "Smuggles values" imports the
  exact framing SW19 disavowed: "'Smuggling' is not the operator" (line 2803);
  "Grant never directly claimed neutrality or concealed a premise" (8146–48).

### 2. Formal-authority leakage (AUX_02) — SUBSTANTIALLY CONFIRMED, two distortions

- CONFIRMED: invariance/cross-model-convergence topic; the
  transformation-class disanalogy acknowledgment (lines 865, 1006–1019,
  2529); the label's retention across stages; and **"formality inflation" is
  verbatim in the source** (AUX_02 line 2527 — a recurring self-audit
  category, also in SW10).
- Distortion 1: **"debate" overstates** — the bounded source is one Ziggy
  question plus one unchallenged assistant reply (line 2547; "No genuine
  dispute between Grant and Ziggy occurs," line 386).
- Distortion 2: **outcome hardened.** The workbook flags and defuses the risk
  ("The extraction *risks* making an informal analogy sound more formal,"
  2529; field desk: "Do **not** promote 'epistemic invariant,'" line 11) —
  Q5 reports a consummated effect ("*made* an informal analogy sound
  technically proven").
- **Stitched quote.** "The correction arrives; the residue stays" appears
  nowhere in AUX_02; it lives in IT-038 / IDEA_TRAILS_INDEX row 38 (seeded by
  SW07's entropy case). IT-038 never mentions AUX_02 or invariance. The
  phrase was lifted from a different finding's index row and welded on.

### 3. Self-sealing (SW17 + SW19) — CONFIRMED events, materially incomplete framing

- CONFIRMED with citations: the offloading diagnosis (SW17 Move 9,
  lines 1268–1281; Nova's supporting role, 2320), the "pedantic" label
  (SW19 lines 510–528, 856–862), and resistance-read-as-confirmation
  (SW17 Loop 6, 1750–1759; SW19 Loop 4, 6613–6617).
- **But nearly every grounding passage IS the archive's own audit layer
  catching it:** SW17's A1-6 "Disconfirmation Test for the Offloading
  Diagnosis," the quarantines ("no accountability-avoidance …
  extraction; seven alternatives live," 1855–57), the standing control
  "Denial of an interpretation cannot automatically count as confirmation"
  (2991); and SW17's counterevidence Finding 14: the loop "was not fully
  closed to revision" — Ziggy repeatedly re-tested his own diagnosis in-chat.
- **In SW19 the self-scrutiny happened inside the source conversation
  itself** (Dispute 9 / Z19: Ziggy asks whether he overuses "pedantic"),
  with the assistant pushing *against* person-labeling (Move 19,
  label-to-process translation) — the opposite of co-building that label.
- Vocabulary: **"accountability offloading" is verbatim in neither
  workbook** (SW17's terms: antecedent offloading / agency offloading /
  accountability avoidance). "Pedantic" appears only in SW19, "offloading"
  only in SW17.
- Honest counterweights, kept: the in-chat Loop 6 dynamic did occur at
  points, and SW19's own audit weakened the self-audit's corrective depth
  ("mainly reassurance and phrasing adjustment," 5051–52). A kernel of Q5's
  criticism survives — as a *locally occurring, audit-qualified* dynamic,
  not the categorical "failing to treat his denial as potentially
  legitimate."

### 4. Bracketing-to-privilege drift (SW18, Voynich) — CONFIRMED, strongest of the four

- CONFIRMED on all substance: the Voynich inquiry as auxiliary corpus
  (lines 1538–45); **"Meaningful-Hypothesis Bracketing" is the workbook's own
  verbatim operator name** (line 1829, ~25 occurrences); hoax/gibberish
  bracketed for pattern-search (1834, 895–897); and the never-restored
  finding is **the workbook's own, recorded repeatedly** (Omission 6, line
  3675; "restoration never occurs," 3973; "not visibly restored," 8220).
- Shadings: "asymmetric preservation" drops the middle word of the
  workbook's term ("asymmetric **possibility** preservation," line 1849);
  and "dominate the inquiry" overstates — the workbook holds domination as
  an *unresolved confirmation risk* ("asymmetric follow-through remains
  unresolved," 4256) and quarantines the move from the profile (6609).

## The meta-finding

Q5's distortion pattern reproduces failure modes the archive itself named:

1. **Flattening the audit layer into actor behavior** — incidents 2 and 3
   present caught-and-controlled failures as if they ran uncaught. This is
   the archive's own case law ("extraction products are never actor
   evidence," SW14) violated by the downstream reader.
2. **Modal hardening** — "risks becoming self-sealing" → "failing to treat
   his denial…"; "risks making … sound more formal" → "made … sound
   technically proven." Kin to the claim-strength-drift seed (AUX_06).
3. **Cross-source stitching** — a SW19 incident filed under SW20; IT-038's
   signature phrase welded onto AUX_02. A provenance failure the dig
   discipline exists to prevent.

The irony is load-bearing: the answer *about* the failure atlas is itself a
fresh specimen for it.

## Comparison with Q7/Q8

The abandonment rule passed clean (zero confabulation). Q5 shows zero
*event* fabrication but systematic attribution/strength distortion. Working
hypothesis for Round 2 question design: Q7/Q8 asked the model to **build**
from flagged gaps (synthesis task — NotebookLM strong); Q5 asked it to
**report** incidents with provenance (citation task — NotebookLM lossy).
Prefer build-shaped questions; treat report-shaped answers as leads.

## Caveats & routing

- Still n=1 NotebookLM pass; this verification is against primary sources.
- **Routing: Q5 does NOT clear as-written.** The four *patterns* clear —
  each is independently grounded in the primary record (IT-126, IT-038,
  IT-067, and SW18's own findings). Downstream consumers (report.md
  Report 2, Infographic 3, Video 1; the New_9 Failure Atlas routing) must
  source from the workbooks or this verification, never from Q5 prose.
- Verifier run: 4 adversarial agents, 2026-10-03, Master Repo Claude
  (Pan Handlers side). Line citations above are to the raw workbooks.
