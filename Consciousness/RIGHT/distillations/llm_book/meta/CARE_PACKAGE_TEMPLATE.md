# Care Package Template

**Purpose:** Standardized format for cross-pollination knowledge transfer between systems (CFA Claude, Nova, NotebookLM projects, Pan Handler labs). Designed so a cold reader six months from now knows exactly what to do with it.

**When to use:** Whenever findings from one domain need to be delivered to another system that wasn't part of the original analysis. Not for internal analysis files (use INSIGHTS/, CONNECTIONS/, EXPERIMENTS/ for those).

---

## Template

```markdown
# Care Package: {Source Title}

**From:** {Source project / LLM Book entry / experiment}
**To:** {Target system / person / lab}
**Date:** {YYYY-MM-DD}
**Priority:** {HIGH | MEDIUM | LOW} — {one-line justification}

---

## Context

{2-3 sentences: What work produced these findings? What has the recipient already seen
(if anything)? What framing constraints apply?}

**Framing reminder:** {Any constraints on how to present the findings — e.g., "independent
convergences, not borrowed authority"}

---

## Finding 1: {Short Title}

{What was found, with enough detail to act on. Include the source question/response
reference (e.g., "Q17" or "Report 5") so the recipient can trace back.}

**{Target} implication:** {What this means specifically for the recipient's domain.
Not "this is interesting" — "this changes X about how you do Y."}

---

## Finding 2: {Short Title}

{Same structure. Repeat for each finding.}

**{Target} implication:** {Specific actionable consequence.}

---

## Finding N: ...

---

## Summary of Actionable Items

| # | Finding | Recommended Action |
|---|---------|-------------------|
| 1 | {Title} | {Specific action — "update X," "test against Y," "evaluate as Z"} |
| 2 | {Title} | {Action} |
| N | {Title} | {Action} |

---

## Source Files

{List of file paths the recipient can read for full context. Use stable paths.}

- `path/to/chat.md` — {what's in it}
- `path/to/report.md` — {what's in it}
- `path/to/specific_artifact.md` — {why this one matters}

---

*Care package generated: {YYYY-MM-DD}*
*Source: {QUESTIONS_OUT.md section or routing.md reference}*
```

---

## Guidelines

### What goes in a care package

- **Findings that change how the recipient works** — not just "interesting parallels" but "this means you should do X differently"
- **Precise definitions** that upgrade hedged language to categorical claims
- **Testable predictions** against data the recipient already has
- **Diagnostic tools** (checklists, rubrics, calibration protocols) that translate cleanly
- **Independent validation** from systems with no shared context

### What does NOT go in a care package

- Raw Q&A dumps (use INSIGHTS/ for those)
- Vague "this resonates with your work" connections (use CONNECTIONS/ for those)
- Experiment designs the recipient can't run yet (use EXPERIMENTS/ for those)
- Anything requiring the recipient to read the full source material to understand

### Quality checklist

Before sending:

- [ ] Every finding has a specific implication for the recipient's domain
- [ ] Framing constraints are stated (independent convergence vs borrowed authority, etc.)
- [ ] Actionable items table includes at least one retroactive test (analyze existing data, not just "run new experiment")
- [ ] Source file paths are stable and correct
- [ ] Package stands alone — recipient doesn't need prior conversation context

### Format notes

- **5-7 findings maximum.** If you have more, you're writing an analysis document, not a care package. Prioritize.
- **Implication lines are mandatory.** A finding without "what this means for you" is a fact, not a transfer.
- **The actionable items table is the most important section.** Many recipients will read only this. Make it complete.

---

## Reference Implementation

See: `experiments/temporal_stability/S7_ARMADA/12_CFA/SYNC_OUT/pending/cognitive_physics_care_package.md`

CFA Claude's review of this package (2026-07-05): "One of the better pieces of knowledge-transfer writing I've seen come through the repo." Key feedback: should have connected Experiment 8 to existing data rather than framing as future work. Updated guideline: always include at least one retroactive test.

---

*Template created: 2026-07-05*
*Based on: cognitive_physics_care_package.md (New_8 → CFA Claude)*
*Feedback incorporated from: CFA Claude review (2026-07-05)*
