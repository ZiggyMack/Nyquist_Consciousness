# Concept Pair Template

Use this when promoting a concept into both hemispheres.

Replace bracketed fields before promotion.

---

## LEFT File Template

Target path:

```text
Consciousness/LEFT/galleries/[gallery]/[concept_slug].md
```

```markdown
# [Concept Name]

**Consciousness Status:** [distilled | historical-distilled | seed | needs-refresh]
**Metric Domain:** [cosine-current | legacy-rms | mixed | non-metric]
**Source Signals:** [run IDs, sync files, maps, LLM Book batch, paper section]
**Paired RIGHT File:** `../../../RIGHT/galleries/[gallery]/[concept_slug].md`
**Last Reconciled:** [YYYY-MM-DD] against [authority]

---

## Claim

[State the narrow claim plainly.]

## Evidence Anchor

| Evidence | Path / ID | Notes |
|----------|-----------|-------|
| [source] | `[path]` | [why it matters] |

## Method / Metric

[Define metric, methodology, or formal distinction.]

## Caveats

- [Boundary condition]
- [Historical conflict or uncertainty]

## What This Permits Us To Say

[Allowed public/internal phrasing.]

## What This Does Not Prove

[Guardrail against overreach.]
```

---

## RIGHT File Template

Target path:

```text
Consciousness/RIGHT/galleries/[gallery]/[concept_slug].md
```

```markdown
# [Concept Name]

**Consciousness Status:** [distilled | historical-distilled | seed | needs-refresh]
**Metric Domain:** [cosine-current | legacy-rms | mixed | non-metric]
**Source Signals:** [run IDs, sync files, maps, LLM Book batch, paper section]
**Paired LEFT File:** `../../../LEFT/galleries/[gallery]/[concept_slug].md`
**Last Reconciled:** [YYYY-MM-DD] against [authority]

---

## Core Image

[The metaphor, shape, or felt pattern.]

## What The Image Explains

[How the metaphor helps understanding.]

## What The Image Does Not Prove

[Keep the metaphor honest.]

## Pattern Connections

- [Related concept]
- [Related run or synthesis]

## Implications

[What this changes about how the project thinks or works.]

## Open Questions

- [Question]
```

---

## BRIDGE Promotion Row

Add a row to:

```text
Consciousness/PROMOTION_LEDGER.md
```

```markdown
| YYYY-MM-DD | [Concept Name] | [Source Signal] | `LEFT/...`, `RIGHT/...` | [status] | [metric domain] | [short note] |
```

