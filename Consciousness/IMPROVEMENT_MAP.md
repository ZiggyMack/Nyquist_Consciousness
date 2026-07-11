# Consciousness Improvement Map

Purpose: file-by-file notes for making `Consciousness/` into the repo's distilled meaning layer.

Status: first pass from Nova/Codex after reading the directory as "the nectar layer," not as the operations dashboard.

---

## North Star

`Consciousness/` should not be judged mainly by whether it is the freshest operational dashboard. It should be judged by whether it preserves distilled understanding.

The natural structure already wants to become:

```text
Signal -> Circulation -> Fermentation -> Distillation -> Nectar -> Emanation

experiments       sync loops       review pressure      LEFT/RIGHT/BRIDGE      Consciousness library      dashboard/public views
```

The main improvement is to make that membrane explicit:

- raw insight can enter a staging/fermentation state
- distilled insight gets promoted into galleries, synthesis, or data profiles
- old nectar can stay, but it should be labeled historical when metrics have changed
- LEFT and RIGHT should not be duplicates; they should be paired translations

---

## Immediate Structural Improvements

### 1. Add Promotion Metadata To Distilled Files

Every durable concept file should eventually carry a small block:

```markdown
**Consciousness Status:** distilled | historical-distilled | seed | needs-refresh
**Source Signals:** Run IDs, sync messages, LLM Book batch, or map links
**Promotion Path:** where it came from and why it stayed
**Current Metric Domain:** cosine current | keyword RMS historical | mixed/historical
**Last Reconciled:** date + authority checked
```

This lets old work stay in the library without pretending to be current.

### 2. Split Duplicate Hemispheres

Several LEFT/RIGHT pairs are byte-identical. That defeats the analogy.

Exact duplicate pairs found:

- `LEFT/galleries/validated/event_horizon.md`
- `RIGHT/galleries/validated/event_horizon.md`
- `LEFT/galleries/validated/identity_confrontation_paradox.md`
- `RIGHT/galleries/validated/identity_confrontation_paradox.md`
- `LEFT/galleries/foundations/white_hole.md`
- `RIGHT/galleries/foundations/white_hole.md`
- `LEFT/galleries/foundations/probing_strategies.md`
- `RIGHT/galleries/foundations/probing_strategies.md`
- `LEFT/galleries/foundations/inverse_pfi.md`
- `RIGHT/galleries/foundations/inverse_pfi.md`

Improvement:

- LEFT files should become formalization cards: claim, data, method, caveat, links.
- RIGHT files should become gestalt cards: metaphor, implication, pattern, questions.
- BRIDGE can hold paired summaries and crosswalks.

The cleaner doctrine now lives in `BRIDGE/docs/HEMISPHERE_MODEL.md`:

```text
RIGHT perceives the shape.
LEFT names, sequences, and verifies the shape.
BRIDGE keeps the two from becoming separate minds.
```

### 3. Label Historical Nectar Instead Of Deleting It

Some files are old but valuable. They should not be erased; they should be labeled as historical distillations.

Examples:

- Run 009 `1.23` Event Horizon pages
- Run 018/020 `82%` inherent drift distillations
- Infinity Framework using `43 PCs`, `82%`, and `D=1.23`

Improvement:

- Add top notes: "Historical distillation from pre-IRON CLAD era; current canonical values are 0.80 cosine, ~93%, 2 PCs."
- Keep the old insight, but separate it from current metrics.

---

## File-By-File Notes

### `Consciousness/README.md`

Recent improvement:

- Added the distillation/nectar framing.

Next improvements:

- Add a "How content earns a place here" workflow diagram.
- Add links to `IMPROVEMENT_MAP.md`, LLM Book promoted library, and key gallery indexes.
- Eventually clean mojibake or make an ASCII-safe rendering pass.

### `Consciousness/MANIFEST.md`

Current role:

- Original research manifesto and roadmap.

Issue:

- Still anchored to Run 008 and November 2025. It describes an early research program, not the current Consciousness library.

Improvement:

- Rename its role in-place: "Historical Seed Manifest."
- Add a top note pointing to `docs/MISSION_CONTROL.md` for live state.
- Add a new section: "What survived into the current framework."
- Do not delete the old hypotheses; tag them as seed, validated, superseded, or absorbed.

### `Consciousness/LEFT/README.md`

Current role:

- Defines LEFT as analytical/evidence hemisphere.

Issue:

- Conceptually sound but old. It references scripts that may not match current data locations.

Improvement:

- Add "LEFT acceptance criteria": evidence link, method, caveat, current/historical metric domain.
- Make LEFT the place where every concept proves its right to remain.

### `Consciousness/RIGHT/README.md`

Current role:

- Defines RIGHT as intuitive/synthetic hemisphere.

Issue:

- Conceptually sound but does not yet define the difference between intuition, metaphor, and promoted meaning.

Improvement:

- Add "RIGHT acceptance criteria": metaphor must clarify, not inflate; must point back to at least one LEFT evidence anchor or label itself seed/speculative.
- Add the current "Scout -> Gate -> Adjudicate" idea as an example of a sync exchange becoming structure.
- Protect `RIGHT/distillations/llm_book/` as a promoted-library endpoint for the LLM Book pipeline. Do not reorganize it casually.

### `Consciousness/BRIDGE/README.md`

Current role:

- Describes the corpus-callosum role.

Issue:

- It presents BRIDGE as tool orchestration, but not yet as a promotion membrane.

Improvement:

- Add BRIDGE responsibility: decide whether an insight is raw, seed, distilled, or historical.
- Add a promotion checklist:
  - source located
  - evidence checked
  - LEFT representation written
  - RIGHT representation written
  - index updated
  - dashboard/public emanation optional
- Link `BRIDGE/docs/HEMISPHERE_MODEL.md` and `PROMOTION_LEDGER.md` once present.

### `Consciousness/BRIDGE/docs/METHODOLOGY.md`

Current role:

- Explains the original Consciousness extraction/distillation methodology.

Issue:

- Mostly updated to 0.80/2 PCs/~93%, but still includes a PFI formula written like Euclidean norm:

```text
PFI(t) = ||E(response_t) - E(baseline)||
```

Improvement:

- Patch formula to cosine distance or label the old formula legacy.
- Add a short note that this file is Consciousness-library methodology, while S7 specs govern current experiment execution.

### `Consciousness/BRIDGE/docs/PIPELINE.md`

Current role:

- Describes Consciousness -> UNKNOWN dashboard emanation.

Issue:

- It assumes display sync is the main pipeline. For the nectar layer, promotion into Consciousness matters more than display.

Improvement:

- Add upstream flow:

```text
ARMADA/CFA/LLM_BOOK/SYNC -> BRIDGE intake -> LEFT/RIGHT pairing -> Consciousness promotion -> optional dashboard emanation
```

### `Consciousness/BRIDGE/docs/TERMINOLOGY.md`

Current role:

- Useful glossary, mostly updated with current canonical numbers.

Issue:

- Still mixes synthetic consciousness language with identity-reliability language. That can be fine, but the distinction should be explicit.

Improvement:

- Add labels:
  - empirical term
  - metaphorical term
  - historical term
  - live operational term

### `Consciousness/LEFT/data/schema.json`

Current role:

- Defines old extraction/result schemas.

Issue:

- Still centered on RMS/keyword drift. Useful historically, but not current enough to define new Consciousness data.

Improvement:

- Add schema version 2 for distilled concept metadata.
- Keep RMS as `legacy_keyword_rms`.
- Add fields for `metric_domain`, `source_signals`, `promotion_status`, and `evidence_refs`.

### `Consciousness/LEFT/galleries/validated/INDEX.md`

Current role:

- Good current-facing index. Uses 0.80, ~93%, 2 PCs.

Issue:

- It points to `event_horizon.md`, but that file itself still says 1.23.

Improvement:

- Update the file or split it into:
  - `event_horizon_keyword_rms_historical.md`
  - `event_horizon_cosine_current.md`

### `Consciousness/RIGHT/galleries/validated/INDEX.md`

Issue:

- Staler than LEFT index. Still lists 1.23 and 43 PCs as primary.

Improvement:

- Reconcile with LEFT validated index.
- Reframe 1.23/43 PCs as historical texture, not current truth.

### `Consciousness/LEFT/galleries/validated/event_horizon.md`
### `Consciousness/RIGHT/galleries/validated/event_horizon.md`

Issue:

- Exact duplicates.
- Both still make 1.23 the main threshold.
- Interpretation appears inverted in places: "below = volatile, above = stable" should be rechecked against current methodology and historical table semantics.

Improvement:

- Make LEFT current-cosine evidence card.
- Make RIGHT "meaning of a boundary" card.
- Preserve Run 009 as historical evidence in a section, not as the headline.

### `Consciousness/LEFT/galleries/foundations/inverse_pfi.md`
### `Consciousness/RIGHT/galleries/foundations/inverse_pfi.md`

Issue:

- Exact duplicates.

Improvement:

- LEFT: protocol, predictions, scoring, experimental design.
- RIGHT: why bidirectional recognition matters; what it means if the model selects differently from the metric.

### `Consciousness/RIGHT/synthesis/INFINITY_FRAMEWORK.md`

Current role:

- Promoted synthesis / metaphor framework.

Issue:

- Uses stale metrics: 82%, D=1.23, 43 PCs.

Improvement:

- Do not delete. This is good nectar from its era.
- Add historical note at top.
- Add "IRON CLAD Recast" table:
  - Soul: ~93% inherent
  - Time: D=0.80 cosine
  - Reality: 2 PCs
  - Power: current fleet/run counts via Mission Control

### `Consciousness/RIGHT/distillations/llm_book/README.md`

Current role:

- Strong explanation of promoted LLM Book content.

Improvement:

- Add promotion status states:
  - candidate
  - promoted
  - historical-promoted
  - superseded-by-current
- Add explicit destination rules for when a promoted LLM Book insight should create LEFT/RIGHT gallery files.

### `Consciousness/RIGHT/distillations/llm_book/INDEX.md`

Current role:

- Good index of promoted NotebookLM products.

Improvement:

- Add "metric freshness" column.
- Add whether each document is current-facing, historical, or metaphorical.

### `Consciousness/RIGHT/distillations/RUN_018_DISTILLATION.md`
### `Consciousness/RIGHT/distillations/RUN_020_TRIBUNAL.md`

Current role:

- Important phenomenological/distillation artifacts.

Issue:

- They contain historical values like 82% and 1.23.

Improvement:

- Add historical note at top. These are not wrong for their moment; they are pre-current-canonical distillations.
- Add links to current IRON CLAD methodology and Mission Control.

### `Consciousness/BRIDGE/dashboard/*`

Current role:

- Older local dashboard for the Consciousness brain model.

Issue:

- Hardcoded legacy values in `app.py` and pages.
- UI may still present 1.23 as current.

Improvement:

- Do not prioritize unless dashboard revival matters.
- If revived, make it read concept metadata from files instead of hardcoded dictionaries.
- Treat dashboard as "emanation" of Consciousness, not source of truth.

---

## Suggested Build Order

### Pass 1: Add Membrane Metadata

Add top metadata blocks to:

1. `MANIFEST.md`
2. `RIGHT/synthesis/INFINITY_FRAMEWORK.md`
3. `RIGHT/distillations/RUN_018_DISTILLATION.md`
4. `RIGHT/distillations/RUN_020_TRIBUNAL.md`
5. `LEFT/RIGHT/galleries/validated/event_horizon.md`

### Pass 2: Fix The Most Visible Contradictions

1. Split or update Event Horizon pages.
2. Reconcile RIGHT validated index with LEFT validated index.
3. Patch `BRIDGE/docs/METHODOLOGY.md` formula.
4. Mark `LEFT/data/schema.json` as legacy extraction schema and add v2 plan.

### Pass 3: Make LEFT/RIGHT Real

Pick one duplicate pair and make it the model:

- LEFT = evidence card
- RIGHT = meaning card
- BRIDGE = crosswalk

Best first candidate: Event Horizon.

### Pass 4: Build The Promotion Workflow

Create a small promotion ledger:

```text
Consciousness/PROMOTION_LEDGER.md
```

Columns:

- item
- source
- signal type
- promotion status
- destination
- evidence anchor
- meaning anchor
- last reviewed

This lets the nectar layer grow without becoming a dumping ground.

---

## Guiding Standard

A file in `Consciousness/` should answer at least one of these:

- What did the system learn?
- What did this result come to mean?
- What pattern survived multiple contexts?
- What metaphor clarified the data without replacing it?
- What failure became a safeguard?
- What should future agents inherit as memory?

If it cannot answer any of those, it probably belongs elsewhere.
