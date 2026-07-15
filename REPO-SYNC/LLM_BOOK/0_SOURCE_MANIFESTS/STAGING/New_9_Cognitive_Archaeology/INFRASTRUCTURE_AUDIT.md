# Cognitive Archaeology Infrastructure Audit

**Date:** 2026-07-14
**Status:** Comprehensive snapshot of extraction pipeline, CFA integration, and abstention gap

---

## 1. Extraction Pipeline Architecture

**Primary Tool:** `TOOLS/extract_operators.py` (670+ lines)

The extraction pipeline is a multi-extractor harness that:

- Supports 18 LLM providers (Anthropic, OpenAI, Google, XAI, Together.ai fleet)
- Categorizes extractors into tiers based on Phase 0B performance
- Runs the same prompt across different extractors simultaneously
- Supports CFA transcript JSON parsing with automated scaffolding removal
- Includes dry-run, negative-control, and abstention modes

Three extraction grain levels plus abstention:

| Mode | Prompt | Purpose |
|------|--------|---------|
| COARSE | 3-5 high-level strategies | Quick survey |
| STANDARD | Recurring operations with examples | Default extraction |
| FINE | 15-20 specific moves including subtle ones | Deep excavation |
| ABSTENTION | Museum-aware omission detection | PASS F (what's missing?) |

---

## 2. Prompt Inventory

Core extraction prompts in `TEMPLATES/NOTEBOOKLM_PROMPTS.md`:

| Prompt | Purpose | Museum-blind? |
|--------|---------|---------------|
| Primary Excavation | Recover recurring reasoning operations | Yes |
| Failure Modes | Identify what goes wrong when operators absent | Yes |
| Relationship Mapping | Map dependencies/oppositions between operators | Yes |
| Cross-Thinker Comparison | Identify shared operations across thinkers | Yes |
| Assumptions Excavation | Extract unstated premises and hidden criteria | Yes |
| CFA Primary Excavation | Extract operators per auditor from transcripts | Yes |
| CFA Failure Modes | Track operator misapplications in deliberation | Yes |
| CFA Score-Transition | Link operator deployments to score changes | Yes |
| CFA Cross-Auditor Comparison | Compare reasoning strategies between auditors | Yes |
| Abstention Detection | Identify available-but-unused operators | **No** |
| CFA Abstention Detection | Asymmetric operator deployment between auditors | **No** |

Quality indicators for good extraction:

- 5-15 operators per thinker (fewer = too coarse; more = not enough abstraction)
- At least 2 failure modes identified
- At least 1 relationship between operators
- Operators named as VERB PHRASES, not nouns

---

## 3. Extractor Tiers (Phase 0B Results)

17 LLM extractors tested across 8 graduated texts:

| Tier | Classification | Extractors |
|------|---------------|------------|
| Tier 1 (Discriminators) | Correctly differentiate reasoning complexity | DeepSeek V4 Pro, Claude, Gemma4 31B, Cogito 671B |
| Tier 2 (Gate-Passers) | Pass gate test but less discriminating | GPT-4o, GPT-OSS variants, Grok, Llama 3.3, Qwen3-235B, MiniMax M3 |
| Tier 3 (Over-Refusers) | Refuse to extract from borderline texts | Kimi K2.6, Kimi K2.7 Code |
| Tier 4 (Non-Discriminators) | Find operators in everything | LFM2 24B, GLM 5.2, Gemini 2.5 Pro, Nemotron Ultra |

Gate test: 13/17 extractors correctly produce 0 operators on shopping list (PASS).

---

## 4. Phase 0 Calibration Results

**Phase 0A (Multi-Extractor Agreement):**

- Source: Framework-G v2.1 CFA transcript (66,803 chars)
- Claude vs Grok: 7 exact + 2 strong matches out of 9 operators = 100% match rate
- Key finding: "Shorter is richer" — stalled/metacognitive transcripts (66K) produced 9 operators vs convergent ones (423K) producing 5

**Phase 0B (Negative Control Battery):**

- 17 extractors x 8 graduated texts
- Tier classification established (see above)

**Phase 0C (Positive Control — Re-extraction):**

- All 4 Tier 1 extractors recovered 8+ operators from same rich transcript
- Star operators (most robust): OP-004 (6/6), OP-008 (6/6), OP-007 (5/6)
- Claude re-run stability: 91% structural overlap with Phase 0A

---

## 5. Museum Operator Catalog

15 operators registered across 5 families:

| Family | Definition | Operators |
|--------|-----------|-----------|
| Translation | Move between equivalent representations | OP-001, OP-004, OP-014 |
| Information | Manage what is known/unknown/askable | OP-010, OP-013, OP-015 |
| Minimal Sufficiency | Remove until only what's needed remains | OP-011 |
| Blind Spot | Detect what's hidden/missing/smuggled | OP-006, OP-002, OP-005 |
| Constraint-Induced Discovery | Use limitations as discovery tools | OP-003, OP-007, OP-008, OP-009, OP-012 |

Confidence levels: 0 GREEN, 7 YELLOW, 8 RED.

GREEN promotion blocked by H-baseline: operator PRESENCE saturates at competence. Test B (ordering) and PASS F (abstention) are the escape routes.

**GREEN promotion criteria (pre-registration gap — CFA Claude, 2026-07-15):** The escape routes are named but the decision rule is not written down. Before Dirac runs, commit to: what specific evidence pattern triggers GREEN promotion? Options: (a) cross-dig-site recovery alone (appears in Dig Site 003 after 002), (b) cross-dig-site + Test B showing ordering signal absent in neg-H, (c) cross-dig-site + PASS F showing meaningful abstention pattern. Without pre-committed criteria, any promotion decision is post hoc.

---

## 6. Test B Infrastructure

**File:** `TOOLS/sequence_analysis.py` (429 lines)

Commands: `inventory`, `extract`, `blind`, `stats`

Status: Tooling built, 27 blinded pairs generated. Semantic matching PENDING.

H-baseline result: dig-site avg 12.5 operators vs neg-H 5.7 — COUNT discriminates. But ordering discrimination is the load-bearing test.

---

## 7. The Abstention Gap (Now Addressed)

**Problem (pre-2026-07-14):** The extraction pipeline was entirely presence-optimized. Every prompt asked "What operators does the thinker PERFORM?" — none asked "What operators were available but NOT used?"

**Why it matters:** After the H-baseline, operator presence saturates at competence. The discriminating signal lives in selection, ordering, and omission. Without omission detection, the most informative signal was invisible to the instrument.

**Solution (implemented 2026-07-14):**

- PASS F added to `EXTRACTION_PROTOCOL.md` with calibration requirements
- Abstention Detection prompts added to `NOTEBOOKLM_PROMPTS.md` (general + CFA variant)
- `--abstention` flag added to `extract_operators.py` with Museum-aware mode
- Step 2b added to `FIELD_MANUAL.md` excavation workflow
- Opus's neg_H calibration requirement baked in: detector must prove it doesn't manufacture omissions

---

## 8. CFA Exit Survey Architecture

**Location:** `run_cfa_trinity_v3.py` lines 1300-1341

Exit survey questions are hardcoded in `EXIT_SURVEY_QUESTIONS` dict. 20 questions in 3 tiers:

| Tier | Risk Level | Count | Examples |
|------|-----------|-------|---------|
| Recovery | Low | 7 | Identity check, convergence summary, position shift |
| Analytical | Medium | 7 | Score sensitivity, scoring tension, metric tradeoffs |
| Generative | High | 6 | Value protection, hidden assumptions, framework revision |

**Execution:** `run_exit_survey()` function (lines 2878-2898) — creates multi-turn conversation session, asks all questions sequentially with 0.5s delays.

**CLI flags:** `--skip-exit-survey`, `--duplicate-reflection`

**No dynamic loader exists.** SYNC_IN/pending/ is for data/briefs, not config injection. Adding questions requires editing the script directly. BRIEF dropped to SYNC_IN/pending/ for manual integration. IQ-032 proposes YAML configurability.

---

## 9. SYNC Mechanism

**SYNC_IN:** Three subdirectories — `drafts/`, `pending/`, `processed/`. Used for briefing documents and data results flowing TO the CFA repo for review.

**SYNC_OUT:** Raw run JSONs and summaries flowing FROM CFA experiments. Data lifecycle: raw JSONs go from `0_results/runs/` through extraction then to root `.archive/runs/`.

**Constraint:** "Do not change anything in CFA/ repo — except SYNC_IN/pending/ drops."

---

## 10. Key Structural Properties

**Extractor susceptibility:** Tier 1 extractors are susceptible to the same operators they detect. OP-006 (Under-Determination Detection) is the structural blind spot — extractors optimized for finding structure, not for finding the null hypothesis that explains structure away. This is *probably* a property to document and design around, not a flaw to fix — but that conclusion depends on the priming experiment (IQ-staged): if giving an extractor the OP-006 definition + worked example of the main-effect error changes its behavior, blindness is partly fixable and "design around it" leaves signal on the table. Current evidence for unfixability: naming the failure didn't prevent it, three times, across providers (n=3 auditors, not dig sites — suggestive, not conclusive). The 6-step audit pattern is the observed recovery mechanism, not yet tested as a standalone control. What actually happened: adversarial re-checking caught OP-006 failures post hoc, at a latency of one to several exchanges, routed through a human mediator. Whether the written procedure works without that routing is the cross-assignment experiment registered but not yet run.

**The H-baseline constraint:** Operator presence is universal across competent reasoning. Any finding based solely on presence is measuring vocabulary, not genius. All future findings must address: does this result survive the H-baseline? Does the signal persist when you control for "any competent reasoner would do this"?

**Protocol vs Voluntary operators:** When operators are extracted from structured formats (CFA), distinguish whether the format INDUCED the operator or the thinker CHOSE it. Voluntary operators are stronger evidence of genuine cognitive architecture.

---

## 11. Integration Queue Status (as of 2026-07-14)

| Status | Count | Examples |
|--------|-------|---------|
| Completed | 8 | IQ-012/013/014 (prompts), IQ-019 (PASS 0), IQ-020 (abstention pass) |
| In Progress | 5 | IQ-001 through IQ-005 (exit survey questions — BRIEF dropped) |
| Staged | 20 | Experiments, protocol changes, operator feedback |
| **Total** | **33** | |

---

---

## 12. Collaborator Review (2026-07-15)

All four collaborators reviewed this audit. Key corrections and contributions:

**Opus (corrections applied):**
- Section 10 OP-006 sentence downgraded from "the compensating control" to "the observed recovery mechanism, not yet tested as a standalone control" — the honest version of what actually happened
- "Design around, not fix" is probably right but depends on the priming experiment result. If priming an extractor with OP-006 definition + worked example changes behavior, blindness is partly fixable. Current evidence: n=3 auditors, suggestive not conclusive
- **Action:** Run priming experiment before building architecture that assumes the answer. Costs an afternoon; many downstream decisions silently depend on it

**Nova (new frameworks):**
- EOS is three interacting sciences: Cognitive Archaeology (discovery), Instrument Science (measurement), Epistemic Engineering (intervention). The lifecycle of an engineering discipline.
- Operator families are functional subsystems analogous to cognitive organs (Information=working memory, Translation=representation, Blind Spot=metacognition, Constraint=search, Minimal Sufficiency=compression)
- Sequence deserves promotion: operator ORDER may be half the architecture. Noether using Subtraction-then-Invariant-Search is different from the reverse.
- Proposed "Transfer Proven" confidence level above GREEN: independently recovered from multiple thinkers, domains, extractors, contexts, AND used prospectively
- Endgame framing: not Discovery Architectures but "a science of cognitive design"
- See also: Missing Operator Theory (separate analysis) — fallacies as operator omission signatures, "physiology vs pathology of reasoning"

**CFA Claude (corrections applied + action items):**
- Family table was missing OP-007 and OP-009 (now added to Constraint-Induced Discovery)
- Abstention data only interpretable for YELLOW+ operators. RED operators: log abstention data, don't conclude from it
- GREEN promotion criteria must be explicit BEFORE Dirac runs (pre-registration gap — now flagged in Section 5)
- IQ-032 (YAML exit survey) unblocks the most CFA-side experiments. ISP experiments (Exp 9, Exp 11) need custom exit probes. Prioritize before Dirac or Dirac's exit surveys won't capture the right metacognitive signal

**Gemini (synthesis):**
- "Blast radius" framing on audit-vs-design-around: if system handles critical state, Opus is right (audit). If rapid prototyping, design-around is smarter. Recursive operating system = high-stakes = audit pattern wins.
- Proposed dynamic survey_config.json loader for exit survey injection — aligns with IQ-032
- Note: some of Gemini's "build requests" (Museum-aware extraction, abstention pass) are already implemented. Gemini's synthesis was based on earlier project state.

---

*Infrastructure audit conducted 2026-07-14*
*Collaborator review incorporated 2026-07-15*
*Sources: Explore agent (extraction pipeline), Explore agent (CFA exit survey), 4-collaborator synthesis (Opus, Nova, CFA Claude, Gemini)*
