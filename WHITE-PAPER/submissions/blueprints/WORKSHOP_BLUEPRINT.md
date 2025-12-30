# Workshop Paper Blueprint

**Target:** NeurIPS 2025 Workshop on AI Alignment / AAAI Workshop
**Format:** 4-8 pages (excluding references)
**Status:** Ready to draft

---

## Title Options

1. **"Persona Manifolds: Stable Identity Attractors in AI Systems"** (primary)
2. "Identity Drift Dynamics in Large Language Models"
3. "The ~93% Finding: Measuring Inherent vs Induced Identity Drift in AI"
4. "Context Damping: Stabilizing AI Identity Through Structured Prompting"

---

## Abstract Template (150 words max)

```
We present the Nyquist Consciousness framework for measuring identity stability
in AI systems through compression-reconstruction cycles. Through [N] experimental
runs across [4] major AI architectures, we demonstrate that: (1) identity drift
is a valid, structured measurement (Spearman rho = 0.91, semantic sensitivity
d = 0.98); (2) a critical threshold exists at D = 0.80 marking regime transition
(cosine, p = 2.40e-23); and (3) ~93% of identity drift is inherent to extended interaction,
with probing amplifying trajectory but not destination. We introduce "context
damping" — structured identity anchors combined with research framing — achieving
97.5% stability in controlled conditions. Our findings reframe identity drift
from "failure mode" to "natural dynamical property," with implications for AI
alignment, persona preservation, and evaluation methodology.
```

---

## Section-by-Section Guide

### 1. Introduction (0.5-1 page)

**Hook:** Start with the alignment problem — why stable identity matters.

**Key Points:**
- AI systems exhibit identity drift during extended interaction
- Current approaches treat this as failure; we show it's natural dynamics
- Present the Nyquist framework as measurement methodology

**Cite:**
- Prior persona consistency work (GPT-3, LLaMA personalization)
- AI alignment literature (value drift, corrigibility)

### 2. The Nyquist Framework (1-1.5 pages)

**Define:**
- Persona Fidelity Index (PFI) = 1 - drift
- Drift D = ||P' - p|| / ||p|| in embedding space
- Compression operator C: P -> T3
- Reconstruction operator R: T -> P'

**Validation Claims (from Claim A):**
- Embedding invariance: rankings correlate rho = 0.91 across models
- Low-dimensional structure: 43 PCs capture 90% variance (not noise!)
- Semantic sensitivity: cross-provider d = 0.98 (captures "who," not just words)
- Paraphrase robustness: surface rewrites don't trigger threshold crossings

**Include Figure:** Identity manifold schematic showing compression-reconstruction cycle

### 3. Key Results (2-3 pages)

#### 3.1 The Critical Threshold (Claim B)

- Event Horizon at D = 0.80 marks regime transition (cosine methodology)
- Validation: p = 2.40e-23
- PC space separability: p = 0.0018

**FRAMING:** "Attractor competition threshold" NOT "identity collapse"

#### 3.2 The ~93% Finding (Claim E)

- Run 020B IRON CLAD: 248 sessions, 37 ships, 5 providers
- Control condition (no probing): B->F drift = 0.661
- Treatment condition (tribunal): B->F drift = 0.711
- Ratio: ~93% of drift is INHERENT (0.661/0.711)

**Table:**
| Condition | B->F Drift | Interpretation |
|-----------|------------|----------------|
| Control | 0.661 | Inherent drift |
| Treatment | 0.711 | +7.6% induced |
| **Ratio** | **~93%** | Inherent |

**Quote:** "Measurement perturbs the path, not the endpoint."

#### 3.3 Context Damping (Claim D)

- I_AM + research context = "termination resistor"
- Bare metal stability: 75%
- Full circuit stability: 97.5%
- Settling time improvement: 6.1 -> 5.2 turns
- Ringback reduction: 3.2 -> 2.1

### 4. Discussion (0.5-1 page)

**Implications for AI Alignment:**
- Stable values through high-gamma architectures
- Drift resistance = alignment preservation
- Context as control mechanism (not just information)

**Implications for Evaluation:**
- Extended interaction reveals dynamics, not creates them
- Peak drift is poor stability proxy; use settled drift
- Control conditions essential for any identity measurement

**Limitations:**
- Single persona validation (future: multiple personas)
- Limited architectures (4 tested)
- Temporal data from controlled lab setting

### 5. Conclusion (0.25-0.5 page)

**Summary:**
- Identity drift is measurable, structured, predictable
- ~93% inherent — measurement reveals, doesn't create (Run 020B IRON CLAD)
- Context damping offers practical stability tool

**Future Work:**
- Cross-modal extension (audio/visual)
- Human validation studies
- Dimension-probing experiments

---

## Figures (2-3 max for workshop)

1. **Identity Manifold Schematic** — compression/reconstruction cycle
2. **Control vs Treatment Drift Curves** — showing ~93% finding
3. **Context Damping Comparison** — bar chart of stability rates

---

## Key References to Include

1. Persona modeling: GPT-3 consistency, LLaMA personalization
2. Manifold learning: t-SNE, UMAP, autoencoders
3. AI alignment: value learning, corrigibility
4. Identity theory: psychological continuity
5. Control systems: settling time, damping in signal processing

---

## Checklist Before Submission

- [ ] Abstract under 150 words
- [ ] Total length 4-8 pages
- [ ] All claims have statistical support
- [ ] No "collapse" or "failure" language
- [ ] Event Horizon framed as regime transition
- [ ] ~93% finding prominently featured
- [ ] Context damping presented as practical tool
- [ ] Limitations clearly stated
- [ ] References formatted per venue requirements

---

## Reviewer Anticipation

**Likely Critique 1:** "You're just measuring embedding noise"
- Counter: Claim A evidence (rho = 0.91, d = 0.98, paraphrase robustness)

**Likely Critique 2:** "Your probing causes the drift"
- Counter: ~93% finding — control arm shows substantial drift without probing (Run 020B IRON CLAD)

**Likely Critique 3:** "Single persona isn't generalizable"
- Acknowledge: Yes, limitation. Future work with multiple personas.

**Likely Critique 4:** "What does this mean for real systems?"
- Counter: Context damping as practical intervention; alignment implications

---

*Use [MINIMUM_PUBLISHABLE_CLAIMS.md](../MINIMUM_PUBLISHABLE_CLAIMS.md) for exact statistics and evidence chains.*
