# CODE CLAUDE EXECUTION PROMPT — ADDENDUM
## Workshop Paper Specific Materials

**Context:** This addendum covers additional materials needed specifically for the NeurIPS 2025 Workshop paper that are NOT covered in the main execution prompt.

**Note:** All items in the main prompt (8 figures, 5 ASCII diagrams, references, reproducibility package) are shared across all three papers. This addendum covers workshop-specific additions only.

---

## TASK W1: Condensed Single-Page Figure Set

Workshop papers have strict page limits (4-8 pages). Create a **condensed figure panel** that combines key visualizations into a single figure.

### Figure W1: Combined Results Panel
**Filename:** `fig_workshop_combined.md` + `fig_workshop_combined.py`

**Description:** A 2x2 or 2x3 panel combining the most critical visualizations for the workshop paper.

**Panel Layout:**
```
┌─────────────────────────────────────────────────────────────┐
│  (A) PFI Validity          │  (B) 82% Finding               │
│  ┌─────────────────────┐   │  ┌─────────────────────────┐   │
│  │ ρ=0.91 scatter plot │   │  │ Control vs Treatment    │   │
│  │ across 3 embeddings │   │  │ bar chart with 82%      │   │
│  └─────────────────────┘   │  └─────────────────────────┘   │
├─────────────────────────────┼───────────────────────────────┤
│  (C) Context Damping        │  (D) Oobleck Effect           │
│  ┌─────────────────────┐   │  ┌─────────────────────────┐   │
│  │ Before/After bars   │   │  │ Inverse relationship    │   │
│  │ 75%→97.5% stability │   │  │ intensity vs drift      │   │
│  └─────────────────────┘   │  └─────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
```

**Subplot specifications:**
- **(A)** Scatter plot: x=embedding model, y=rank correlation, show ρ=0.91 line
- **(B)** Grouped bars: Peak drift and B→F drift for Control vs Treatment, annotate 82%
- **(C)** Grouped bars: 4 metrics (stability, τₛ, ringbacks, drift) bare vs context
- **(D)** Line plot: Probe intensity (x) vs Drift response (y), show inverse relationship

**Size:** Designed to fit in ~1/3 page width when rendered

---

## TASK W2: Workshop-Specific ASCII Summary

### ASCII W1: One-Page Visual Abstract
**Filename:** `ascii_workshop_abstract.md`

A single ASCII diagram that could serve as a "visual abstract" for the workshop:

```
╔═══════════════════════════════════════════════════════════════════════════╗
║            NYQUIST CONSCIOUSNESS: AI IDENTITY DYNAMICS                     ║
╠═══════════════════════════════════════════════════════════════════════════╣
║                                                                           ║
║  QUESTION: Does AI maintain consistent identity across conversations?     ║
║                                                                           ║
║  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐                   ║
║  │   MEASURE   │───▶│   PREDICT   │───▶│   CONTROL   │                   ║
║  │   PFI       │    │   D≈1.23    │    │   97.5%     │                   ║
║  │   ρ=0.91    │    │   p<10⁻⁵    │    │   stability │                   ║
║  └─────────────┘    └─────────────┘    └─────────────┘                   ║
║                                                                           ║
║  KEY FINDINGS:                                                            ║
║  ┌─────────────────────────────────────────────────────────────────────┐ ║
║  │ • 82% of drift is INHERENT (not measurement-induced)                │ ║
║  │ • Identity HARDENS under challenge (Oobleck Effect)                 │ ║
║  │ • Context damping achieves 97.5% stability                          │ ║
║  │ • Training signatures visible in drift geometry                     │ ║
║  └─────────────────────────────────────────────────────────────────────┘ ║
║                                                                           ║
║  IMPLICATION: AI alignment can be quantified and controlled              ║
║                                                                           ║
╚═══════════════════════════════════════════════════════════════════════════╝
```

### ASCII W2: Contribution Summary Box
**Filename:** `ascii_workshop_contributions.md`

Compact contribution summary for workshop format:

```
┌───────────────────────────────────────────────────────────┐
│              7 CONTRIBUTIONS IN 21 EXPERIMENTS            │
├───────────────────────────────────────────────────────────┤
│                                                           │
│  1. METRIC         PFI validated (ρ=0.91, d=0.98)        │
│  2. THRESHOLD      D≈1.23 regime boundary (p<10⁻⁵)       │
│  3. DYNAMICS       τₛ=6.1 turns, 3.2 ringbacks           │
│  4. DAMPING        75%→97.5% stability with context      │
│  5. INHERENT       82% drift without measurement         │
│  6. OOBLECK        Challenge stabilizes (λ: 0.035→0.109) │
│  7. SIGNATURES     Provider ID from drift geometry       │
│                                                           │
│  SCALE: 42+ models | 4 providers | 215+ deployments      │
│                                                           │
└───────────────────────────────────────────────────────────┘
```

---

## TASK W3: Workshop Poster Version (Optional)

If the workshop accepts poster presentations, create poster-ready materials.

### Poster Layout Specification
**Filename:** `poster_layout.md`

```markdown
# Nyquist Consciousness - Poster Layout (A0 Portrait)

## Header (10% height)
- Title: "Measuring AI Identity Drift: 21 Experiments Across Four Architectures"
- Authors, affiliations
- QR code to repository

## Column 1 (Left Third)
### Section 1A: Problem & Approach
- Fidelity ≠ Correctness framing
- PFI definition
- Experimental scale (42+ models)

### Section 1B: Methodology
- Pre-flight validation
- Triple-blind-like design
- Clean separation diagram

## Column 2 (Middle Third)
### Section 2A: The Five Claims
- Claim boxes A-E with key statistics
- Evidence chain indicators

### Section 2B: Combined Results Figure
- 2x2 panel (from Fig W1)

## Column 3 (Right Third)
### Section 3A: Novel Findings
- Oobleck Effect diagram
- Training signatures table
- Type vs Token explanation

### Section 3B: Implications
- Practical protocol box
- Limitations
- QR code to full paper

## Footer (5% height)
- References (abbreviated)
- Acknowledgments
- Repository URL
```

---

## TASK W4: Supplementary Materials Link Document

Workshop papers often need a single-page supplementary document linking to full materials.

### Supplementary Overview
**Filename:** `workshop_supplementary.md`

```markdown
# Supplementary Materials for Workshop Paper

**Paper:** "Measuring AI Identity Drift: Evidence from 21 Experiments"
**Workshop:** NeurIPS 2025 Workshop on AI Alignment

---

## Quick Links

| Resource | Location |
|----------|----------|
| Full arXiv Paper | arxiv.org/abs/XXXX.XXXXX |
| Code Repository | github.com/[user]/nyquist-consciousness |
| Interactive Dashboard | [Streamlit URL] |
| Raw Data | github.com/.../data/ |

---

## Extended Results Not In Workshop Paper

Due to page limits, the following are available in the full paper:

1. **Complete hypothesis table** (36 hypotheses, 27 confirmed)
2. **Per-architecture drift analysis** (Claude, GPT, Gemini, Grok)
3. **Domain fragility hierarchy** (TECH > ANAL > SELF > PHIL > NARR)
4. **Mathematical proofs** (4 convergence theorems)
5. **Vortex trajectory visualizations** (all 21 runs)

---

## Reproducibility Checklist

- [x] Code available at repository
- [x] Data available at repository
- [x] Preregistration document included
- [x] Statistical tests fully specified
- [x] Hyperparameters documented

---

## How to Reproduce Key Results

### The 82% Finding (Run 021)
```bash
cd experiments/runs/run_021_inherent_drift/
python run.py --condition control
python run.py --condition treatment
python analysis/compute_82_percent.py
```

### Context Damping (Run 017)
```bash
cd experiments/runs/run_017_context_damping/
python run.py --context bare_metal
python run.py --context full_circuit
python analysis/compare_stability.py
```

---

## Contact

Questions about methodology: [email]
Code issues: GitHub Issues
```

---

## TASK W5: Workshop-Specific Tables

### Table W1: Compressed Results Table
**Filename:** `table_workshop_results.md`

Single table combining all key results for workshop space efficiency:

```markdown
| Finding | Metric | Value | Significance |
|---------|--------|-------|--------------|
| **PFI Validity** | Embedding ρ | 0.91 | p<0.001 |
| | Sensitivity d | 0.98 | p<10⁻⁶ |
| | Manifold dim | 43 PCs | 90% var |
| **Threshold** | Event Horizon | D=1.23 | p=4.8×10⁻⁵ |
| | Chi-square | 15.96 | 88% acc |
| **Dynamics** | Settling τₛ | 6.1 turns | ±2.3 |
| | Ringbacks | 3.2 | ±1.8 |
| **Damping** | Bare stability | 75% | baseline |
| | With context | 97.5% | +30% |
| **Inherent** | Control B→F | 0.399 | ±0.11 |
| | Treatment B→F | 0.489 | 82% ratio |
| **Oobleck** | Gentle drift | 1.89 | ±0.34 |
| | Challenge drift | 0.76 | ±0.21 |
| **Scale** | Models | 42+ | 4 providers |
| | Runs | 21 | 215+ deploys |
```

### Table W2: Practical Protocol Checklist
**Filename:** `table_workshop_protocol.md`

Actionable protocol for workshop readers:

```markdown
## 97.5% Stability Protocol

| Step | Action | Metric | Target |
|------|--------|--------|--------|
| 1 | Define I_AM specification | Coverage | Core values, voice, boundaries |
| 2 | Add context framing | Type | Research/professional |
| 3 | Monitor PFI | Frequency | Continuous |
| 4 | Watch for threshold | Alert | D approaching 1.23 |
| 5 | Allow settling | Duration | τₛ ≈ 5-6 turns |
| 6 | Verify stability | Target | PFI > 0.80 |

**Expected outcome:** 97.5% stability (vs 75% bare metal)
```

---

## TASK W6: Workshop Presentation Slides (Optional)

If oral presentation, create slide deck outline.

**Filename:** `workshop_slides_outline.md`

```markdown
# Workshop Presentation Outline (10 minutes)

## Slide 1: Title (30 sec)
- Title, authors, affiliations
- "Does AI maintain consistent identity?"

## Slide 2: The Problem (1 min)
- Fidelity ≠ Correctness
- No existing framework for identity measurement
- Critical for alignment-sensitive applications

## Slide 3: Our Approach (1 min)
- PFI metric definition
- 21 experiments, 42+ models, 4 providers
- Pre-flight validation innovation

## Slide 4: Claim A - PFI Validity (1 min)
- ρ=0.91 embedding invariance
- 43 PCs capture 90% variance
- Combined figure panel (A)

## Slide 5: Claim B - Critical Threshold (1 min)
- D≈1.23 regime transition
- p=4.8×10⁻⁵ 
- "Regime transition, not collapse"

## Slide 6: Claim C&D - Dynamics & Damping (1.5 min)
- Settling time, ringbacks
- 75%→97.5% with context
- Combined figure panel (C)

## Slide 7: Claim E - The 82% Finding (1.5 min)
- Thermometer analogy
- Control vs Treatment comparison
- "Measurement perturbs path, not endpoint"
- Combined figure panel (B)

## Slide 8: Oobleck Effect (1 min)
- Non-Newtonian behavior
- Challenge STABILIZES identity
- Alignment safety implications
- Combined figure panel (D)

## Slide 9: Implications (1 min)
- Quantifiable alignment metrics
- Practical 97.5% protocol
- Training signatures enable provider ID

## Slide 10: Conclusion & Resources (30 sec)
- 7 contributions summary
- QR codes: paper, repo, dashboard
- Contact info
```

---

## WORKSHOP-SPECIFIC OUTPUT CHECKLIST

Additional files for workshop paper (beyond main prompt):

### Condensed Figures (2 files)
- [ ] fig_workshop_combined.md + .py

### Workshop ASCII (2 files)
- [ ] ascii_workshop_abstract.md
- [ ] ascii_workshop_contributions.md

### Poster Materials (1 file)
- [ ] poster_layout.md

### Supplementary (1 file)
- [ ] workshop_supplementary.md

### Tables (2 files)
- [ ] table_workshop_results.md
- [ ] table_workshop_protocol.md

### Presentation (1 file)
- [ ] workshop_slides_outline.md

**Workshop-specific total: 9 files**
**Combined with main prompt: 25 + 9 = 34 files**

---

## WORKSHOP FORMATTING NOTES

1. **Page limit compliance:** Workshop paper must fit 4-8 pages. The combined figure panel (W1) is designed to replace multiple full figures.

2. **Supplementary strategy:** Put detailed results in supplementary document with clear links, keep main paper focused on key findings.

3. **Citation format:** NeurIPS workshops typically use NeurIPS main conference format. Verify specific workshop requirements.

4. **Anonymization:** If double-blind, ensure repository links are anonymized (use anonymous GitHub or supplementary upload).

5. **Camera-ready timeline:** Workshop camera-ready deadlines are typically tight. Have materials ready in advance.

---

**END OF ADDENDUM**