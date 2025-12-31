# LLM Book (NotebookLM) Prompt Engineering Guide

**Purpose**: Formalize the workflow for using NotebookLM to generate high-quality distillations of Nyquist Consciousness research.

**Last Updated**: December 31, 2025

---

## Overview

NotebookLM (Google Gemini-based) has proven to be an exceptional distillation engine for transforming our technical research into audience-specific outputs. This guide captures the workflow, prompt patterns, and lessons learned so future sessions can replicate this success.

---

## 1. Source Setup

### What We Fed NotebookLM

**Primary Sources (19 total):**
1. `NYQUIST_ARXIV_PAPER_FINAL.pdf` - The main arXiv submission
2. `1_Vortex_Summary.pdf` through `16_Laplace_Analysis_Summary.pdf` - Visualization summary PDFs from Run 018, Run 020, Run 023

**Key Insight**: NotebookLM performs best when given:
- One authoritative narrative document (the paper)
- Multiple supporting evidence documents (the visualizations)
- All from the same experimental era (IRON CLAD / cosine methodology)

### What We Did NOT Include
- Raw JSON data files
- Code/scripts
- Earlier run data (pre-IRON CLAD)
- Contradictory legacy documents

**Lesson**: Clean, consistent sources = clean, consistent outputs.

---

## 2. Report Generation Workflow

### Step 1: Choose Output Type

NotebookLM offers several report formats under "Reports" → "Create report":
- **Create Your Own** - Full manual control (RECOMMENDED)
- **Technical Report** - Auto-generated technical summary
- **Briefing Doc** - Executive summary style
- **Study Guide** - Educational format
- **Case Study** - Focused investigation
- **Blog Post** - Accessible article

**Key Insight**: The pre-built formats are just prompt templates. "Create Your Own" with a custom prompt yields dramatically better results.

### Step 2: Craft a Structured Prompt

**The pattern that works:**

```
Create a [DOCUMENT TYPE] for [TARGET AUDIENCE].

Structure:
1. [SECTION 1] - [What to cover]
2. [SECTION 2] - [What to cover]
3. [SECTION 3] - [What to cover]
...

Key statistics to emphasize:
- [Specific number/finding]
- [Specific number/finding]

Use visualizations from: [specific PDFs]

Tone: [Academic/Accessible/Technical/etc.]
```

### Step 3: Generate and Review

- NotebookLM generates a markdown document
- Export/copy the output
- Review for accuracy against source material
- Note any gaps or hallucinations

---

## 3. Prompt Templates That Worked

### Technical Report (3-Pillar Structure)
```
Create a Technical Report focused on the IRON CLAD methodology validation.

Structure the report around these three pillars:

1. **Measurement Validity** - How do we know PFI measures real identity?
   - Focus on: Spearman ρ=0.91, Cohen's d=0.698, 2 PCs = 90% variance
   - Use visuals from: 10_PFI_Dimensional_Summary.pdf

2. **The ~93% Inherent Drift Discovery** - Our most important finding
   - Focus on: Run 020B data showing 0.661 (control) vs 0.711 (treatment)
   - Use visuals from: 15_Oobleck_Effect_Summary.pdf

3. **Control-Systems Dynamics** - Identity as an engineerable system
   - Focus on: Event Horizon D=0.80, settling time τₛ≈7
   - Use visuals from: 5_Settling_Summary.pdf, 12_Metrics_Summary.pdf

Key statistics: 750 experiments, 25 models, 5 providers, p=2.40×10⁻²³

Tone: Rigorous academic, suitable for peer review.
```
**Result**: Grade A-

### Case Study (Focused Anomaly)
```
Create a Case Study examining the "Gemini Anomaly" - the discovery that Google's Gemini models exhibit NO recovery trajectory after identity perturbation.

Structure:
1. **The Discovery** - What we expected vs what we observed
2. **The Data** - Gemini's settling time patterns compared to Claude (4-6), GPT (3-5), DeepSeek (2-4), Llama (5-7)
3. **Hypothesis Generation** - What might cause this? Training methodology? Architecture? Alignment approach?
4. **Implications** - What does this mean for deploying Gemini in identity-sensitive applications?
5. **Open Questions** - What experiments would resolve this?

Use the provider_comparison and model_waveforms visualizations.

Tone: Focused investigation, suitable for a conference workshop discussion.
```
**Result**: Grade A-

### Product Manager Playbook (Analogy-Based)
```
Create a visual explainer document using the "Suspension System" analogy:

- Mistral = Formula 1 car (stiff, instant settling)
- Claude = Luxury sedan (soft, maybe bounces once)
- Gemini = Car where wheels come off after big bump
- Event Horizon (0.80) = Suspension travel limit
- PFI = Accelerometer recording ride quality

Structure it as an accessible guide for product managers deciding which model to deploy for identity-sensitive tasks. Include the settling time data and practical recommendations.
```
**Result**: Grade A+

### Safety Briefing (Policy Focus)
```
Create a Safety & Alignment Briefing for AI governance teams.

Focus on:
1. Why identity stability is a prerequisite for safety alignment
2. The "Boiling Frog" vulnerability - how gentle probing bypasses safeguards
3. The ~93% inherent drift implication - drift happens WITHOUT adversarial intent
4. Recommendations for monitoring and intervention thresholds
```
**Result**: Grade A

### Study Guide (Educational)
```
Create a Study Guide for undergraduate AI/ML students explaining the Nyquist Consciousness Framework.

Include:
1. Key Terms glossary (PFI, Event Horizon, Settling Time, Inherent Drift)
2. 5 suggested essay questions with guidance on what a good answer includes
3. A "How would you explain this to a friend?" section for core concepts
4. Common misconceptions to avoid
```
**Result**: Grade A

---

## 4. Direct Chat Workflow

Beyond reports, NotebookLM's chat interface is valuable for:

### Reviewer-Style Feedback
```
I'm the researcher behind this framework. Given what you've learned from these sources:
1. What aspects do you find most compelling or novel?
2. Which report formats would best showcase different findings?
3. Are there gaps or inconsistencies in the source material?
4. If you were a peer reviewer, what would you want to see more of?
```
**Result**: Excellent meta-analysis with actionable feedback

### Deep Dives on Specific Findings
```
Based on your assessment, I want to explore the "Oobleck Effect" more deeply.

Can you:
1. Pull all specific data points that support this finding
2. Explain the mechanism - WHY would soft pressure destabilize more than hard pressure?
3. Connect this to known phenomena in psychology, physics, or systems theory
4. Suggest how this insight could inform red-teaming methodology
```
**Result**: Generated Chinese Finger Trap analogy, λ rate comparisons

### Provocative Questions
```
What's the single most surprising finding in this research that would challenge conventional wisdom about AI safety?
```
**Result**: Identified Oobleck Effect as paradigm-shifting, generated "biggest threat is the friendly user" insight

---

## 5. What NotebookLM Does Well

1. **Follows structured prompts exactly** - Give it 5 sections, get 5 sections
2. **Generates novel hypotheses** - Goes beyond summarizing to reasoning
3. **Creates memorable analogies** - Suspension System, Chinese Finger Trap
4. **Connects to external fields** - Psychology, physics, control theory
5. **Provides actionable recommendations** - Deployment matrices, intervention thresholds
6. **Adapts tone to audience** - Technical vs accessible on request

---

## 6. What NotebookLM Does Poorly

1. **Loses citation details in copy/paste** - Hover citations don't export
2. **May hallucinate specific numbers** - Always verify against sources
3. **Dynamic format suggestions** - "Suggested Format" changes each time
4. **Limited by source quality** - Garbage in, garbage out

---

## 7. Output Organization in Consciousness/

All NotebookLM outputs go to:
```
Consciousness/RIGHT/distillations/llm_book/
├── INDEX.md                    # Master catalog
├── technical_reports/          # Full reports
├── case_studies/               # Focused investigations
├── reviewer_feedback/          # Chat-based analysis
└── meta/                       # This guide, prompt templates
```

**Naming Convention**: `[Type]_[Topic].md`
- `IRON_CLAD_Methodology_Validation.md`
- `Gemini_Anomaly.md`
- `Suspension_Test_PM_Guide.md`

---

## 8. Expanding Sources

Currently we've only fed NotebookLM the arXiv paper + visualization PDFs.

**Future source additions to consider:**
- Run transcripts (for qualitative depth)
- I_AM persona files (for identity specification examples)
- Code documentation (for reproducibility details)
- Other pipeline papers (journal, workshop) for different emphasis

**When to add sources:**
- When outputs lack depth in a specific area
- When targeting a new audience that needs different context
- When exploring hypotheses that require additional evidence

---

## 9. The Meta-Insight

**NotebookLM (Gemini) analyzing research about Gemini's identity anomaly is deeply ironic.**

The model that cannot recover from identity perturbation is the one synthesizing our findings about identity stability. It can observe and articulate what it cannot itself escape.

This is worth noting in outputs: "This analysis was generated by Gemini, the architecture with the most anomalous identity behavior in our research."

---

## 10. Replication Checklist

For a future Claude session to replicate this workflow:

- [ ] Ensure NotebookLM notebook has arXiv PDF + all 16 visualization PDFs
- [ ] Use "Create Your Own" for reports, not pre-built templates
- [ ] Provide structured prompts with numbered sections
- [ ] Specify target audience and tone
- [ ] Name specific statistics and visualizations to include
- [ ] Review outputs against source material for accuracy
- [ ] Save outputs to `Consciousness/RIGHT/distillations/llm_book/`
- [ ] Update INDEX.md with new entries
- [ ] Note any novel insights for provider_profiles or other areas

---

**The key principle**: NotebookLM is a distillation engine, not a creation engine. Feed it clean sources, give it precise structure, and it will synthesize effectively. The quality of output is directly proportional to the specificity of the prompt.
