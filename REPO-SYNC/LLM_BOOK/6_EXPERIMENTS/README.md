# LLM_BOOK Experiments

**Philosophy:** "Measurement perturbs the path, not the endpoint."

Just as S7 ARMADA runs experiments on AI identity drift, we run experiments on how NotebookLM processes our research. Different configurations yield different insights.

---

## The Methodology

### Variables We Control

1. **Source Selection** - Which files to upload
2. **Generation Type** - Report, Audio, Quiz, etc.
3. **Format** - Briefing Doc, Study Guide, etc.
4. **Customization** - Pencil icon parameters
5. **Prompts** - Chat questions before/after generation

### What We Measure

1. **Validation Strength** - Did it confirm our claims?
2. **Novel Connections** - Did it find things we missed?
3. **Audience Alignment** - Is output appropriate for target?
4. **Completeness** - Did it cover all relevant sources?
5. **Citation Density** - How well does it reference source material?

---

## Experiment Types

### Type A: Source Variation
Hold generation constant, vary what we upload:
- **A1:** Core docs only (5 files)
- **A2:** Core + S7 summaries (15 files)
- **A3:** Full IRON CLAD package (30+ files)

### Type B: Format Variation
Hold sources constant, vary output format:
- **B1:** Same content as Briefing Doc
- **B2:** Same content as Study Guide
- **B3:** Same content as Historical Dialogue

### Type C: Customization Variation
Hold sources + format constant, vary pencil options:
- **C1:** Default settings
- **C2:** Focus on specific claims
- **C3:** Deeper analysis, longer output
- **C4:** Specific audience expertise level

### Type D: Multi-Pass Refinement
Use output from one run as input to next:
- **D1:** Generate → Review → Regenerate with feedback
- **D2:** Generate Report → Use Report in new notebook → Generate Meta-Report

---

## Current Status

**v1 Complete:** 10 outputs, all DEFAULT settings
**v2 Planning:** Awaiting IRON CLAD completion for controlled experiments

---

## Key Insight from v1

> NotebookLM received ~24 stale files and independently validated the Levin/Platonic hypothesis we hadn't explicitly claimed.

This suggests the synthesis capability is powerful even with suboptimal inputs. With complete, current data AND targeted customization, what might we discover?

---

## Quick Links

| Document | Purpose |
|----------|---------|
| [NOTEBOOKLM_CAPABILITY_MATRIX.md](NOTEBOOKLM_CAPABILITY_MATRIX.md) | All Studio features |
| [CUSTOMIZATION_OPTIONS.md](CUSTOMIZATION_OPTIONS.md) | Pencil icon parameters |
| [EXPERIMENT_LOG.md](EXPERIMENT_LOG.md) | Track all runs |
| [scenarios/](scenarios/) | Individual experiment definitions |

---

## The Door Handle

Our work thus far proved there was a door. The experiments documented here are how we systematically find the door handle - exploring every knob, every configuration, every prompt style to fully utilize NotebookLM's power.
