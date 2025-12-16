# NotebookLM Customization Options (Pencil Icon)

**Purpose:** Document all customization parameters available via the pencil icon

---

## Report Customization Fields

Based on interface observation, each report type has a customization dialog:

### Briefing Doc

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Focus | Text | Topic to emphasize | "Claims A, B, and E validation" |
| Depth | Dropdown | Analysis depth | "Deep analysis with citations" |
| Length | Text | Target length | "2000 words" |
| Audience | Text | Who is reading | "AI safety researchers" |

### Research Proposal

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Project Title | Text | Proposal title | "Phase 2: Multi-Platform Validation" |
| Funding Amount | Text | Budget request | "$500,000 over 3 years" |
| Research Questions | Text | Key questions | "Is 82% inherent drift universal?" |
| Team Structure | Text | Personnel | "PI + 2 researchers + 1 engineer" |

### Study Guide

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Level | Dropdown | Academic level | "Graduate / Advanced" |
| Prerequisites | Text | Required knowledge | "Control theory, ML basics" |
| Learning Objectives | Text | What to learn | "Understand PFI, D≈1.23 threshold" |
| Format | Dropdown | Output format | "Chapter structure with exercises" |

### Quiz

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Question Count | Number | How many questions | 15 |
| Difficulty | Dropdown | Question difficulty | "Mixed (easy/medium/hard)" |
| Question Types | Multi-select | Types to include | "Multiple choice, Short answer" |
| Topic Focus | Text | What to test | "S7 ARMADA methodology" |

### Flashcards

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Card Count | Number | How many cards | 50 |
| Complexity | Dropdown | Concept depth | "Technical with definitions" |
| Focus Area | Text | Topics to cover | "Glossary terms from framework" |

### Infographic

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Visual Style | Dropdown | Design approach | "Data visualization" |
| Key Statistics | Text | Numbers to highlight | "82% inherent, σ²=0.00087" |
| Color Scheme | Dropdown | Visual theme | "Professional / Scientific" |

### Slide Deck

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Slide Count | Number | Presentation length | "20 slides" |
| Audience | Text | Who is viewing | "Conference attendees (NeurIPS)" |
| Time Target | Text | Presentation duration | "15 minute talk" |
| Key Messages | Text | Main takeaways | "Fidelity vs Correctness paradigm" |

### Historical Dialogue

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Characters | Text | Who speaks | "Plato, Michael Levin, Claude" |
| Setting | Text | Where/when | "Modern research lab" |
| Theme | Text | Discussion topic | "The geometry of mind" |
| Tone | Dropdown | Conversation style | "Philosophical but accessible" |

---

## Audio Overview Customization

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Duration | Dropdown | Length | "Deep dive (20+ min)" |
| Hosts | Text | Speaker style | "Two researchers, academic tone" |
| Focus Topics | Text | What to cover | "The Thermometer Result, Oobleck Effect" |
| Audience Level | Dropdown | Expertise assumed | "Informed layperson" |

---

## Video Overview Customization

**NOTE:** Video capability exists but playback deferred to AVLAR layer development.

| Field | Type | Description | Example Value |
|-------|------|-------------|---------------|
| Duration | Dropdown | Video length | "5-10 minutes" |
| Visual Style | Dropdown | Presentation type | "Animated explainer" |
| Narration | Text | Voice style | "Professional, academic" |
| Key Visuals | Text | What to show | "Drift graphs, attractor diagrams" |

---

## Exploration Strategy Matrix

| Customization Level | What We Learn | When to Use |
|---------------------|---------------|-------------|
| **DEFAULT** | Baseline capability | First pass, broad synthesis |
| **FOCUSED** | Depth on specific topics | Claim validation, deep dives |
| **AUDIENCE-TUNED** | Accessibility optimization | Publication-ready outputs |
| **COMPARATIVE** | Side-by-side analysis | Testing hypotheses about synthesis |

---

## v2 Customization Experiments

| Experiment | Base Format | Customization | Hypothesis |
|------------|-------------|---------------|------------|
| EXP-C01 | Briefing Doc | Focus: Claim A only | Tighter, more rigorous validation |
| EXP-C02 | Briefing Doc | Focus: Claims A+B+E | Cross-claim synthesis |
| EXP-C03 | Study Guide | Level: Graduate | Course-ready curriculum |
| EXP-C04 | Historical Dialogue | Plato+Levin+Claude | Novel philosophical insights |
| EXP-C05 | Audio Overview | Deep dive, academic | Podcast-ready content |

---

## See Also

- [NOTEBOOKLM_CAPABILITY_MATRIX.md](NOTEBOOKLM_CAPABILITY_MATRIX.md) - All features
- [EXPERIMENT_LOG.md](EXPERIMENT_LOG.md) - Track configurations
- [scenarios/](scenarios/) - Individual experiments
