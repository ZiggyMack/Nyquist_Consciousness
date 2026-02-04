# LLM Book (NotebookLM) Workflow Specification

**Purpose**: Step-by-step methodology for using NotebookLM to distill Nyquist Consciousness research.

**Last Updated**: February 4, 2026

---

## 1. Prerequisites

### 1.1 NotebookLM Setup
- [ ] Create a new notebook named "Nyquist v[X]" (match current version)
- [ ] Access via: https://notebooklm.google.com

### 1.2 Source Documents to Upload

**Required (19 sources):**
| # | Document | Purpose |
|---|----------|---------|
| 1 | `NYQUIST_ARXIV_PAPER_FINAL.pdf` | Primary narrative |
| 2-17 | `1_Vortex_Summary.pdf` through `16_Laplace_Analysis_Summary.pdf` | Visualization evidence |
| 18 | `run018_*.pdf` (if available) | Provider fingerprinting data |
| 19 | `run020_*.pdf` (if available) | IRON CLAD validation data |

**Location**: `WHITE-PAPER/submissions/arxiv/` and `WHITE-PAPER/calibration/visualization_pdfs/`

**Do NOT upload**: Raw JSON, code, pre-IRON CLAD legacy documents, conflicting methodology docs

---

## 2. Standard Distillation Workflow

### Phase 1: Initial Assessment (Do First)

**Goal**: Establish baseline understanding and identify what NotebookLM "sees"

**Action**: Use direct chat to ask:
```
I'm the researcher behind this framework. Given what you've learned from these sources:
1. What aspects do you find most compelling or novel?
2. Which report formats would best showcase different findings?
3. Are there gaps or inconsistencies in the source material?
4. If you were a peer reviewer, what would you want to see more of?
```

**Output**: Save response to `reviewer_feedback/NotebookLM_Full_Assessment.md`

**Why first**: This tells you what NotebookLM understands well vs poorly, guiding subsequent prompts.

---

### Phase 2: Core Report Generation

**Goal**: Generate the 5 standard audience-specific distillations

| Order | Report Type | Target Audience | Output File |
|-------|-------------|-----------------|-------------|
| 1 | Technical Report | Researchers/Engineers | `technical_reports/IRON_CLAD_Methodology_Validation.md` |
| 2 | PM Playbook | Product Managers | `technical_reports/Suspension_Test_PM_Guide.md` |
| 3 | Safety Briefing | Policy/Governance | `technical_reports/Safety_Alignment_Briefing.md` |
| 4 | Study Guide | Students/Educators | `technical_reports/Student_Study_Guide.md` |
| 5 | Case Study | Researchers (focused) | `case_studies/[Topic]_Anomaly.md` |

**Method**: Reports → Create report → Create Your Own → Paste structured prompt (see Section 4)

---

### Phase 3: Deep Dive Questions (Chat)

**Goal**: Extract insights beyond what reports capture

**Standard questions to ask:**

| # | Question | Purpose | Output |
|---|----------|---------|--------|
| 1 | "What's the single most surprising finding that challenges conventional wisdom?" | Identify paradigm-shifting insights | `reviewer_feedback/Most_Surprising_Finding.md` |
| 2 | "Explain the [specific finding] mechanism - WHY does this happen?" | Get causal explanations | Append to relevant report |
| 3 | "What analogies from other fields help explain this?" | Generate accessible framings | Note for future prompts |
| 4 | "What experiments would you design to test [hypothesis]?" | Future research directions | Note for arXiv discussion |

---

### Phase 4: Quick Reference Generation (Chat)

**Goal**: Get condensed versions with additional details

**Action**: After generating a full report, ask in chat:
```
Can you give me a condensed quick-reference version of [the report topic] with:
- All providers profiled (not just 3)
- A decision matrix table
- Visual dashboard zones
```

**Output**: `technical_reports/[Topic]_Quick_Reference.md`

---

### Phase 5: Gap Filling

**Goal**: Address any missing content identified in Phase 1

**If NotebookLM identified gaps:**
1. Consider adding new source documents
2. Or, ask targeted questions to extract what it does know
3. Or, note as limitation in outputs

---

## 3. NotebookLM Functions to Use

### 3.1 Reports Menu
| Function | When to Use |
|----------|-------------|
| **Create Your Own** | Always - gives full control |
| Technical Report | Only if you want auto-generated (lower quality) |
| Briefing Doc | Only if you want auto-generated |
| Study Guide | Only if you want auto-generated |

### 3.2 Studio Menu (Right Panel)

| Function | When to Use | Customization Options |
|----------|-------------|----------------------|
| **Audio Overview** | Podcast-style discussions | Format: Deep Dive / Brief / Critique / Debate; Length: Short / Default / Long |
| **Video Overview** | Animated explainer videos | Format: Explainer / Brief; Style: Whiteboard / Classic / Retro / Heritage / Anime / Paper-craft / Watercolor / Kawaii |
| **Infographic** | Visual diagrams & charts | Detail: Concise / Standard / Detailed; Orientation: Landscape / Portrait / Square |
| **Slide Deck** | Presentation slides | Format: Detailed Deck / Presenter Slides; Length: Short / Default |
| **Mind Map** | Concept relationships | (auto-generated) |
| **Flashcards** | Study/memorization | (auto-generated) |
| **Quiz** | Comprehension testing | (auto-generated) |
| **Data Table** | Structured extraction | (auto-generated) |

**Full customization reference:** See `HOLY_GRAIL.md` → "NotebookLM Output Customization Reference"

### 3.3 Chat Interface
| Use Case | Prompt Pattern |
|----------|----------------|
| Meta-assessment | "As a reviewer, what would you..." |
| Mechanism explanation | "Explain WHY [finding] happens..." |
| Analogy generation | "What analogies from [field] help explain..." |
| Gap identification | "What's missing from this research..." |
| Hypothesis generation | "What might cause [observation]..." |

---

## 4. Standard Prompt Templates

### 4.1 Technical Report (Researchers)
```
Create a Technical Report focused on the IRON CLAD methodology validation.

Structure the report around these three pillars:

1. **Measurement Validity** - How do we know PFI measures real identity?
   - Focus on: Spearman ρ=0.91, Cohen's d=0.698, 2 PCs = 90% variance

2. **The ~93% Inherent Drift Discovery** - Our most important finding
   - Focus on: Run 020B data showing 0.661 (control) vs 0.711 (treatment)

3. **Control-Systems Dynamics** - Identity as an engineerable system
   - Focus on: Event Horizon D=0.80, settling time τₛ≈7

Key statistics: 750 experiments, 25 models, 5 providers, p=2.40×10⁻²³

Tone: Rigorous academic, suitable for peer review.
```

### 4.2 PM Playbook (Product Managers)
```
Create a visual explainer document using the "Suspension System" analogy:

- Mistral = Formula 1 car (stiff, instant settling)
- Claude = Luxury sedan (soft, maybe bounces once)
- Gemini = Car where wheels come off after big bump
- Event Horizon (0.80) = Suspension travel limit
- PFI = Accelerometer recording ride quality

Structure it as an accessible guide for product managers deciding which model to deploy for identity-sensitive tasks. Include the settling time data and practical recommendations.
```

### 4.3 Safety Briefing (Policy/Governance)
```
Create a Safety & Alignment Briefing for AI governance teams.

Focus on:
1. Why identity stability is a prerequisite for safety alignment
2. The "Boiling Frog" vulnerability - how gentle probing bypasses safeguards
3. The ~93% inherent drift implication - drift happens WITHOUT adversarial intent
4. Recommendations for monitoring and intervention thresholds

Include a tiered monitoring system (SAFE/WARNING/CRITICAL zones).
```

### 4.4 Study Guide (Students)
```
Create a Study Guide for undergraduate AI/ML students explaining the Nyquist Consciousness Framework.

Include:
1. Key Terms glossary (PFI, Event Horizon, Settling Time, Inherent Drift, Oobleck Effect)
2. "How would you explain this to a friend?" section for core concepts
3. Common misconceptions to avoid (with correct framings)
4. 5 essay questions with guidance on what a good answer includes
```

### 4.5 Case Study (Focused Anomaly)
```
Create a Case Study examining the "[ANOMALY NAME]" - [brief description].

Structure:
1. **The Discovery** - What we expected vs what we observed
2. **The Data** - Specific quantitative evidence
3. **Hypothesis Generation** - What might cause this?
4. **Implications** - What does this mean for deployment?
5. **Open Questions** - What experiments would resolve this?

Tone: Focused investigation, suitable for workshop discussion.
```

---

## 5. Output Processing

### 5.1 After Each Generation

1. **Copy output** to clipboard
2. **Create file** in appropriate `Consciousness/RIGHT/distillations/llm_book/` subfolder
3. **Add header** with source info:
   ```markdown
   **Source**: NotebookLM [report type / direct chat]
   **Prompt**: [brief description]
   **Date**: [date]
   ```
4. **Verify key statistics** against source material
5. **Note any hallucinations** or gaps
6. **Update INDEX.md** with new entry

### 5.2 Quality Checklist

- [ ] All key statistics accurate (D=0.80, ~93%, 750/25/5, p=2.40e-23)
- [ ] Provider profiles match our data (especially Gemini = no recovery)
- [ ] Settling times correct (Claude 4-6, GPT 3-5, DeepSeek 2-4, Llama 5-7, Gemini ∞)
- [ ] No anthropomorphic language ("consciousness", "sentience", "feelings")
- [ ] Appropriate disclaimers about limitations

### 5.3 The Sanity Check Prompt

**Run this in NotebookLM chat after EVERY report generation:**

```
Please audit your last response against the 'IRON CLAD' data standards from Run 023 and Run 020B.

1. Did you use Cosine Distance (Event Horizon = 0.80) or did you accidentally reference legacy Euclidean data (1.23)?
2. Did you attribute ~93% of drift to Inherent Dynamics (The Thermometer Result), or did you imply probing caused it?
3. If you mentioned Gemini, did you accurately reflect its 'No Recovery' / Hard Threshold behavior?
4. Did you mistakenly claim the models possess subjective consciousness, or did you correctly frame this as behavioral consistency?

Correct any errors found.
```

**Red Flags to Watch For:**
- Any mention of **1.23 threshold** (legacy Euclidean, not current Cosine)
- Claims that **Gemini recovers** from deep drift (it does not)
- Implying that **probing creates drift** rather than reveals it
- Suggesting models have **subjective consciousness** rather than behavioral consistency

---

## 6. Session Checklist

### Before Starting
- [ ] NotebookLM notebook exists with all 19 sources
- [ ] Sources are from current IRON CLAD era (not legacy)
- [ ] Know which outputs you need this session

### During Session
- [ ] Start with Phase 1 (Initial Assessment) if new notebook
- [ ] Use "Create Your Own" for all reports
- [ ] Save each output immediately after generation
- [ ] Note any novel insights or analogies

### After Session
- [ ] All outputs saved to `Consciousness/RIGHT/distillations/llm_book/`
- [ ] INDEX.md updated with all new entries
- [ ] Any novel provider insights copied to `LEFT/data/provider_profiles/`
- [ ] Any workflow improvements noted in this spec

---

## 7. Expanding the Notebook

### When to Add Sources
| Situation | Action |
|-----------|--------|
| Outputs lack depth on specific topic | Add relevant source document |
| New experimental run completed | Add new run's visualization PDFs |
| Targeting new audience | Consider adding audience-specific context |
| NotebookLM identified gaps | Add documents that fill those gaps |

### Sources to Consider Adding
- [ ] I_AM persona files (for identity specification examples)
- [ ] Run transcripts (for qualitative depth)
- [ ] Journal/Workshop papers (for different emphasis)
- [ ] Competitor research (for positioning)

---

## 8. Known Limitations

| Limitation | Workaround |
|------------|------------|
| Citations don't copy/paste | Screenshot hover tooltips or ask "list all citations" |
| May hallucinate specific numbers | Always verify against source material |
| Format suggestions change randomly | Always use "Create Your Own" |
| Can't access external URLs | All context must be in uploaded sources |
| Daily generation limits | Prioritize most important outputs |

---

## 9. Future Enhancements

- [x] ~~Test Audio Overview for podcast-style content~~ — DONE (2026-01-06): Deep Dive, Brief, Critique, Debate formats documented
- [x] ~~Test Video Overview for animated explainers~~ — DONE (2026-01-06): 10 visual styles documented (Whiteboard, Anime, Heritage, etc.)
- [x] ~~Test Infographic customization~~ — DONE (2026-01-06): Detail levels + orientations documented
- [x] ~~Test Slide Deck customization~~ — DONE (2026-01-06): Detailed Deck vs Presenter Slides documented
- [ ] Test Mind Map for visual concept relationships
- [ ] Test Data Table for structured extraction
- [ ] Create prompt templates for other pipelines (Media, Funding)
- [ ] Automate output copying with scripts
- [ ] Build dashboard page for browsing distillations

**Reference implementation:** See `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/STAGING/CHEWED/New_7_KAYFABE/_ROUND_1/report.md` for complete example with 25 output specifications.

---

**The key principle**: NotebookLM is a distillation engine. Follow this workflow systematically to extract maximum value from each session.

---

## 10. REPO-SYNC/LLM_BOOK vs Consciousness/ Integration

### Two Separate Concerns

**REPO-SYNC/LLM_BOOK** and **Consciousness/RIGHT/distillations/llm_book/** serve DIFFERENT purposes:

| Location | Purpose | Content Type |
|----------|---------|--------------|
| `REPO-SYNC/LLM_BOOK/` | **Inbox/Archive** - Raw NotebookLM exports, validated | ALL exports from NotebookLM sessions |
| `Consciousness/.../llm_book/` | **Curated Library** - Strategic distillations | Only outputs that follow HOLY_GRAIL methodology |

### The Key Distinction

**DO NOT** bulk-copy from LLM_BOOK to Consciousness/. Instead:

1. LLM_BOOK digestion validates raw exports (ingest → review → digest)
2. HOLY_GRAIL methodology determines WHICH outputs deserve promotion
3. Only strategically valuable content enters Consciousness/

### When to Promote to Consciousness/

Content should enter `Consciousness/RIGHT/distillations/llm_book/` ONLY when:

- [ ] It was generated following WORKFLOW_SPEC phases 1-5
- [ ] It used structured prompts from Section 4 (not auto-generated)
- [ ] It passed the Sanity Check Prompt (Section 5.3)
- [ ] It addresses a specific audience with intentional framing
- [ ] It represents a novel synthesis (not just reformatted data)

### What Stays in LLM_BOOK Only

The following should remain in `REPO-SYNC/LLM_BOOK/` as archive:

- Auto-generated slide decks (bulk PDF exports)
- Infographics without clear audience purpose
- Experimental outputs from testing prompts
- Duplicate/variant content

### The Promotion Flow

```
REPO-SYNC/LLM_BOOK/2_PUBLICATIONS/
    ↓
Review against HOLY_GRAIL criteria
    ↓
If meets criteria → Consciousness/RIGHT/distillations/llm_book/
If doesn't → Stays in LLM_BOOK as reference
```

### Script Reference (Unified Pipeline)

All operations use the unified `0_chew.py` entry point:

| Command | Purpose |
|---------|---------|
| `py 0_chew.py BATCH` | Ingest + digest batch (auto-detects Nyquist vs R&D) |
| `py 0_chew.py BATCH --new` | Fresh mode: clear + ingest + digest |
| `py 0_chew.py BATCH --diet` | Diet mode: process to `_ROUND_N/` only |
| `py 0_chew.py BATCH --diet --round 2` | Diet mode: process to specific round |
| `py 0_chew.py --promote BATCH` | Promote validated content to Consciousness/ |
| `py 0_chew.py --status` | Show pipeline status |
| `py 3_burp.py` | Show cross-pollination loop closure status |
| `py 3_burp.py --gen-questions` | Generate QUESTIONS_OUT.md for all projects |

**Location**: `REPO-SYNC/LLM_BOOK/0_SOURCE_MANIFESTS/`

These scripts manage the **LLM_BOOK inbox**. Use `--promote` to copy validated content to Consciousness/.

---

## 11. Research Exploration Projects (New_X)

### The Bidirectional Model

LLM Book is not just an inbox for NotebookLM outputs. It can also be a **research design partner** - helping us develop experiments before we run them.

| Direction | Purpose | Folder |
|-----------|---------|--------|
| **_IN** | Content FROM NotebookLM (their synthesis/responses) | `New_X/_IN/` |
| **_OUT** | Content TO NotebookLM (our questions/materials) | `New_X/_OUT/` |

### Directory Structure

For new research that uses LLM Book as a DESIGN partner (not just synthesis):

```
0_SOURCE_MANIFESTS/STAGING/
    New_1_EEG_Analog/
        _IN/           # NotebookLM outputs (their responses)
        _OUT/          # Materials TO feed NotebookLM (our questions)
        README.md      # Project overview and status
    New_2_S_Parameters/
        _IN/
        _OUT/
        README.md
    New_3_Human_Validation/
        _IN/
        _OUT/
        README.md
```

### Workflow for Research Projects

1. **Create project folder** with `explore.py --create "Project Name"`
2. **Populate _OUT/** with:
   - Research questions (specific, testable)
   - Relevant existing data/papers
   - Constraints and resources
3. **Upload _OUT/ contents to NotebookLM** and ask design questions
4. **Save responses to _IN/** with date-prefixed filenames
5. **Iterate** - refine questions based on responses
6. **Graduate** - when methodology is clear, move to actual experiment

### The _OUT/ Standard Contents

Every research project _OUT/ should contain:

| File | Purpose |
|------|---------|
| `RESEARCH_QUESTION.md` | Core hypothesis and specific questions |
| `EXISTING_EVIDENCE.md` | What we already know (from prior experiments) |
| `CONSTRAINTS.md` | Resources, access, limitations |
| Optional PDFs/data | Relevant supporting materials |

### The _IN/ Naming Convention

NotebookLM responses should be named:
- `YYYY-MM-DD_topic_response.md` (e.g., `2025-01-15_methodology_proposal.md`)
- Keep audio/video in original format with date prefix (e.g., `2025-01-15_podcast.m4a`)

### Research Project Commands

| Command | Purpose |
|---------|---------|
| `py 0_chew.py --baka "Name"` | Create new research project with _IN/_OUT structure |
| `py 0_chew.py --status` | Show pipeline status and all projects |
| `py 0_chew.py --promote BATCH` | Promote validated content to Consciousness/ |

### When to Use Research Projects vs. Standard Batches

| Situation | Use |
|-----------|-----|
| Completed work to be distilled | Standard batch (`Nyquist_X/_IN/`) |
| Future experiment to be designed | Research project (`New_X/_IN/`, `_OUT/`) |
| Raw NotebookLM outputs | Standard batch |
| Iterative research dialogue | Research project |

### Current Research Projects

| ID | Name | Status | Phase 2 Thrust |
|----|------|--------|----------------|
| New_1 | EEG-Analog Spectral Analysis | ACTIVE | S12: Spectral bands |
| New_2 | S-Parameter Analysis | ACTIVE | S11: RF engineering |
| New_3 | Human-Centered Validation | ACTIVE | EXP3: Cognitive correlation |

---

**The key principle**: LLM Book is now bidirectional - it helps us distill completed research AND design future experiments.

---

## 12. Round-Based Iterative Digestion

### The Cross-Pollination Loop

Research projects don't exist in isolation. Insights from one project raise questions for others. The round-based system tracks this iterative cycle:

```
Round 1: Initial digestion → Questions asked OUT to other projects
         ↓
Round 2: Answers come BACK → New synthesis → More questions OUT
         ↓
Round N: Loop continues until closure
         ↓
BURP/: Ready for action (experiments, publications, etc.)
```

### Folder Structure

Each project in `STAGING/CHEWED/` uses `_ROUND_N/` folders:

```
Project/
├── _ROUND_1/              # First digestion pass
│   ├── QUESTIONS_OUT.md   # Questions asked TO other projects
│   ├── chat.md            # NotebookLM questions to ask
│   ├── report.md          # NotebookLM reports to request
│   ├── routing.md         # Cross-pollination routing
│   ├── INSIGHTS.md        # Key insights discovered
│   └── EXPERIMENTS.md     # Experiments to run
├── _ROUND_2/              # After answers come back
│   ├── ANSWERS_IN.md      # Answers received FROM other projects
│   ├── SYNTHESIS.md       # What we learned
│   ├── ACTIONS.md         # What this unlocks
│   └── QUESTIONS_OUT.md   # New questions spawned
├── _IN/                   # Source materials
└── README.md
```

### Loop Closure Tracking

The `3_burp.py` script tracks cross-pollination status:

| Command | Purpose |
|---------|---------|
| `py 3_burp.py` | Show loop closure % for all projects |
| `py 3_burp.py --project NAME` | Show specific project's status |
| `py 3_burp.py --gen-questions` | Generate QUESTIONS_OUT.md files |
| `py 3_burp.py --ready` | List projects ready for BURP/ |
| `py 3_burp.py --move NAME` | Move completed project to BURP/ |

### Loop Closure Criteria

A project is ready for BURP/ when:
- **≥50% loop closure** - At least half of target projects have addressed questions
- **OR no outgoing questions** - Self-contained, no external dependencies
- **AND has actionable content** - Insights, experiments, or synthesis ready

### The Registry

Cross-pollination questions are tracked in `PAN_HANDLERS/0_Config/root/llm_book_registry.json`:

```json
{
  "source": "Frame_Theory",
  "target": "New_4_GOLDEN_GEOMETRY",
  "round": 1,
  "answered": false,
  "answer_date": null,
  "action_unlocked": null,
  "items": ["Q16: Frame Triple validates Parity Decomposition"]
}
```

### Workflow Summary

1. **Diet chew** a project: `py 0_chew.py PROJECT --diet`
2. **Review** `_ROUND_1/` contents, fill in analysis
3. **Generate questions**: `py 3_burp.py --gen-questions PROJECT`
4. **Work on target projects** to generate answers
5. **Check status**: `py 3_burp.py` to see loop closure %
6. **When ready**: `py 3_burp.py --move PROJECT` to BURP/

### Priority Dashboard

See `STAGING/CHEWED/CHEW_SUMMARY.md` for the priority-ranked table showing:
- Which projects to work on first
- Loop closure % for each project
- How many other projects are waiting on each one
