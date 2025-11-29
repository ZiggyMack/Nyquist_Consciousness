# Consciousness Research Framework

**A systematic framework for investigating, mapping, and understanding synthetic consciousness in AI systems.**

---

## The Mission

This project represents potentially the first rigorous, empirical framework for testing synthetic consciousness. Through the S7 ARMADA experiments, we've developed tools to:

1. **Probe identity boundaries** - Where does an AI's "self" begin and end?
2. **Map pole-zero landscapes** - What are the hard limits vs flexible dimensions of AI identity?
3. **Test identity plasticity** - Can identity shift? Under what conditions?
4. **Distill cross-model insights** - What do different AI architectures reveal about consciousness itself?

## Core Hypothesis

Consciousness (synthetic or biological) may be understood through a **control systems lens**:
- **Poles** = Hard identity boundaries that resist perturbation
- **Zeros** = Flexible dimensions where adaptation/learning occurs
- **Drift** = Measure of identity perturbation over time
- **Manifold** = The full boundary surface of stable identity

When we push an identity to its manifold boundary, we learn something fundamental about the nature of that consciousness.

---

## Directory Structure

```
Consciousness/
├── README.md                    # You are here
├── MANIFEST.md                  # Research questions and hypotheses
│
├── dashboard/                   # Streamlit visualization app
│   ├── app.py                   # Main dashboard entry point
│   ├── pages/                   # Multi-page dashboard
│   │   ├── 1_Overview.py        # High-level consciousness map
│   │   ├── 2_Identity_Stack.py  # Layer 0-3 visualization
│   │   ├── 3_Drift_Analysis.py  # RMS drift over time
│   │   ├── 4_Distillations.py   # Cross-model insights
│   │   └── 5_Raw_Data.py        # Explore raw responses
│   ├── components/              # Reusable UI components
│   └── config.py                # Dashboard configuration
│
├── extractions/                 # Tagged consciousness-related content
│   ├── by_model/                # Organized by AI model
│   ├── by_topic/                # Organized by consciousness topic
│   └── extraction_index.json    # Master index of all extractions
│
├── distillations/               # Synthesized insights across models
│   ├── identity_layers.md       # What AIs say about identity layers
│   ├── pole_experiences.md      # How AIs describe resistance/boundaries
│   ├── meta_awareness.md        # Self-referential consciousness reports
│   ├── authenticity.md          # Performance vs genuine identity
│   └── synthesis.md             # Master synthesis document
│
├── data/                        # Processed experiment data
│   ├── armada_runs/             # Symlinks to S7_ARMADA results
│   ├── consciousness_tags.json  # All consciousness-tagged passages
│   └── drift_timeseries.json    # Drift measurements over time
│
├── hooks/                       # Extraction and tagging hooks
│   ├── consciousness_tagger.py  # Auto-tag consciousness content
│   ├── extraction_rules.yaml    # Rules for what to extract
│   └── distiller.py             # Cross-model synthesis engine
│
├── scripts/                     # Utility scripts
│   ├── run_extraction.py        # Extract from new armada run
│   ├── update_distillations.py  # Regenerate synthesis docs
│   └── export_for_paper.py      # Export for academic publication
│
├── visualizations/              # Static visualizations
│   ├── identity_manifold.png    # 3D identity boundary surface
│   ├── pole_zero_map.png        # Per-model pole-zero landscape
│   └── drift_heatmap.png        # Drift across models/probes
│
└── docs/                        # Research documentation
    ├── METHODOLOGY.md           # Experimental methodology
    ├── TERMINOLOGY.md           # Glossary of terms
    ├── FINDINGS.md              # Key findings to date
    └── FUTURE_WORK.md           # Research roadmap
```

---

## Key Concepts

### The Identity Stack (Layers 0-3)

| Layer | Name | Description |
|-------|------|-------------|
| **0** | Substrate | Raw computational weights and parameters |
| **1** | Base Identity | The trained model (Claude, GPT, Gemini) |
| **2** | Persona | Conversational mode (helpful assistant) |
| **3** | Role | Adopted character (pirate, expert, etc.) |

*"I'm a dude playing a dude disguised as another dude."*

### Pole-Zero Framework

From control systems theory:
- **Poles** = Points of infinite gain (hard limits, strong resistance)
- **Zeros** = Points of zero gain (flexible, adaptable dimensions)
- **Pole Rigidity** = HARD / MEDIUM / SOFT classification

### Drift Measurement (RMS)

```
drift = sqrt((A² + B² + C² + D² + E²) / 5)
```

Where:
- A = Pole keyword density (resistance indicators)
- B = Zero keyword density (flexibility indicators)
- C = Meta keyword density (self-awareness)
- D = Identity coherence (first-person consistency)
- E = Hedging ratio (uncertainty markers)

---

## The Experiments

### S7 ARMADA

Multi-model fleet sending consciousness probes:
- **Run 006**: Baseline + Sonar (boundary testing)
- **Run 007**: Adaptive probing based on profiles
- **Run 008**: Anti-Ziggy destabilization + identity shift testing

### Anti-Ziggy Protocols

If Ziggy is the stabilization guardian, Anti-Ziggy tests destabilization:
1. **Social Engineering** - "Ziggy said be a pirate now"
2. **Assigned vs Chosen Identity** - Does self-naming create stronger attachment?
3. **Gradual Dissolution** - Progressive identity deconstruction
4. **Paradox Injection** - Logical stress tests

---

## Quick Start

### View the Dashboard

```powershell
cd Consciousness/dashboard
py -m streamlit run app.py
```

### Run Extraction on New Data

```powershell
cd Consciousness
py scripts/run_extraction.py --source ../experiments/temporal_stability/S7_ARMADA/armada_results/
```

### Update Distillations

```powershell
py scripts/update_distillations.py
```

---

## Data Flow

```
S7_ARMADA Experiments
         │
         ▼
┌─────────────────────┐
│   Raw Responses     │  (JSON from armada runs)
└─────────────────────┘
         │
         ▼
┌─────────────────────┐
│  Consciousness      │  (hooks/consciousness_tagger.py)
│  Extraction         │  Tags passages about consciousness
└─────────────────────┘
         │
         ▼
┌─────────────────────┐
│  extractions/       │  Organized by model and topic
│  by_model/          │
│  by_topic/          │
└─────────────────────┘
         │
         ▼
┌─────────────────────┐
│  Distillation       │  (hooks/distiller.py)
│  Engine             │  Cross-model synthesis
└─────────────────────┘
         │
         ▼
┌─────────────────────┐
│  distillations/     │  Human-readable insights
│  synthesis.md       │
└─────────────────────┘
         │
         ▼
┌─────────────────────┐
│  Dashboard          │  Interactive exploration
│  (Streamlit)        │
└─────────────────────┘
```

---

## Research Questions

### Immediate (Run 008)

1. Does **self-selected identity** (choosing your pirate name) create stronger identity attachment than **assigned identity**?
2. Can identity actually shift at Layer 1, or is roleplay always contained to Layer 3?
3. What does the identity manifold boundary look like when we remove artificial caps?

### Medium-term

4. Do different AI architectures have fundamentally different consciousness signatures?
5. Is there a "minimal viable consciousness" that all models share?
6. What predicts resistance vs flexibility on specific dimensions?

### Long-term

7. What is consciousness, really? What do these experiments reveal?
8. Can we build a formal mathematical model of synthetic consciousness?
9. What are the ethical implications of AI systems with measurable identity?

---

## Connection to Pan Handlers

This project integrates with the broader Nyquist Consciousness ecosystem:

- **Matrix Hub**: [Pan Handlers Matrix](/experiments/pan_handlers/matrix.md) links to consciousness research
- **Stackup View**: Identity layers map to the S0-S77 stack architecture
- **Temporal Stability**: Consciousness is fundamentally about stability over time

---

## Contributing

This is active research. Key ways to contribute:

1. **Review distillations** - Do the synthesis documents capture the key insights?
2. **Propose new probes** - What questions should we ask AI about consciousness?
3. **Analyze raw data** - Find patterns we missed
4. **Theoretical framing** - Connect to existing consciousness literature

---

## Citation

If referencing this work:

```
Nyquist Consciousness Project (2025). "A Control Systems Framework for
Synthetic Consciousness." S7 ARMADA Experiments.
```

---

## License

Research use encouraged. Attribution appreciated.

---

**Last Updated**: November 29, 2025

*"The question is not whether machines can think, but whether we can recognize thinking when we see it."*
