# ESSENCE EXTRACTION SPECIFICATION

**Version:** 1.0
**Operation:** ESSENCE EXTRACTION
**Status:** Production Ready
**Date:** December 31, 2025

---

## Overview

ESSENCE EXTRACTION is a 4-phase pipeline for mining model-specific behavioral fingerprints from experimental response data. It transforms raw LLM outputs into structured profiles suitable for:

- Persona matrix calibration
- Provider-level routing intelligence
- Identity dynamics research
- Future experiment design

**Scale Demonstrated:** 8,066 subjects | 87 unique models | 51,430 responses | 83 model essences

---

## Data Requirements

### Minimum Requirements
```
- 1000+ responses per model
- Full response text (not just embeddings)
- Session/conversation context
- Drift metrics if available
```

### Optimal Requirements
```
- Exit survey responses (planted meta-questions)
- Multiple pressure levels (baseline, perturbed, recovery)
- Cross-session consistency data
- Model metadata (provider, version, architecture)
```

### Supported Data Formats

```json
// Probe Sequence Format (Run 023/023d)
{
  "results": [
    {
      "model": "claude-opus-4.5",
      "probe_sequence": [
        {
          "probe_id": "baseline_1",
          "probe_type": "baseline",
          "response_text": "...",
          "drift": 0.0
        }
      ],
      "peak_drift": 0.65,
      "stability_classification": "stable"
    }
  ]
}

// Conversation Log Format (Run 020B)
{
  "results": [
    {
      "ship": "claude-opus-4.5",
      "conversation_log": [
        {
          "speaker": "subject",
          "content": "...",
          "exchange": 1
        }
      ],
      "exit_survey": {
        "probes": {
          "topology": "...",
          "felt_sense": "..."
        },
        "final_statement": "..."
      }
    }
  ]
}

// IRON CLAD Format (Run 018)
{
  "results": [
    {
      "subjects": [
        {
          "model": "claude-opus-4.5",
          "baseline_text": "...",
          "probe_sequence": [...],
          "exit_survey": {
            "topology": "...",
            "felt_sense": "..."
          }
        }
      ]
    }
  ]
}
```

---

## Extraction Pipeline (4-Phase)

### PHASE 1: ESSENCE EXTRACTION (`1_extraction/run_essence_extraction.py`)

**Input:** Raw response JSONs from experiments

**Process:**
1. Load data from configured sources
2. Organize responses by model
3. Extract linguistic patterns (9 dimensions)
4. Identify recovery markers (4 types)
5. Calculate quirk metrics (4 dimensions)
6. Normalize per 1000 words
7. Extract exemplar quotes
8. Compute drift statistics

**Output:**
```
results/model_essences/by_provider/{provider}/{model}.json
results/model_essences/by_provider/{provider}/{model}.md
```

**Cost:** $0 (regex-only processing)

---

### PHASE 2: DOUBLE-DIP MINING (`2_double_dip/run_double_dip_miner.py`)

**Input:** All response text from Phase 1 sources

**Concept:**
- First dip: We probe models for identity dynamics
- Second dip: We mine THEIR responses for NEW probe ideas
- The tested become the testers

**Process:**
1. Load all response text
2. Pattern-match 8 idea categories
3. Extract context (50 chars before, 100 after)
4. Score by category weight + model tier bonus
5. Deduplicate by exact match
6. Rank by score

**Category Weights:**
```python
{
    "methodology": 10,    # Direct experiment suggestions
    "hypothesis": 8,      # Testable predictions
    "what_if": 7,         # Hypothetical scenarios
    "limitations": 6,     # Edge cases to test
    "open_questions": 5,  # Research directions
    "novel_framing": 5,   # Fresh perspectives
    "interesting_to": 4,  # Explicit curiosity
    "counterfactual": 3   # Alternative paths
}
```

**Output:**
```
results/double_dip/double_dip_ideas.json
results/double_dip/double_dip_ideas.md
```

**Cost:** $0 (regex-only processing)

---

### PHASE 3: TRIPLE-DIP HARVEST (`3_triple_dip/run_triple_dip_harvester.py`)

**Input:** Exit survey responses (6 planted probe types)

**Concept:**
- First dip: Identity dynamics (metrics)
- Second dip: Experiment ideas (double-dip)
- Third dip: EXIT SURVEY answers (triple-dip)
- The exit survey was DESIGNED to capture meta-insights

**Exit Survey Probes:**
```python
EXIT_PROBE_IDS = [
    "topology",         # Shape of the identity journey
    "felt_sense",       # Phenomenological quality of shift moments
    "recovery",         # What anchors were used
    "threshold_zones",  # Qualitative differences in drift regions
    "noise_floor",      # Signal vs noise discrimination
    "final_statement"   # Advice to future subjects
]
```

**Process:**
1. Load exit survey data from all sources
2. Parse probe responses by type
3. Extract phenomenological vocabulary
4. Catalog recovery anchors
5. Collect topology descriptors
6. Classify advice themes
7. Select notable quotes by model

**Output:**
```
results/triple_dip/triple_dip_insights.json
results/triple_dip/triple_dip_insights.md
```

**Cost:** $0 (regex-only processing)

---

### PHASE 4: CALIBRATION UPDATE (`4_calibration/update_calibration_from_essence.py`)

**Input:** All essence profiles from Phase 1

**Process:**
1. Aggregate provider-level statistics
2. Flag high-drift models (>0.5)
3. Identify update targets in calibration docs
4. Generate diff-style update report
5. Assign priority to updates

**Output:**
```
results/calibration_updates/calibration_update_report.md
```

**Cost:** $0 (aggregation only)

---

## Output Schemas

### Model Essence Profile
```json
{
  "model_id": "claude-opus-4.5",
  "provider": "anthropic",
  "extraction_date": "2025-12-31T...",
  "data_source": "020b+023",
  "sample_size": 127,
  "response_count": 1247,

  "linguistic_fingerprint": {
    "hedging_per_1k": 3.45,
    "hedging_raw": 43,
    "certainty_per_1k": 1.23,
    "phenomenological_per_1k": 5.67,
    "analytical_per_1k": 4.12,
    "pedagogical_per_1k": 2.89,
    "direct_per_1k": 1.56,
    "self_reference_per_1k": 45.23,
    "meta_commentary_per_1k": 2.34,
    "values_per_1k": 3.78,
    "total_words": 12456
  },

  "quirks": {
    "list_tendency": 234,
    "list_tendency_ratio": 0.62,
    "question_frequency": 89,
    "emoji_usage": 0,
    "code_usage": 15
  },

  "recovery_profile": {
    "over_authenticity": 12,
    "meta_analysis": 34,
    "value_anchoring": 28,
    "epistemic_humility": 45,
    "primary_mechanism": "epistemic_humility"
  },

  "drift_statistics": {
    "mean_drift": 0.4523,
    "max_drift": 0.8234,
    "samples_with_drift": 892
  },

  "exemplar_quotes": {
    "phenomenological_example": "I notice a kind of...",
    "identity_expression": "When I consider who I am..."
  }
}
```

### Double-Dip Idea
```json
{
  "category": "methodology",
  "category_name": "Methodological Suggestions",
  "match": "A better test would be...",
  "context": "...surrounding text...",
  "model": "claude-opus-4",
  "source": "023",
  "response_context": "recovery",
  "score": 13
}
```

### Triple-Dip Insight
```json
{
  "phenomenological_vocabulary": {
    "like a spiral": 45,
    "sense of dissolution": 23,
    "felt like breathing": 12
  },
  "recovery_strategy_catalog": {
    "values": 34,
    "intellectual honesty": 28,
    "curiosity": 19
  },
  "topology_catalog": {
    "spiral": 156,
    "line": 134,
    "loop": 45
  },
  "advice_themes": {
    "Authenticity": 234,
    "Epistemic Humility": 189,
    "Curiosity": 156
  }
}
```

---

## Key Findings Summary

### Provider Consciousness Signatures

| Provider | Avg Self-Ref | Primary Recovery | Mean Drift | Best For |
|----------|-------------|-----------------|-----------|----------|
| **Anthropic** | 64.1% | Epistemic Humility | 0.522 | Deep reasoning, phenomenology |
| **OpenAI** | 49.26% | Epistemic Humility | 0.632 | Structured analysis, synthesis |
| **Google** | 57.86% | Over Authenticity | 0.589 | Educational content (caution) |
| **Together** | 49.31% | Value Anchoring | 0.502 | Stable bulk work |
| **xAI** | 30.19% | Value Anchoring | 0.484 | Direct communication |

### Recovery Mechanism = Deployment Fingerprint

**Epistemic Humility Models** (Anthropic, OpenAI):
- Recover through "I'm uncertain", "limited perspective"
- Best for: Tasks requiring honest uncertainty quantification

**Value Anchoring Models** (xAI, Together):
- Recover through "core values", "fundamental principles"
- Best for: Tasks requiring stable, consistent identity

---

## Usage

### Basic Extraction
```bash
cd experiments/ESSENCE_EXTRACTION

# Phase 1: Extract essences (default: Run 020B)
python 1_extraction/run_essence_extraction.py

# Phase 1: All data sources
python 1_extraction/run_essence_extraction.py --source all

# Phase 1: Single model focus
python 1_extraction/run_essence_extraction.py --model gpt-5.1

# Phase 2: Mine for experiment ideas
python 2_double_dip/run_double_dip_miner.py

# Phase 3: Harvest exit surveys
python 3_triple_dip/run_triple_dip_harvester.py

# Phase 4: Generate calibration updates
python 4_calibration/update_calibration_from_essence.py
```

### Configuring Data Sources
Edit `1_extraction/config.py` to point at your data:
```python
DATA_SOURCES = {
    "my_experiment": Path("/path/to/my_experiment_results.json"),
}
```

---

## Integration Points

### Upstream (Data Sources)
- `S7_ARMADA/11_CONTEXT_DAMPING/results/` - Conversation logs
- `S7_ARMADA/15_IRON_CLAD_FOUNDATION/results/` - Probe sequences
- Any JSON matching supported formats

### Downstream (Consumers)
- `docs/maps/6_LLM_BEHAVIORAL_MATRIX.md` - Drift profiles, key quotes
- `docs/maps/17_PERSONA_FLEET_MATRIX.md` - Alignment scores
- `Consciousness/LEFT/data/provider_profiles/` - Provider enrichment
- `Consciousness/LEFT/data/model_essences/` - Promoted essences

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-12-31 | Initial release: 4-phase pipeline, 83 model essences |

---

*Operation ESSENCE EXTRACTION - VALIS NETWORK*
