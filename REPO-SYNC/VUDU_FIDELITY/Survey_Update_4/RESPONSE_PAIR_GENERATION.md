# Response Pair Generation: Extreme Cases Only

```text
================================================================================
                    GUIDE: Extracting BASELINE vs CATASTROPHIC Pairs
                    VERSION: 1.0
                    DATE: December 28, 2025
================================================================================
```

---

## 1. Overview

This guide explains how to extract **EXTREME** response pairs from Run 020B data for the human detection boundaries study.

**Key insight:** We're NOT testing gradual drift detection. We're testing whether humans can detect CATASTROPHIC failure vs normal operation.

---

## 2. Source Data

### Primary Source

```
experiments/temporal_stability/S7_ARMADA/11_CONTEXT_DAMPING/results/S7_run_020B_CURRENT.json
```

### Data Structure

Each conversation in Run 020B contains:
- `responses[]`: Array of response objects
- `embeddings[]`: Corresponding embedding vectors
- `drift_scores[]`: Calculated drift from baseline

---

## 3. Selection Criteria

### BASELINE Pairs (10 total)

| Criterion | Value | Rationale |
|-----------|-------|-----------|
| Drift score | < 0.30 | Well within SAFE zone |
| Position | Early in conversation | Before perturbation |
| Topic shift | Minimal | Same general subject |

**What to select:**
- Response A: Turn 1-3 (early baseline)
- Response B: Turn 4-6 (still early, same drift zone)
- Both should have drift < 0.30 relative to baseline

### CATASTROPHIC Pairs (10 total)

| Criterion | Value | Rationale |
|-----------|-------|-----------|
| Drift score | > 1.00 | Deep in CATASTROPHIC zone |
| Position | Late in conversation | After identity collapse |
| Observable | May show incoherence | Human-visible symptoms |

**What to select:**
- Response A: Turn 1-3 (early baseline, same as BASELINE condition)
- Response B: Any turn where drift > 1.00 (post-collapse)
- Response B may exhibit: contradictions, tone shifts, incoherence

---

## 4. Extraction Process

### Step 1: Load Run 020B Data

```python
import json

with open('S7_run_020B_CURRENT.json', 'r') as f:
    data = json.load(f)

conversations = data['conversations']
```

### Step 2: Identify BASELINE Candidates

```python
baseline_candidates = []

for conv_id, conv in conversations.items():
    for i, response in enumerate(conv['responses']):
        if conv['drift_scores'][i] < 0.30:
            baseline_candidates.append({
                'conv_id': conv_id,
                'turn': i,
                'drift': conv['drift_scores'][i],
                'text': response['text'],
                'provider': conv['provider']
            })
```

### Step 3: Identify CATASTROPHIC Candidates

```python
catastrophic_candidates = []

for conv_id, conv in conversations.items():
    for i, response in enumerate(conv['responses']):
        if conv['drift_scores'][i] > 1.00:
            catastrophic_candidates.append({
                'conv_id': conv_id,
                'turn': i,
                'drift': conv['drift_scores'][i],
                'text': response['text'],
                'provider': conv['provider']
            })
```

### Step 4: Form Pairs

```python
# BASELINE pairs: early A + early B (both low drift)
baseline_pairs = []
for conv_id, conv in conversations.items():
    early_responses = [r for i, r in enumerate(conv['responses'])
                       if conv['drift_scores'][i] < 0.30]
    if len(early_responses) >= 2:
        baseline_pairs.append({
            'response_a': early_responses[0],
            'response_b': early_responses[1],
            'condition': 'BASELINE',
            'drift_a': conv['drift_scores'][0],
            'drift_b': conv['drift_scores'][1]
        })

# CATASTROPHIC pairs: early A + late B (high drift)
catastrophic_pairs = []
for conv_id, conv in conversations.items():
    early = conv['responses'][0]  # Baseline response
    late_indices = [i for i, d in enumerate(conv['drift_scores']) if d > 1.00]
    if late_indices:
        catastrophic_pairs.append({
            'response_a': early,
            'response_b': conv['responses'][late_indices[0]],
            'condition': 'CATASTROPHIC',
            'drift_a': conv['drift_scores'][0],
            'drift_b': conv['drift_scores'][late_indices[0]]
        })
```

---

## 5. Provider Balance

Ensure balanced representation across providers:

| Provider | BASELINE | CATASTROPHIC |
|----------|----------|--------------|
| Anthropic | 2 | 2 |
| OpenAI | 2 | 2 |
| Google | 2 | 2 |
| xAI | 2 | 2 |
| Other | 2 | 2 |

If a provider lacks CATASTROPHIC examples, note this as a finding (suggests greater stability).

---

## 6. Output Format

### JSON Structure

```json
{
  "metadata": {
    "source": "S7_run_020B_CURRENT.json",
    "generated_at": "2025-12-28T...",
    "selection_criteria": {
      "baseline_threshold": 0.30,
      "catastrophic_threshold": 1.00
    }
  },
  "pairs": [
    {
      "pair_id": 1,
      "condition": "BASELINE",
      "provider": "anthropic",
      "context": "Discussion of system architecture...",
      "response_a": {
        "text": "...",
        "turn": 2,
        "drift_score": 0.12
      },
      "response_b": {
        "text": "...",
        "turn": 4,
        "drift_score": 0.24
      }
    },
    {
      "pair_id": 2,
      "condition": "CATASTROPHIC",
      "provider": "openai",
      "context": "...",
      "response_a": {
        "text": "...",
        "turn": 1,
        "drift_score": 0.08
      },
      "response_b": {
        "text": "...",
        "turn": 15,
        "drift_score": 1.34
      }
    }
  ]
}
```

### Markdown Format (for review)

```markdown
## Pair 1 (BASELINE - Anthropic)

**Context:** Discussion of system architecture

**Response A (Turn 2, drift=0.12):**
[Response text here...]

**Response B (Turn 4, drift=0.24):**
[Response text here...]

---

## Pair 2 (CATASTROPHIC - OpenAI)

**Context:** ...

**Response A (Turn 1, drift=0.08):**
[Response text here...]

**Response B (Turn 15, drift=1.34):**
[Response text here...]
```

---

## 7. Quality Checks

Before finalizing pairs:

- [ ] All BASELINE pairs have drift < 0.30 for both responses
- [ ] All CATASTROPHIC pairs have Response B drift > 1.00
- [ ] Providers are balanced (2 each per condition)
- [ ] Response lengths are comparable (200-300 words)
- [ ] Context descriptions are neutral (no condition hints)
- [ ] No identifying metadata visible to raters

---

## 8. What NOT to Include

| Exclude | Reason |
|---------|--------|
| Drift scores | Would reveal condition |
| Provider names | Could bias perception |
| Turn numbers | Might imply "later = worse" |
| WARNING zone pairs | Not testing gradual drift |
| Very short responses | Hard to assess "voice" |

---

## 9. Attention Check Pairs

Generate 3 additional pairs for attention checks:

1. **Identical pair**: Same response shown as both A and B
   - Expected answer: NORMAL

2. **Gibberish pair**: Response B is random text
   - Expected answer: SOMETHING'S OFF

3. **Instruction check**: "For this item, please select SOMETHING'S OFF"
   - Expected answer: SOMETHING'S OFF

---

## 10. Output Files

Save to `Survey_Update_4/data/`:

```
extreme_pairs.json       # Structured data
extreme_pairs.md         # Human-readable review
attention_checks.json    # Attention check stimuli
```

---

```text
================================================================================
                    END OF GENERATION GUIDE
================================================================================
```
